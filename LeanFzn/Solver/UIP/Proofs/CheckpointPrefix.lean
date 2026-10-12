/-
File: LeanFzn/Solver/UIP/Proofs/CheckpointPrefix.lean

Purpose: the RUN-LEVEL checkpoint-prefix invariant that discharges the
`hsurv` family of `supportedHpre_of_snapshots` (HdeadCkpt §2) and the
`supportedHdeadCheckpointRegion_*` consumers, plus the derived producers
of the `hfresh` and `hrange` families.

  §1 `checkpointAt_filter_le` — the pure lookup algebra of the runtime's
     level filter (`cfg.checkpoints.filter fun cp => cp.level ≤ t`): the
     lookup at any `L ≤ t` is unchanged. This is the checkpoint-lookup
     half of the jump and consume arms.

  §2 `identifiesChain_of_reach` — the identifies+chain run induction at
     the `SupportedReach` index, WITHOUT the `hconsumeInv` premise the
     landed `supportedIdentifiesChain_of_premises` takes (the consume arm
     empties the checkpoint list, so both conjuncts are vacuous there).

  §3 `CheckpointStrictPrefix` + `checkpointsStrictPrefix_of_reach` — THE
     J1 SURVIVOR INVARIANT: the newest checkpoint at level `L` carries a
     trail whose remaining part sits STRICTLY above `L`. Proved by the
     real dispatcher induction; the jump arm consumes §1 (the filter),
     §2 (the chain gives the selected checkpoint's dominance over the
     found one, and the identifies conjunct gives the selected
     checkpoint's trail prefix), the predecessor's strict invariant at
     `L`, and `perform_trail_prefix_checkpoint` (the successor trail
     extends the selected checkpoint's trail by target-level entries).

     `hsurv` (the LOOSE bound) follows from §3 immediately: the entries
     at level `≤ L` of the branch trail are exactly the checkpoint's own
     (§4 `supportedHsurv_of_cert`), so no strict-bound restatement is
     needed anywhere.

  §5 `supportedHfresh_of_reach` — the asserting-enqueue absence check,
     DERIVED from the UIP witness (`analyzeStep_uip_on_trail`) plus the
     conflict semantics: an entry of the checkpoint trail carrying the
     asserting literal's normal form would evaluate `uip` both true and
     false at every assignment the branch frame covers. The single
     premise is the RECORDED-SITE INHABITEDNESS of the branch frame
     (`∃ a, FrameCovers cfg.branch.frame a`) — exactly C2's owed
     obligation (PLAN.md C2: "discharge recorded-site inhabitedness or
     prove an empty-frame route").

  §6 `supportedHrange_of_premises` — the asserting literal's slot range,
     from the C1 pool alignment (`recordedAnalysis_learned_poolAligned`)
     plus the NEW pool-slot lemma (`atomPool_slot_lt`: every atom of
     `atomPool orig` names a slot below `orig.length`). The single
     premise is C1's run-wide trail-vocabulary family
     (`BranchTrailVocabulary`).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.CheckpointPrefix` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedProviders
import LeanFzn.Solver.UIP.Proofs.SchedulerBackjump
import LeanFzn.Solver.UIP.Proofs.SupportedDatabaseFacts
import LeanFzn.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Solver.UIP.Proofs.SchedulerVocabulary
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Checkpoint-lookup algebra of the level filter -/

/-- Generic `find?` algebra: filtering by `q` does not change the `find?`
lookup by `p` when every `p`-match survives `q` (`l.filter q` keeps the
same first `p`-match). -/
theorem List.find?_filter_of_forall {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = true → q a = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq]
        by_cases hp : p a = true
        · rw [List.find?_cons_of_pos hp, List.find?_cons_of_pos hp]
        · rw [List.find?_cons_of_neg hp, List.find?_cons_of_neg hp]
          exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      · rw [List.filter_cons_of_neg hq]
        by_cases hp : p a = true
        · exact absurd (h a (List.mem_cons_self ..) hp) hq
        · rw [List.find?_cons_of_neg hp]
          exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- THE LOOKUP ALGEBRA OF THE RUNTIME LEVEL FILTER: the newest checkpoint
at a level `L ≤ t` is unchanged by the jump/consume filter
`fun cp => cp.level ≤ t`. -/
theorem checkpointAt_filter_le {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {t L : Nat} (hLt : L ≤ t) :
    checkpointAt (cps.filter fun cp => cp.level ≤ t) L = checkpointAt cps L := by
  unfold checkpointAt
  exact List.find?_filter_of_forall
    (fun cp _ hp => decide_eq_true (by
      rw [beq_iff_eq] at hp
      omega))

/-! ## §2 The identifies+chain run induction (no consume-invariant input) -/

/-- **THE IDENTIFIES+CHAIN INDUCTION (J1)**: one pass over the supported
run produces both the per-state checkpoint identity conjunct and the
newest-first `CpChain`. Unlike the landed
`supportedIdentifiesChain_of_premises`, NO `hconsumeInv` is consumed: the
consume arm EMPTIES the checkpoint list (`stepConsume`), so both
conjuncts are vacuous at its successor (the checkpoint-read
`checkpoints_identify` of the landed version was used only as a weakened
stand-in for that vacuity). -/
theorem identifiesChain_of_reach {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      (∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level) ∧
        CpChain cfg.checkpoints := by
  intro cfg hreach
  induction hreach with
  | init =>
      refine ⟨?_, ?_⟩
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst hcp
        simpa only [SchedulerConfig.init, rootCheckpoint] using
          rootCheckpoint_identifies_init leaf orig
      · exact ⟨fun cp' h => by simp at h, trivial⟩
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            refine ⟨?_, ?_⟩
            · intro cp hcp
              exact ih.1 cp (by simpa only [stepChronologicalFallback] using hcp)
            · simpa only [stepChronologicalFallback] using ih.2
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp'
                  exact ih.1 cp
                    (by simpa only [stepChronologicalFallback] using hcp')
                · simpa only [stepChronologicalFallback] using ih.2
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.original cfg.props with
                | none =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    refine ⟨?_, ?_⟩
                    · intro cp' hcp'
                      exact ih.1 cp'
                        (by simpa only [stepLocalExclude] using hcp')
                    · simpa only [stepLocalExclude] using ih.2
                | some restored =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    refine ⟨?_, ?_⟩
                    · intro cp' hmem
                      exact stepLearnBackjumpAssert_hident_of_chain ih.2 hcp hp
                        hmem
                    · rw [stepLearnBackjumpAssert_checkpoints]
                      exact CpChain.filter ih.2 _
      · -- ===== ROUTE 2: dead branch — the consume route EMPTIES the list
        rw [hnc] at hs
        unfold consumeStep at hs
        split at hs
        · rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest =>
              refine ⟨?_, ?_⟩
              · -- the consume successor's checkpoint list is EMPTY
                intro cp hmem
                unfold stepConsume at hcs
                rw [hpend] at hcs
                injection hcs with hnext
                subst hnext
                cases hmem
              · unfold stepConsume at hcs
                rw [hpend] at hcs
                injection hcs with hnext
                subst hnext
                trivial
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          refine ⟨?_, ?_⟩
          · intro cp hcp
            exact stepPropagate_checkpoints_identify_of_identifies ih.1
              (supportedHlevel_of_reach hrec) d cp hcp
          · simpa only [stepPropagate] using ih.2
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hs
              · -- SKIP arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact stepDecideSkip_checkpoints_identify_of_identifies ih.1
                    hsp cp hcp
                · simpa only [stepDecideSkip] using ih.2
              · -- FRESH arm: the push site
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact stepDecide_checkpoints_identify_of_identifies ih.1
                    (supportedHlevel_of_reach hrec) hsp cp hcp
                · exact CpChain.of_identifies ih.2 ih.1
                    (supportedHlevel_of_reach hrec)
            · -- no split data: localExclude
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro cp hcp
                exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
              · simpa only [stepLocalExclude] using ih.2
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro cp hcp
                exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
              · simpa only [stepLocalExclude] using ih.2
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site: branch and checkpoint list unchanged
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact ih.1 cp (by simpa only [stepAnalyzeConflictCounted,
                    stepAnalyzeConflict, SchedulerConfig.countResolutions]
                      using hcp)
                · simpa only [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                    SchedulerConfig.countResolutions] using ih.2
        · -- ARM 6: localExcluded → localExclude
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          refine ⟨?_, ?_⟩
          · intro cp hcp
            exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
          · simpa only [stepLocalExclude] using ih.2

/-! ## §3 The strict checkpoint-prefix invariant (the `hsurv` core) -/

/-- **THE J1 SURVIVOR INVARIANT** (strict-mid form): the newest checkpoint
at a level `L` below the current branch level is a PREFIX of the branch
trail whose remaining part sits STRICTLY above `L`.

This is the invariant the loose `hsurv` bound is an immediate corollary
of (§4): every branch-trail entry at level `≤ L` is a checkpoint entry.
The jump arm consumes the filter algebra (§1), the identifies+chain
induction (§2 — the chain's dominance gives the SELECTED checkpoint's
trail-extension of the found one, and the identifies conjunct gives the
selected checkpoint's trail prefix), the predecessor's own strict
invariant at `L` (whose remaining-part levels are strictly above `L`),
and `perform_trail_prefix_checkpoint` (the successor trail extends the
selected checkpoint's trail by target-level entries only).

The strictness is exactly what the chain's NON-strict mid bound
(`cp'.level ≤ e.level`) cannot supply by itself: the predecessor's
strict part rules out mid entries AT `L` (they would be entries of the
predecessor branch trail above the found checkpoint, i.e. of its
`mid_cp`, whose levels are strictly above `L`). -/
def CheckpointStrictPrefix {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop :=
  ∀ {L : Nat} {cp : DecisionCheckpoint leaf},
    checkpointAt cfg.checkpoints L = some cp → L < cfg.branch.level →
      ∃ mid : List TrailEntry, cfg.branch.trail = cp.trail ++ mid ∧
        ∀ e ∈ mid, L < e.level

/-- **THE STRICT-PREFIX RUN INDUCTION (J1)**: every supported
configuration satisfies the strict checkpoint-prefix invariant. -/
theorem checkpointsStrictPrefix_of_reach {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      CheckpointStrictPrefix cfg := by
  intro cfg hreach
  induction hreach with
  | init =>
      intro L cp hcp hlt
      exact absurd hlt (Nat.not_lt_zero L)
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            intro L cp hcp hlt
            exact ih (by simpa only [stepChronologicalFallback] using hcp)
              (by simpa only [stepChronologicalFallback] using hlt)
        | some an =>
            cases hcpsel : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcpsel] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                intro L cp hcp hlt
                exact ih (by simpa only [stepChronologicalFallback] using hcp)
                  (by simpa only [stepChronologicalFallback] using hlt)
            | some cpsel =>
                cases hp : (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.original cfg.props with
                | none =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcpsel] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    intro L cp hcp hlt
                    exact ih (by simpa only [stepLocalExclude] using hcp)
                      (by simpa only [stepLocalExclude] using hlt)
                | some restored =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcpsel] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    -- ===== THE JUMP ARM
                    intro L cp hcp hlt
                    -- the successor's level is the selected checkpoint's level
                    have hlevX : (stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                          an.learned) ev restored).branch.level = cpsel.level :=
                      (rfl : (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                            an.learned) ev restored).branch.level
                          = restored.level).trans
                        ((BackjumpPlan.perform_level hp).trans
                          (rfl : (BackjumpPlan.ofCheckpoint cpsel cfg.branch
                            an.asserting an.learned).target = cpsel.level))
                    have hLsel : L < cpsel.level := by
                      rw [← hlevX]
                      exact hlt
                    -- transport the lookup through the runtime level filter
                    have hcps_eq : (stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                          an.learned) ev restored).checkpoints
                        = cfg.checkpoints.filter
                          (fun c => c.level ≤ cpsel.level) := by
                      rw [stepLearnBackjumpAssert_checkpoints]
                      rfl
                    have hcp' : checkpointAt cfg.checkpoints L = some cp := by
                      have h2 : checkpointAt (cfg.checkpoints.filter
                          fun c => c.level ≤ cpsel.level) L = some cp := by
                        rw [← hcps_eq]
                        exact hcp
                      rwa [checkpointAt_filter_le (t := cpsel.level) (L := L)
                        (by omega)] at h2
                    -- the selected checkpoint sits at or above L
                    have hplev : L < cfg.branch.level := by
                      have hb := supportedHlevel_of_reach hrec cpsel
                        (checkpointAt_mem hcpsel)
                      omega
                    obtain ⟨mid_cp, hmid_cp, hmid_cp_lev⟩ := ih hcp' hplev
                    -- the identifies conjunct: the selected checkpoint's
                    -- trail is a prefix of the branch trail
                    obtain ⟨hident, hchain⟩ := identifiesChain_of_reach hrec
                    have hsel_ident : cpsel.Identifies cfg.branch cpsel.level :=
                      hident cpsel (checkpointAt_mem hcpsel)
                    obtain ⟨midT, hmidT, -⟩ := hsel_ident.2.1
                    -- the chain: the selected checkpoint dominates the found one
                    have hlev_chain : cp.level ≤ cpsel.level := by
                      rw [checkpointAt_level hcp']
                      omega
                    obtain ⟨-, ⟨mid_chain, hmid_chain, -⟩, -⟩ :=
                      CpChain.pair_of_checkpointAt hchain hcpsel
                        (checkpointAt_mem hcp') hlev_chain
                    -- the perform trail: the successor extends the selected trail
                    obtain ⟨extra, hextra, hextra_lev⟩ :=
                      perform_trail_prefix_checkpoint hp
                    have hpref : restored.trail = cpsel.trail ++ extra :=
                      hextra
                    refine ⟨mid_chain ++ extra, ?_, ?_⟩
                    · show (stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                          an.learned) ev restored).branch.trail
                          = cp.trail ++ (mid_chain ++ extra)
                      rw [show (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cpsel cfg.branch an.asserting
                            an.learned) ev restored).branch.trail
                            = restored.trail from rfl,
                        hpref, hmid_chain, List.append_assoc]
                    · intro e he
                      rcases List.mem_append.mp he with he | he
                      · -- mid_chain is a middle chunk of mid_cp
                        have hcancel : mid_cp = mid_chain ++ midT := by
                          have h1 : cp.trail ++ mid_cp
                              = cp.trail ++ (mid_chain ++ midT) := by
                            rw [← hmid_cp, hmidT, hmid_chain, List.append_assoc]
                          exact List.append_cancel_left h1
                        rw [hcancel] at hmid_cp_lev
                        exact hmid_cp_lev e (List.mem_append.mpr (Or.inl he))
                      · -- the extra part sits at the selected checkpoint's level
                        have h2 : cpsel.level ≤ e.level := hextra_lev e he
                        omega
      · -- ===== ROUTE 2: dead branch — the consume route EMPTIES the list
        rw [hnc] at hs
        unfold consumeStep at hs
        split at hs
        · rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest =>
              intro L cp hcp hlt
              unfold stepConsume at hcs
              rw [hpend] at hcs
              injection hcs with hnext
              subst hnext
              cases hcp
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate (one entry at the current level)
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          intro L cp hcp hlt
          have hlev : L < cfg.branch.level := by
            simpa only [stepPropagate, narrowState] using hlt
          obtain ⟨mid, hmid, hmidlev⟩ :=
            ih (by simpa only [stepPropagate] using hcp) hlev
          refine ⟨mid ++ [(⟨d.literal.norm, cfg.branch.level,
            some { clause := d.reason }⟩ : TrailEntry)], ?_, ?_⟩
          · simp only [stepPropagate, narrowState]
            rw [hmid, List.append_assoc]
          · intro e he
            rcases List.mem_append.mp he with he | he
            · exact hmidlev e he
            · rw [List.mem_singleton] at he
              subst he
              exact hlev
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hs
              · -- SKIP arm: trail/level/checkpoints unchanged
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                intro L cp hcp hlt
                exact ih (by simpa only [stepDecideSkip] using hcp)
                  (by simpa only [stepDecideSkip] using hlt)
              · -- FRESH arm: the push of the parent snapshot
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                intro L cp hcp hlt
                by_cases hL : L = cfg.branch.level
                · -- the found checkpoint is the pushed parent snapshot
                  subst hL
                  have h1 : checkpointAt (DecisionCheckpoint.ofBranch cfg.branch
                      :: cfg.checkpoints) (DecisionCheckpoint.ofBranch
                        cfg.branch).level
                      = some (DecisionCheckpoint.ofBranch cfg.branch) := by
                    simp [checkpointAt]
                  have hcpn : checkpointAt (DecisionCheckpoint.ofBranch cfg.branch
                      :: cfg.checkpoints) cfg.branch.level = some cp := by
                    simpa only [stepDecide] using hcp
                  have hlevel_eq : (DecisionCheckpoint.ofBranch cfg.branch).level
                      = cfg.branch.level := rfl
                  rw [← hlevel_eq] at hcpn
                  rw [h1] at hcpn
                  have hcpeq : cp = DecisionCheckpoint.ofBranch cfg.branch := by
                    simpa only [Option.some.injEq] using hcpn.symm
                  subst hcpeq
                  refine ⟨[(⟨l.norm, cfg.branch.level + 1, none⟩ :
                    TrailEntry)], rfl, ?_⟩
                  intro e he
                  rw [List.mem_singleton] at he
                  subst he
                  show cfg.branch.level < cfg.branch.level + 1
                  omega
                · -- an older checkpoint: recurse and append the decision entry
                  have hlt' : L < cfg.branch.level := by
                    have hlt'' : L < cfg.branch.level + 1 := by
                      simpa only [stepDecide_level] using hlt
                    omega
                  have hbeqL : ¬ (((DecisionCheckpoint.ofBranch cfg.branch).level
                      == L) = true) := by
                    intro hh
                    exact hL ((beq_iff_eq.mp (by simpa only
                      [DecisionCheckpoint.ofBranch] using hh)).symm)
                  have hcp' : checkpointAt cfg.checkpoints L = some cp := by
                    have h2 : checkpointAt (DecisionCheckpoint.ofBranch cfg.branch
                        :: cfg.checkpoints) L = some cp := by
                      simpa only [stepDecide] using hcp
                    have h2' : checkpointAt (DecisionCheckpoint.ofBranch cfg.branch
                        :: cfg.checkpoints) L = checkpointAt cfg.checkpoints L := by
                      simp [checkpointAt, hbeqL]
                    rw [h2'] at h2
                    exact h2
                  obtain ⟨mid, hmid, hmidlev⟩ := ih hcp' hlt'
                  refine ⟨mid ++ [(⟨l.norm, cfg.branch.level + 1, none⟩ :
                    TrailEntry)], ?_, ?_⟩
                  · rw [show (stepDecide cfg v vs doms l).branch.trail
                        = cfg.branch.trail ++ [(⟨l.norm, cfg.branch.level + 1,
                            none⟩ : TrailEntry)] from rfl, hmid, List.append_assoc]
                  · intro e he
                    rcases List.mem_append.mp he with he | he
                    · exact hmidlev e he
                    · rw [List.mem_singleton] at he
                      subst he
                      show L < cfg.branch.level + 1
                      omega
            · -- no split data: localExclude
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              intro L cp hcp hlt
              exact ih (by simpa only [stepLocalExclude] using hcp)
                (by simpa only [stepLocalExclude] using hlt)
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              intro L cp hcp hlt
              exact ih (by simpa only [stepLocalExclude] using hcp)
                (by simpa only [stepLocalExclude] using hlt)
          | cons c rest =>
              intro L cp hcp hlt
              by_cases hlv : cfg.branch.level = 0
              · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site: branch and checkpoint list unchanged
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                exact ih (by simpa only [stepAnalyzeConflictCounted,
                  stepAnalyzeConflict, SchedulerConfig.countResolutions]
                    using hcp)
                  (by simpa only [stepAnalyzeConflictCounted,
                    stepAnalyzeConflict, SchedulerConfig.countResolutions]
                      using hlt)
        · -- ARM 6: localExcluded → localExclude
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          intro L cp hcp hlt
          exact ih (by simpa only [stepLocalExclude] using hcp)
            (by simpa only [stepLocalExclude] using hlt)

/-! ## §4 The `hsurv` producer (loose bound, literal load) -/

/-- **THE `hsurv` FAMILY (LOOSE BOUND) FROM THE CERTIFICATE**: at every
supported recorded-evidence site whose selected checkpoint sits at the
recorded analysis's backjump level, EVERY branch-trail entry at level
`≤ an.backjumpLevel` is an entry of the checkpoint's trail — entries
exactly AT the target level included, which is the load-bearing boundary
the §7 finding of `HdeadCkpt.lean` pins down (`strict_hsurv_insufficient_
for_chronology`).

The proof is §3 plus the certificate's `targetDescends` (the target
strictly descends on the positive-level recorded sites,
`recorded_conflict_level_pos`): the strict-prefix invariant puts every
post-checkpoint entry strictly above the target level, so an entry at
level `≤ target` cannot be one of them. No statement is weakened: the
loose bound is proved as stated. -/
theorem supportedHsurv_of_cert {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail := by
  intro cfg ev an cp hreach hconf hana hcp e he hle
  have hlt : an.backjumpLevel < cfg.branch.level := by
    have hd := (hcert hreach hconf hana).targetDescends
    have hp := recorded_conflict_level_pos hreach.reachable ev hconf
    rcases hd with h0 | h
    · omega
    · exact h
  obtain ⟨mid, hmid, hmidlev⟩ := checkpointsStrictPrefix_of_reach hreach hcp hlt
  rw [hmid] at he
  rcases List.mem_append.mp he with h | h
  · exact h
  · exact absurd (hmidlev e h) (by omega)

/-! ## §5 The `hfresh` producer (the enqueue absence check) -/

/-- **THE `hfresh` FAMILY (THE ENQUEUE ABSENCE CHECK), DERIVED**: at every
supported recorded-evidence site with a selected checkpoint, no entry of
the checkpoint's trail carries the recorded asserting literal's normal
form.

DERIVATION (no certificate content assumed): the recorded analysis is the
canonical `(ofUIP below uip).normalized`, so its asserting literal is
`(uip.negate).norm`; the UIP witness `m` of the computed-allowance run
(`analyzeStep_uip_on_trail`) sits ON the conflict branch's trail with
literal `uip`. An entry `e` of the checkpoint's trail is a branch-trail
entry (the identifies prefix), so at every assignment the branch frame
covers, `e` makes `uip` FALSE (`(uip.negate).norm` holds) while `m` makes
`uip` TRUE — a contradiction as soon as the branch frame covers ANY
assignment.

THE SINGLE PREMISE `hinhab` is exactly the RECORDED-SITE INHABITEDNESS of
the branch frame — C2's owed obligation (PLAN.md C2: "discharge
recorded-site inhabitedness or prove an empty-frame route"). No pool or
database fact is consumed; the certificate's `assertingSurvives` is NOT
used (it speaks about the NEGATION, as documented). -/
theorem supportedHfresh_of_reach {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hinhab : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∃ a : Assignment, FrameCovers cfg.branch.frame a) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro cfg ev an cp hreach hconf hana hcp e he hcon
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  -- the recorded asserting literal is the normalized negated UIP
  have hass : an.asserting.norm = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting, norm_norm]
  have hel : e.literal = (uip.negate).norm := by rw [hcon, hass]
  -- e is a branch-trail entry (the identifies prefix of the checkpoint)
  obtain ⟨hident, -⟩ := identifiesChain_of_reach hreach
  obtain ⟨mid, hmid, -⟩ := (hident cp (checkpointAt_mem hcp)).2.1
  have he' : e ∈ cfg.branch.trail := by
    rw [hmid]
    exact List.mem_append.mpr (Or.inl he)
  -- the UIP witness sits on the trail at the conflict level
  have hrun' := hrun
  unfold analyzeAtAllowance at hrun'
  obtain ⟨m, hm, hmlit, -⟩ :=
    analyzeStep_uip_on_trail cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail ev.clause) [ev.clause] none [] []
      (analyzerInvariant_init cfg.branch.trail cfg.branch.level) below uip hrun'
  -- an inhabited branch frame: both literals hold at a covered assignment
  obtain ⟨a, hcov⟩ := hinhab hreach
  have hbs := hbr hreach
  have h1 : (uip.negate).eval a = some true := by
    have h := hbs.agrees e he' a hcov
    rw [hel, Literal.norm_eval] at h
    exact h
  have h2 : uip.eval a = some false :=
    (Literal.eval_negate_false_iff uip a).mp h1
  have h3 : uip.eval a = some true := by
    have h := hbs.agrees m hm a hcov
    rwa [hmlit] at h
  rw [h2] at h3
  cases h3

/-! ## §6 The `hrange` producer (the asserting literal's slot range) -/

/-- Every atom of the base atom pool names a slot below the box length: a
slot-`s` atom of `atomPoolBase s orig` sits at a position `s + j` with
`j < orig.length`. -/
theorem atomPoolBase_slot_lt (s : Nat) : ∀ (orig : List Domain) {a : Atom},
    a ∈ atomPoolBase s orig → a.slot < s + orig.length
  | [], a, h => by
      exact absurd h (by simp [atomPoolBase])
  | d :: ds, a, h => by
      have h' : a ∈ slotAtomPool s d ++ atomPoolBase (s + 1) ds := h
      rcases List.mem_append.mp h' with h1 | h2
      · have hslot : a.slot = s := by
          simp only [slotAtomPool] at h1
          rcases List.mem_append.mp h1 with h1 | h1
          · rcases List.mem_append.mp h1 with h1 | h1
            · rcases (by simpa using h1 : a = Atom.boolEq s true ∨
                a = Atom.boolEq s false) with rfl | rfl <;> rfl
            · rcases List.mem_map.mp h1 with ⟨k, -, rfl⟩
              rfl
          · rcases List.mem_map.mp h1 with ⟨k, -, rfl⟩
            rfl
        simp only [List.length_cons]
        omega
      · have ih := atomPoolBase_slot_lt (s + 1) ds h2
        simp only [List.length_cons]
        omega

/-- The Boolean flip preserves the atom's slot. -/
theorem _root_.LeanFzn.Solver.Propagation.Atom.boolFlip_slot (a : Atom) : a.boolFlip.slot = a.slot := by
  cases a <;> rfl

/-- **POOL SLOT RANGE**: every atom of the box's atom pool names a slot
below the box length (the pool is indexed by slot position; the
Boolean-flip image preserves the slot). -/
theorem atomPool_slot_lt {orig : List Domain} {a : Atom}
    (h : a ∈ atomPool orig) : a.slot < orig.length := by
  rw [atomPool] at h
  rcases List.mem_append.mp h with h | h
  · have := atomPoolBase_slot_lt 0 orig h
    simpa using this
  · rcases List.mem_map.mp h with ⟨a', ha', rfl⟩
    have := atomPoolBase_slot_lt 0 orig ha'
    simpa [Atom.boolFlip_slot] using this

/-- **LITERAL POOL SLOT RANGE**: every literal of the box's literal pool
names a slot below the box length. -/
theorem litPool_slot_lt {orig : List Domain} {l : Literal}
    (h : l ∈ litPool orig) : l.atom.slot < orig.length := by
  rw [litPool] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
        exact atomPool_slot_lt ha
      · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
        exact atomPool_slot_lt ha
    · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
      exact atomPool_slot_lt (atomPool_boolFlip_mem ha)
  · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
    exact atomPool_slot_lt (atomPool_boolFlip_mem ha)

/-- **THE `hrange` FAMILY FROM THE C1 TRAIL VOCABULARY**: at every
supported recorded-evidence site, the recorded asserting literal names a
slot below the box length.

The proof composes the canonical form of the recorded analysis
(`reachable_analysis_success`; the asserting literal's membership is the
mapped head of `ofUIP`), C1's pool alignment
(`recordedAnalysis_learned_poolAligned`) and the pool slot-range lemma
above. The single premise `hv` is C1's run-wide trail-vocabulary family
(`BranchTrailVocabulary`, `TrailVocabularyProducers`); `hbr` is the joint
induction's per-site branch-reachability component. -/
theorem supportedHrange_of_premises {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → an.asserting.atom.slot < orig.length := by
  intro cfg ev an hreach hconf hana
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  -- the asserting literal is (the normal form of) the learned clause's head
  have hmem : an.asserting ∈ an.learned := by
    rw [hcanon]
    simp only [ConflictAnalysis.normalized_learned,
      ConflictAnalysis.normalized_asserting, ConflictAnalysis.ofUIP_learned,
      ConflictAnalysis.ofUIP_asserting]
    exact List.mem_map_of_mem (f := Literal.norm) (List.mem_cons_self ..)
  -- C1's pool alignment at the recorded site
  have halign := recordedAnalysis_learned_poolAligned (leaf := leaf)
    (orig := orig) (cfg := cfg) (bs := cfg.branch) (ev := ev) (an := an)
    rfl (hbr hreach) hreach.reachable hconf hana (hv hreach)
  have hpool : an.asserting.norm ∈ litPool orig :=
    halign an.asserting hmem
  have hlt := litPool_slot_lt hpool
  rwa [norm_atom_slot] at hlt

end LeanFzn.Solver.UIP
