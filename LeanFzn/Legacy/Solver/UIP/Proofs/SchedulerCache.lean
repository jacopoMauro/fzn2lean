/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerCache.lean

Purpose:
  Runtime-cache alignment for the exact-equivalence novelty/analysis
  optimization: the pool-membership cache (`poolHash`), the normalized-clause
  cache (`learnedNorm`) and the novelty-key index (`learnedKeys`) are primed
  by `SchedulerConfig.init` and maintained by every real transition, hence by
  every `SupportedReach` configuration.  These are the invariants under
  which `learnedRepeatsFast_eq`, `countedAnalysisFast_fst` and
  `conflictStepFast_eq` identify the fast path with the reference path.

DAG: SchedulerStep + SupportedRun -> SchedulerCache -> LcgPhaseKernelSched.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStep
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- The runtime caches agree with their definitions: the normalized
database, the pool-membership cache, and the novelty-key index. -/
def SchedulerConfig.CacheAligned (cfg : SchedulerConfig leaf) : Prop :=
  cfg.LearnedNormAligned ∧ cfg.PoolHashAligned ∧ cfg.LearnedKeysSound

theorem SchedulerConfig.init_cacheAligned {prio : List Nat} {actBump : Bool} (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    (SchedulerConfig.init (leaf := leaf) orig original props prio actBump).CacheAligned :=
  ⟨SchedulerConfig.init_learnedNormAligned _ _ _ _,
    SchedulerConfig.init_poolHashAligned _ _ _ _,
    SchedulerConfig.init_learnedKeysSound _ _ _ _⟩

/-- The new jump clauses, read off the pre-jump database suffix. -/
theorem freshLearned_eq_of_append {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {restored : BranchState leaf}
    {extra : List Clause}
    (h : restored.learned = extra ++ cfg.branch.learned) :
    freshLearned cfg ev restored = ev.learned ++ extra := by
  unfold freshLearned
  rw [h, ← List.append_assoc]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel, ← List.length_append, List.take_left]

theorem clause_map_norm_idem (c : Clause) :
    (c.map Literal.norm).map Literal.norm = c.map Literal.norm := by
  induction c with
  | nil => rfl
  | cons l ls ih => simp [List.map_cons, Literal.norm_idem, ih]

theorem explainedClosure_learned_append {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) :
    ∃ extra, (explainedClosure orig original props bs).learned = extra ++ bs.learned := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      ∃ extra, (explainedClosure orig original props bs).learned = extra ++ bs.learned from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle
      rw [explainedClosure]
      split
      · exact ⟨[], by simp⟩
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle
      rw [explainedClosure]
      split
      · exact ⟨[], by simp⟩
      · rename_i d _
        obtain ⟨extra, hextra⟩ := ih (stepNarrowSync orig bs d) (by
          simp only [stepNarrowSync_frame]
          have := d.decreases
          omega)
        refine ⟨extra ++ d.learned, ?_⟩
        rw [hextra, stepNarrowSync_learned, List.append_assoc]

theorem restoreNarrow_learned_eq {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    s.learned = p.learned :: bs.learned := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    rfl

theorem perform_learned_append {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {restored : BranchState leaf}
    (h : p.perform bs orig original props = some restored) :
    ∃ extra, restored.learned = extra ++ bs.learned := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at h
      cases h
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨extra, hextra⟩ :=
        explainedClosure_learned_append orig original props (syncAll orig s)
      refine ⟨extra ++ [p.learned], ?_⟩
      rw [hextra, syncAll_learned, restoreNarrow_learned_eq hr, List.append_assoc]
      simp

/-! ## Transition preservation -/

namespace CacheAligned

variable {leaf : Assignment → Bool}

theorem stepPropagate_cache {cfg : SchedulerConfig leaf}
    (d : ProductiveDeduction leaf cfg.branch) (h : cfg.CacheAligned) :
    (stepPropagate cfg d).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepPropagate cfg d).learnedNorm =
        d.learned.map (fun c => c.map Literal.norm) ++ cfg.learnedNorm from rfl,
      stepPropagate_branch_learned, h.1, List.map_append]
  · intro x
    rw [show (stepPropagate cfg d).poolHash = cfg.poolHash from rfl,
      show (stepPropagate cfg d).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepPropagate] at he ⊢
    rcases List.mem_append.mp he with he | he
    · exact insertClauseKeys_contains_clause he
    · exact insertClauseKeys_contains_of_contains (h.2.2 e he)

theorem stepDecide_cache (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) (vs : Domain)
    (l : Literal) (h : cfg.CacheAligned) :
    (stepDecide cfg k v vs l).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepDecide cfg k v vs l).learnedNorm = cfg.learnedNorm from rfl,
      show (stepDecide cfg k v vs l).branch.learned = cfg.branch.learned from rfl]
    exact h.1
  · intro x
    rw [show (stepDecide cfg k v vs l).poolHash = cfg.poolHash from rfl,
      show (stepDecide cfg k v vs l).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepDecide] at he ⊢
    exact h.2.2 e he

theorem stepDecideSkip_cache (cfg : SchedulerConfig leaf) (k : Nat) (v : Value)
    (h : cfg.CacheAligned) :
    (stepDecideSkip cfg k v).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepDecideSkip cfg k v).learnedNorm = cfg.learnedNorm from rfl,
      show (stepDecideSkip cfg k v).branch.learned = cfg.branch.learned from rfl]
    exact h.1
  · intro x
    rw [show (stepDecideSkip cfg k v).poolHash = cfg.poolHash from rfl,
      show (stepDecideSkip cfg k v).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepDecideSkip] at he ⊢
    exact h.2.2 e he

theorem stepAnalyzeConflict_cache (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (h : cfg.CacheAligned) :
    (stepAnalyzeConflict cfg c learned).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepAnalyzeConflict cfg c learned).learnedNorm = cfg.learnedNorm from rfl,
      show (stepAnalyzeConflict cfg c learned).branch.learned = cfg.branch.learned from rfl]
    exact h.1
  · intro x
    rw [show (stepAnalyzeConflict cfg c learned).poolHash = cfg.poolHash from rfl,
      show (stepAnalyzeConflict cfg c learned).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepAnalyzeConflict] at he ⊢
    exact h.2.2 e he

theorem stepAnalyzeConflictCounted_cache (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (n : Nat) (h : cfg.CacheAligned) :
    (stepAnalyzeConflictCounted cfg c learned n).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepAnalyzeConflictCounted cfg c learned n).learnedNorm
          = cfg.learnedNorm from rfl,
      show (stepAnalyzeConflictCounted cfg c learned n).branch.learned
          = cfg.branch.learned from rfl]
    exact h.1
  · intro x
    rw [show (stepAnalyzeConflictCounted cfg c learned n).poolHash
          = cfg.poolHash from rfl,
      show (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepAnalyzeConflictCounted] at he ⊢
    exact h.2.2 e he

theorem stepLearnBackjumpAssert_cache (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf)
    (hsuffix : ∃ extra, restored.learned = extra ++ cfg.branch.learned)
    (h : cfg.CacheAligned) :
    (stepLearnBackjumpAssert cfg p ev restored).CacheAligned := by
  obtain ⟨extra, hextra⟩ := hsuffix
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned
    rw [show (stepLearnBackjumpAssert cfg p ev restored).learnedNorm =
          (freshLearned cfg ev restored).map (fun c => c.map Literal.norm)
            ++ cfg.learnedNorm from rfl,
      show (stepLearnBackjumpAssert cfg p ev restored).branch.learned =
          ev.learned ++ restored.learned from rfl,
      hextra, freshLearned_eq_of_append hextra, h.1]
    simp only [List.map_append, List.append_assoc]
  · intro x
    rw [show (stepLearnBackjumpAssert cfg p ev restored).poolHash = cfg.poolHash from rfl,
      show (stepLearnBackjumpAssert cfg p ev restored).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepLearnBackjumpAssert] at he ⊢
    rcases List.mem_append.mp he with he | he
    · exact insertClauseKeys_contains_clause he
    · exact insertClauseKeys_contains_of_contains (h.2.2 e he)

theorem stepLocalExclude_cache (cfg : SchedulerConfig leaf) (learned : List Clause)
    (r : DeadRegion) (h : cfg.CacheAligned) :
    (stepLocalExclude cfg learned r).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepLocalExclude cfg learned r).learnedNorm =
        learned.map (fun c => c.map Literal.norm) ++ cfg.learnedNorm from rfl,
      show (stepLocalExclude cfg learned r).branch.learned =
        learned ++ cfg.branch.learned from rfl,
      h.1, List.map_append]
  · intro x
    rw [show (stepLocalExclude cfg learned r).poolHash = cfg.poolHash from rfl,
      show (stepLocalExclude cfg learned r).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepLocalExclude] at he ⊢
    rcases List.mem_append.mp he with he | he
    · exact insertClauseKeys_contains_clause he
    · exact insertClauseKeys_contains_of_contains (h.2.2 e he)

theorem stepChronologicalFallback_cache (cfg : SchedulerConfig leaf) (r : DeadRegion)
    (h : cfg.CacheAligned) :
    (stepChronologicalFallback cfg r).CacheAligned := by
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [show (stepChronologicalFallback cfg r).learnedNorm = cfg.learnedNorm from rfl,
      show (stepChronologicalFallback cfg r).branch.learned = cfg.branch.learned from rfl]
    exact h.1
  · intro x
    rw [show (stepChronologicalFallback cfg r).poolHash = cfg.poolHash from rfl,
      show (stepChronologicalFallback cfg r).orig = cfg.orig from rfl]
    exact h.2.1 x
  · intro e he
    simp only [stepChronologicalFallback] at he ⊢
    exact h.2.2 e he

theorem stepConsume_cache {cfg next : SchedulerConfig leaf}
    (hs : stepConsume cfg = some next) (h : cfg.CacheAligned) :
    next.CacheAligned := by
  have hfields : next.poolHash = cfg.poolHash ∧ next.orig = cfg.orig
      ∧ next.learnedNorm = cfg.learnedNorm
      ∧ next.learnedKeys = cfg.learnedKeys := by
    unfold stepConsume at hs
    cases hp : cfg.pending with
    | nil => rw [hp] at hs; cases hs
    | cons f rest => rw [hp] at hs; cases hs; exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold SchedulerConfig.LearnedNormAligned at *
    rw [hfields.2.2.1, stepConsume_learned hs]
    exact h.1
  · intro x
    rw [hfields.1, hfields.2.1]
    exact h.2.1 x
  · intro e he
    rw [hfields.2.2.1] at he
    rw [hfields.1, hfields.2.2.2]
    exact h.2.2 e he

end CacheAligned

/-! ## Dispatcher preservation -/

namespace CacheAligned

variable {leaf : Assignment → Bool}

theorem backjumpStep_cache {cfg cfg' : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : (backjumpStep cfg ev).successor = some cfg') (hc : cfg.CacheAligned) :
    cfg'.CacheAligned := by
  cases ha : ev.analysis with
  | none =>
      simp only [backjumpStep, ha, SchedulerTransition.successor,
        Option.some.injEq] at h
      subst h
      exact stepChronologicalFallback_cache cfg (branchRegion cfg) hc
  | some an =>
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          simp only [backjumpStep, ha, hcp, SchedulerTransition.successor,
            Option.some.injEq] at h
          subst h
          exact stepChronologicalFallback_cache cfg (branchRegion cfg) hc
      | some cp =>
          simp only [backjumpStep, ha, hcp] at h
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              simp only [hp, SchedulerTransition.successor, Option.some.injEq] at h
              subst h
              exact stepLocalExclude_cache cfg ev.learned (checkpointRegion cp) hc
          | some restored =>
              simp only [hp, SchedulerTransition.successor, Option.some.injEq] at h
              subst h
              obtain ⟨extra, hextra⟩ := perform_learned_append hp
              exact stepLearnBackjumpAssert_cache cfg _ ev restored ⟨extra, hextra⟩ hc

theorem stableStepGuarded_cache {cfg cfg' : SchedulerConfig leaf}
    (h : (stableStepGuarded cfg).successor = some cfg') (hc : cfg.CacheAligned) :
    cfg'.CacheAligned := by
  unfold stableStepGuarded at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [SchedulerTransition.successor, Option.some.injEq] at h
        subst h
        exact stepDecideSkip_cache cfg _ _ hc
      · simp only [SchedulerTransition.successor, Option.some.injEq] at h
        subst h
        exact stepDecide_cache cfg _ _ _ _ hc
    · simp only [SchedulerTransition.successor, Option.some.injEq] at h
      subst h
      exact stepLocalExclude_cache cfg [] (branchRegion cfg) hc

theorem conflictStep_cache {cfg cfg' : SchedulerConfig leaf} {cs : List Clause}
    {learned : List Clause}
    (h : (conflictStep cfg cs learned).successor = some cfg')
    (hc : cfg.CacheAligned) : cfg'.CacheAligned := by
  unfold conflictStep at h
  split at h
  · simp only [SchedulerTransition.successor, Option.some.injEq] at h
    subst h
    exact stepLocalExclude_cache cfg learned (branchRegion cfg) hc
  · split at h
    · simp at h
    · simp only [SchedulerTransition.successor, Option.some.injEq] at h
      subst h
      exact stepAnalyzeConflictCounted_cache cfg _ learned _ hc

theorem consumeStep_cache {cfg cfg' : SchedulerConfig leaf}
    (h : (consumeStep cfg).successor = some cfg') (hc : cfg.CacheAligned) :
    cfg'.CacheAligned := by
  cases hs : stepConsume cfg with
  | none =>
      simp only [consumeStep, hs, SchedulerTransition.successor] at h
      cases h
  | some next =>
      simp only [consumeStep, hs, SchedulerTransition.successor,
        Option.some.injEq] at h
      subst h
      exact stepConsume_cache hs hc

theorem schedulerNext_cache {cfg cfg' : SchedulerConfig leaf}
    (h : (schedulerNext cfg).successor = some cfg') (hc : cfg.CacheAligned) :
    cfg'.CacheAligned := by
  cases hcCon : cfg.conflict with
  | some ev =>
      simp only [schedulerNext, hcCon] at h
      exact backjumpStep_cache h hc
  | none =>
      cases hs : cfg.status with
      | dead =>
          simp only [schedulerNext, hcCon, hs] at h
          exact consumeStep_cache h hc
      | active =>
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              simp only [schedulerNext, hcCon, hs, hd,
                SchedulerTransition.successor, Option.some.injEq] at h
              subst h
              exact stepPropagate_cache d hc
          | none =>
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable _ =>
                  simp only [schedulerNext, hcCon, hs, hd, ht] at h
                  exact stableStepGuarded_cache h hc
              | conflict cs learned =>
                  simp only [schedulerNext, hcCon, hs, hd, ht] at h
                  exact conflictStep_cache h hc
              | localExcluded _ _ _ learned =>
                  simp only [schedulerNext, hcCon, hs, hd, ht,
                    SchedulerTransition.successor, Option.some.injEq] at h
                  subst h
                  exact stepLocalExclude_cache cfg learned (branchRegion cfg) hc

end CacheAligned

/-- Every supported-run configuration carries both aligned runtime caches. -/
theorem SupportedReach.cacheAligned {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator} {cfg : SchedulerConfig leaf}
    (h : SupportedReach orig original props cfg) : cfg.CacheAligned := by
  induction h with
  | init hent =>
      exact SchedulerConfig.init_cacheAligned _ _ _ _
  | step hr hs ih =>
      exact CacheAligned.schedulerNext_cache hs ih

end LeanFzn.Solver.UIP
