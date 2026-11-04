/-
File: LeanFzn/Solver/UIP/SchedulerStep.lean

Purpose:
  The executable scheduler transitions of the explained frontier: ONE
  function per transition of INTERFACES §2.5, the frozen
  `SchedulerTransition` result, the dispatcher `schedulerNext`, and the
  per-transition obligations exported for C2/C3.

  Functions (one per transition):
  1. `stepPropagate`            — propagate one productive explained
                                  deduction to the closure's fixpoint;
  2. `stepDecide`               — decision/split: pin the head remaining
                                  value at a fresh level, push both
                                  children, register the new level's
                                  checkpoint;
  3. `leafWitness`              — the leaf SAT check (total: `some` only
                                  for a complete frame passing `leaf`);
  4. `stepAnalyzeConflict`      — record the conflict evidence, leave
                                  branch/pending/DB unchanged;
  5. `stepLearnBackjumpAssert`  — insert the learned clauses globally,
                                  restore the target frame and trail,
                                  narrow by the assertion, record its
                                  reason, resume propagation (the branch
                                  value comes from `BackjumpPlan.perform`),
                                  and account the jump's counters;
  6. `stepLocalExclude`         — register a dead region and mark the
                                  branch dead;
  7. `stepChronologicalFallback`— the analysis produced no asserting
                                  result: register the branch's dead
                                  region and continue chronologically;
  8. `stepConsume`              — resume the next pending alternative
                                  (`none` = the frontier is exhausted, the
                                  `unsat` precondition).

  Exported obligations (C2's discharge targets, PLAN P1.3 items 4-5 and
  INTERFACES §2.6): `SplitCovers` (proved for the concrete split),
  `SolutionWitness`, `RootContradiction`, `UnsatEvidence`,
  `BackjumpCovers`, `ResumeCoherent`, `PlanMatchesAnalysis` (proved for
  the concrete plan construction), `ResolutionCountBound`, plus the
  `rfl`-level transition shape lemmas and the `unsat`-site
  characterizations.

  `analyzedSolve` in `AnalysisDriver.lean` stays the untouched reference.

Dependencies:
  - LeanFzn.Solver.UIP.SchedulerState (C1): the configuration, counters, coverage.

DAG:
  SchedulerState -> SchedulerStep -> Proofs.SchedulerStep (C2)
  -> Scheduler (C3) -> the public driver (D1).
-/

import LeanFzn.Legacy.Solver.UIP.SchedulerState
import LeanFzn.Legacy.Solver.Propagation.SparseRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Legacy.Solver.Propagation.FrameSync
import LeanFzn.Legacy.Solver.Propagation.ConflictResolution    -- analysisFuel
import LeanFzn.Legacy.Solver.Propagation.AnalysisProgress      -- initAnalysisState
import LeanFzn.Legacy.Solver.Propagation.AnalysisEventsCore    -- analyzeEvents, analyzeEventsExpansions
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Exported per-transition obligations (C2's discharge targets) -/

/-- The split's coverage obligation: the two children cover every
assignment the parent frame covered (`covers_split` is its proof,
instantiated below as `splitCovers_of_splitData`). -/
def SplitCovers (f child sibling : BranchFrame) : Prop :=
  ∀ a, FrameCovers f a → FrameCovers child a ∨ FrameCovers sibling a

/-- The SAT verdict's obligation (INTERFACES §2.6): the reported witness
is a genuine solution of the original box. -/
def SolutionWitness (leaf : Assignment → Bool) (orig : List Domain)
    (w : Assignment) : Prop :=
  OriginalLeaves leaf orig w

/-- A root contradiction (INTERFACES §2.3 and §2.8): no leaf solution
satisfies the root trail. This is the immediate, trail-conditional
statement; the a-priori `∀ a, leaf a = true → False` additionally needs
the root-facts/coverage bridge, which C2 (branch configuration) and D1
(the compiled public path) instantiate. A level-0 conflict must be
classified as UNSAT only together with this evidence — never as a local
exclusion. -/
def RootContradiction (leaf : Assignment → Bool) (bs : BranchState leaf) :
    Prop :=
  ∀ a, leaf a = true → (∀ e ∈ bs.trail, e.literal.eval a = some true) → False

/-- The two UNSAT justifications (INTERFACES §2.6 for the exhausted
frontier, §2.8 for the root conflict): every `unsat` emission must be
covered by one of them. -/
def UnsatEvidence (leaf : Assignment → Bool) (orig : List Domain)
    (pending : List BranchFrame) (db : List Clause) (bs : BranchState leaf) :
    Prop :=
  CoversRemainingLeaves leaf orig pending db ∨ RootContradiction leaf bs

/-- The learn/backjump/assert coverage obligation (INTERFACES §2.6, PLAN
P1.3 items 3-4): every original leaf solution the pre-configuration
covered is covered after the jump by the restored frame or by a retained
alternative, or excluded by the (monotone, now larger) global database. -/
def BackjumpCovers (leaf : Assignment → Bool) (orig : List Domain)
    (cfg next : SchedulerConfig leaf) : Prop :=
  ∀ a, OriginalLeaves leaf orig a →
    (∃ f ∈ cfg.frontier, FrameCovers f a) →
    (∃ f ∈ next.frontier, FrameCovers f a) ∨
      (∃ c ∈ next.branch.learned, ¬ c.SatisfiedBy a)

/-- The resume obligation (PLAN P1.3 item 5, RESTATED by C2b-int): restoring
a pending alternative as the current branch must be coherent at the
alternative's own level. Stated in this layer's vocabulary (A1's
`NarrowingComplete` lives in `Proofs.BranchState`, which runtime modules
must not import): the frame IS the alternative's frame; the level is the
alternative's own (`f.2.length`); the trail extends the checkpoint's trail
by later entries at or above that level — on the repaired route those
entries are the real history at or below the level plus the retirement
`resumeSibling` appends (the checkpoint's raw trail asserts the FAILED
child's pin, refuted by `stepConsume_resumes_without_retirement`); the
frame is a sub-box of the original box; and every original value the
frame drops at a remaining slot carries a falsifying trail literal for
that slot. Resuming by the assertion path (after a backjump, the
assertion's trail entry is exactly that falsifier) or by the retirement
route (`resumeSibling_retires`) is how C2 discharges it.

The trail conjunct is the `Identifies`-shaped extension (`cp.trail ++
extra` with every extra entry at level ≥ `f.2.length`), which is what the
repaired runtime actually establishes and what
`DecisionCheckpoint.Identifies.restore_extend` consumes. The old equality
`restored.trail = cp.trail` — refuted by the retirement repair — is
retained as `ResumeCoherent_old` for references written against the
frozen predicate. -/
def ResumeCoherent (orig : List Domain) (f : BranchFrame)
    (cp : DecisionCheckpoint leaf) (restored : BranchState leaf) : Prop :=
  restored.frame = f ∧
  (∃ extra : List TrailEntry,
    restored.trail = cp.trail ++ extra ∧ ∀ e ∈ extra, f.level ≤ e.level) ∧
  restored.level = f.level ∧
  (∀ i v, v ∈ (Frame.domains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty) ∧
  (∀ k ∉ f.order, ∀ w, w ∈ orig.getD k Dom.empty → w ∉ f.doms.getD k Dom.empty →
    ∃ e ∈ restored.trail, e.literal.atom.slot = k ∧
      e.literal.valueHolds w = false)

/-- The pre-repair (C2b-refuted) shape of `ResumeCoherent`: the trail
equality the prefix-length `stepConsume` established unconditionally and
the retirement repair replaces. Kept for compatibility with proofs (and
documentation) written against the frozen predicate. -/
def ResumeCoherent_old (orig : List Domain) (f : BranchFrame)
    (cp : DecisionCheckpoint leaf) (restored : BranchState leaf) : Prop :=
  restored.frame = f ∧ restored.trail = cp.trail ∧ restored.level = cp.level ∧
  (∀ i v, v ∈ (Frame.domains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty) ∧
  (∀ k ∉ f.order, ∀ w, w ∈ orig.getD k Dom.empty → w ∉ f.doms.getD k Dom.empty →
    ∃ e ∈ restored.trail, e.literal.atom.slot = k ∧
      e.literal.valueHolds w = false)

/-- The plan-evidence coherence the `learnBackjumpAssert` emission must
satisfy: the plan's reason clause is the recorded analysis's learned
clause and the plan's assertion is the analysis's asserting literal.
Holds by construction (`planMatchesAnalysis_ofCheckpoint`). -/
def PlanMatchesAnalysis (p : BackjumpPlan leaf) (an : ConflictAnalysis) : Prop :=
  p.learned = an.learned ∧ p.asserting = an.asserting

/-! ## Transition data helpers -/

/-- The split data of a frame (S0 §3.3, M2/M3): the policy-selected live
slot `k` (S1's `selectSlot`: minimum domain cardinality, ties by smallest
index), the pinned value `v`, the sibling domain `vs`, and the literal
asserting the pinned value (`valueLiteral`, the decision vocabulary of the
closure layer). `none` when no live slot exists or the value shape is
unsupported. Sparse: the children are `f.pin k v` / `f.retire k vs`. -/
def splitData (f : BranchFrame) (σ : List Nat := []) :
    Option (Literal × Nat × Value × Domain) :=
  SparseRun.Frame.splitData f σ

/-- The split data selects a live slot and decomposes its domain. -/
theorem splitData_spec {f : BranchFrame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} (h : splitData f σ = some (l, k, v, vs)) :
    f.doms[k]?.map Dom.enum = some (v :: vs.enum) ∧ valueLiteral k v = some l :=
  SparseRun.Frame.splitData_spec h

/-- The sibling produced by the policy split is canonical: its enumeration
round-trips through `Dom.ofList`. -/
theorem splitP_sibling_canonical {σ : List Nat} {f : BranchFrame} {k : Nat}
    {v : Value} {vs : Domain} (h : SparseRun.Frame.splitP σ f = some (k, v, vs)) :
    vs = Dom.ofList vs.enum := by
  unfold SparseRun.Frame.splitP at h
  cases hs : SelectPolicy.selectSlotP σ f.doms with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases he : Dom.enum d with
          | nil => simp [hd, he] at h
          | cons w ws =>
              simp only [hd, he, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              rw [Dom.enum_ofList]

/-- Exact characterization of the split data: the selected slot is exactly
the policy's choice (`selectSlotP σ`) and its domain head is the pinned value. -/
theorem splitData_eq_some_iff {f : BranchFrame} {σ : List Nat} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} :
    splitData f σ = some (l, k, v, vs) ↔
      SelectPolicy.selectSlotP σ f.doms = some k ∧
        f.doms[k]?.map Dom.enum = some (v :: vs.enum) ∧
        valueLiteral k v = some l ∧ vs = Dom.ofList vs.enum := by
  constructor
  · intro h
    obtain ⟨hspec, hlit⟩ := SparseRun.Frame.splitData_spec h
    exact ⟨SparseRun.Frame.splitData_slot h, hspec, hlit,
      splitP_sibling_canonical (SparseRun.Frame.splitData_split h)⟩
  · rintro ⟨hslot, hspec, hlit, hcanon⟩
    have hsplit : SparseRun.Frame.splitP σ f = some (k, v, vs) := by
      unfold SparseRun.Frame.splitP
      rw [hslot]
      dsimp only
      cases hk : f.doms[k]? with
      | none =>
          rw [hk] at hspec
          simp at hspec
      | some d =>
          rw [hk] at hspec
          simp only [Option.map_some, Option.some.injEq] at hspec
          dsimp only
          rw [hspec]
          dsimp only
          rw [← hcanon]
    show SparseRun.Frame.splitData f σ = some (l, k, v, vs)
    simp only [SparseRun.Frame.splitData, hsplit, hlit]
    rfl

/-- The leaf SAT check (S0 §3.6): the current frame reads back a complete
assignment (`BranchFrame.assignment?`: every domain a singleton) that
passes the leaf predicate. Total; `none` for an incomplete frame or a
failing assignment. -/
def leafWitness (leaf : Assignment → Bool) (cfg : SchedulerConfig leaf) :
    Option Assignment :=
  match cfg.branch.frame.assignment? with
  | some w => if leaf w then some w else none
  | none => none

/-- The dead region registered for the current branch: the COMPUTABLE
exact frame region `DeadRegion.byFrame` (C2b-int repair). Replaces the
former `DeadRegion.byPrefix` of the frame's chosen prefix, which was
UNSOUND for narrowed frames (`narrowed_prefix_region_not_sound` in
`Proofs/SchedulerResume.lean` exhibits a live sibling solution inside
`byPrefix []` of a narrowed frame): the registered region now claims
exactly assignments covered by the frame, and its soundness under the
site's deadness evidence `∀ a, leaf a = true → FrameCovers f a → False`
is `DeadRegion.byFrame_sound`. The region stays computable, so
`stableStep`/`conflictStep`/`backjumpStep`/`schedulerNext` remain
computable and `Tests.UIP.OracleFixtures` still compiles its `main`. -/
def branchRegion (cfg : SchedulerConfig leaf) : DeadRegion :=
  DeadRegion.byFrame cfg.branch.frame

/-- The dead region of a saved checkpoint's frame: the COMPUTABLE exact
frame region `DeadRegion.byFrame`, with the same `DeadRegion.byFrame_sound`
registration lemma as `branchRegion` (the ancestor frame can be narrowed
by propagation before the split; see `assertion_reject_routes_local`,
whose soundness statement is about the frame region). -/
def checkpointRegion (cp : DecisionCheckpoint leaf) : DeadRegion :=
  DeadRegion.byFrame cp.frame

/-- The split's coverage is the arbitrary-slot exhaustiveness law
(`covers_split_at`): pushing both children (`f.pin k v` / `f.retire k vs`)
never loses a covered assignment. -/
theorem splitCovers_of_splitData {f : BranchFrame} {σ : List Nat} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (h : splitData f σ = some (l, k, v, vs)) :
    SplitCovers f (f.pin k v) (f.retire k vs) := by
  obtain ⟨hspec, -⟩ := splitData_spec h
  intro a ha
  rcases (covers_split_at hspec a).mp ha with h' | h'
  · exact Or.inl h'
  · exact Or.inr h' 

/-- The concrete plan construction satisfies the plan-evidence
coherence: the plan's clause and assertion are the analysis's. -/
theorem planMatchesAnalysis_ofCheckpoint (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) :
    PlanMatchesAnalysis
      (BackjumpPlan.ofCheckpoint cp bs an.asserting an.learned) an :=
  ⟨rfl, rfl⟩

/-! ## One function per transition (PLAN P1.3 item 2) -/

/-- 1. PROPAGATE: one productive explained deduction at the current branch
(A2's `narrowState`, which appends the justified entry and prepends the
freshly learned clause). `steps` records the transition and `propagations`
the deduction; the remaining counters are unchanged (§2.7). -/
def stepPropagate (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) : SchedulerConfig leaf :=
  { cfg with
    branch := syncSlot cfg.orig
      (narrowState cfg.branch d.frame d.literal d.reason d.learned)
      d.literal.atom.slot
    status := .active
    stats := cfg.stats.add { steps := 1, propagations := 1 }
    learnedNorm := d.learned.map (fun c => c.map Literal.norm) ++ cfg.learnedNorm
    learnedKeys := insertClauseKeys cfg.poolHash cfg.learnedKeys
      (d.learned.map fun c => c.map Literal.norm) }

/-- 2. DECIDE/SPLIT: pin the head remaining value at a fresh decision
level, move the current frame to the pinned child, push the sibling
alternative (`covers_split`: parent ⇔ pinned child ∪ sibling, so the two
children replace the parent in the frontier), and register the checkpoint
at the parent level. The checkpoint is the PRE-PINNING PARENT snapshot
(`DecisionCheckpoint.ofBranch cfg.branch`: parent level, frame AND
trail — repaired by H4, `decide_push_not_snapshot`: the former
child-trail/parent-frame record admits no reachable snapshot). The parent
frame covers the pinned child and the child trail extends the parent
trail by the decision entry at the parent level, so
`DecisionCheckpoint.Identifies` still holds and restoring the record then
narrowing by the negated pin produces exactly the sibling — the mechanism
that lets a jump land on the alternative without re-deciding it. -/
def stepDecide (cfg : SchedulerConfig leaf) (k : Nat) (v : Value)
    (vs : Domain) (l : Literal) : SchedulerConfig leaf :=
  let child : BranchFrame := cfg.branch.frame.pin k v
  let decided : BranchState leaf := { (cfg.branch.decide l) with frame := child }
  { cfg with
    branch := decided
    checkpoints := DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints
    pending := cfg.branch.frame.retire k vs :: cfg.pending
    status := .active
    stats := cfg.stats.add { steps := 1, decisions := if vs.isEmpty then 0 else 1 } }

/-- 2-bis. REDUNDANT-PIN SKIP (the true branch of the `.decide` guard; V1
limitation 5). When the split's normalized pin literal is ALREADY recorded
at another level, the plain `stepDecide` would append a duplicate entry and
destroy `ReachableState.distinct` (`stepDecide_redundant_not_distinct`).
The skip instead advances the frame to the pinned child `(doms, pre ++ [v])`
with NO trail and NO level change — the recorded pin already justifies the
extended prefix — and does NOT push the sibling: S1's
`stepDecide_redundant_no_alternative` proves every parent-covered assignment
is already covered by the pinned child (and `stepDecide_redundant_forces_pin`
shows every parent-covered assignment carries the pin), so the dropped
sibling carries no represented leaf. No checkpoint is pushed (the site is
not a branch point) and no counter changes. This case is REACHABLE: a unit
clause whose literal IS the pin narrows the head to the pinned singleton
and the closure is then stable — the kernel-checked witness is
`Proofs/SchedulerDecideSkip.lean` §1. Residual for the INT shape only:
the skip's `PrefixForced` obligation is the named conditional
`DecideSkipPrefixTyped` (Bool: discharged globally). -/
def stepDecideSkip (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) : SchedulerConfig leaf :=
  { cfg with
    branch := { cfg.branch with frame := cfg.branch.frame.pin k v }
    status := .active
    stats := cfg.stats.add { steps := 1 } }

/-- The novelty test parameterized by a pool-membership predicate and a
database of ALREADY-NORMALIZED clauses: the two runtime representations
(`learnedRepeats` reads `litPool`/`branch.learned`; `learnedRepeatsFast`
reads the caches) are instances of this one function. -/
def learnedRepeatsWith (mem : Literal → Bool) (db : List Clause)
    (c : Clause) : Bool :=
  let csP := (c.map Literal.norm).filter mem
  db.any fun ds =>
    csP.all (fun x => decide (x ∈ ds)) &&
      ds.all (fun x => decide (x ∈ csP) || !mem x)

/-- Runtime novelty guard (cheap): true when the sorted canonical form
`canonicalSorted cfg.orig` of `c` may already occur among the sorted canonical
forms of the learned database (it is implied by equality of those forms). The
pool literals of `c` are compared; database clauses are first filtered by the
pool-free inclusion, so only near-duplicates pay for pool tests. -/
def learnedRepeats (cfg : SchedulerConfig leaf) (c : Clause) : Bool :=
  let P := litPool cfg.orig
  let mem : Literal → Bool := fun x => decide (x ∈ P)
  learnedRepeatsWith mem (cfg.branch.learned.map fun d => d.map Literal.norm) c

/-- The analysis the recording site stores: the normalised allowance analysis,
DROPPED (so the scheduler takes the chronological fallback) when its learned
clause repeats a database clause (novelty at every jump by construction). -/
def recordedAnalysis (cfg : SchedulerConfig leaf) (c : Clause) :
    Option ConflictAnalysis :=
  ((analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level c).map
    (fun p => (ConflictAnalysis.ofUIP p.1 p.2).normalized)).filter
    (fun an => !learnedRepeats cfg an.learned)

/-- THE FAST NOVELTY GUARD: a hash-bucket-mask lookup in the learned-key
index (`learnedKeys`, a necessary condition of a repeat) short-circuits the
common non-repeat; on a hit it verifies with the exact list test over the
runtime normalized-clause cache (`learnedNorm`) and the pool membership
cache (`poolHash`). It is EQUAL to `learnedRepeats` on every configuration
whose caches are aligned (`learnedRepeatsFast_eq`), and it gates exactly the
same recorded-analysis filter. -/
def learnedRepeatsFast (cfg : SchedulerConfig leaf) (c : Clause) : Bool :=
  if cfg.learnedKeys.contains (cfg.clauseKey c) then
    learnedRepeatsWith (fun x => cfg.poolHash.contains x) cfg.learnedNorm c
  else false

/-- A true reference test exhibits a database clause with the same
pool-restricted literal set. -/
theorem learnedRepeatsWith_true_exists {mem : Literal → Bool} {db : List Clause}
    {c : Clause} (h : learnedRepeatsWith mem db c = true) :
    ∃ d ∈ db, ∀ x, x ∈ (c.map Literal.norm).filter mem ↔ x ∈ d.filter mem := by
  unfold learnedRepeatsWith at h
  rw [List.any_eq_true] at h
  obtain ⟨d, hd, hall⟩ := h
  rw [Bool.and_eq_true] at hall
  obtain ⟨h1, h2⟩ := hall
  refine ⟨d, hd, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨hxc, hmem⟩ := List.mem_filter.mp hx
    have hxd : x ∈ d := by
      have := (List.all_eq_true.mp h1) x (List.mem_filter.mpr ⟨hxc, hmem⟩)
      simpa using this
    exact List.mem_filter.mpr ⟨hxd, hmem⟩
  · intro hx
    obtain ⟨hxd, hmem⟩ := List.mem_filter.mp hx
    have h := (List.all_eq_true.mp h2) x hxd
    rw [Bool.or_eq_true] at h
    rcases h with hcs | hnot
    · exact decide_eq_true_eq.mp hcs
    · rw [Bool.not_eq_true'] at hnot
      rw [hnot] at hmem
      cases hmem

/-- EXACTNESS of the fast novelty guard: under the cache-alignment
invariants it is the reference `learnedRepeats` (a key miss is a proof of
non-repeat; a key hit is verified by the exact list test). -/
theorem learnedRepeatsFast_eq {cfg : SchedulerConfig leaf} {c : Clause}
    (hdb : cfg.LearnedNormAligned) (hpool : cfg.PoolHashAligned)
    (hkeys : cfg.LearnedKeysSound) :
    learnedRepeatsFast cfg c = learnedRepeats cfg c := by
  unfold learnedRepeatsFast learnedRepeats
  by_cases hk : cfg.learnedKeys.contains (cfg.clauseKey c) = true
  · simp only [hk, if_true]
    rw [hdb]
    congr 1
    funext x
    exact hpool x
  · simp only [hk, if_false]
    cases hrep : learnedRepeatsWith (fun x => decide (x ∈ litPool cfg.orig))
        (cfg.branch.learned.map fun d => d.map Literal.norm) c with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨d, hd, hiff⟩ := learnedRepeatsWith_true_exists hrep
        have hiff' : ∀ x, x ∈ (c.map Literal.norm).filter
              (fun x => cfg.poolHash.contains x) ↔
            x ∈ d.filter (fun x => cfg.poolHash.contains x) := by
          intro x
          simpa only [List.mem_filter, hpool x] using hiff x
        have hkey := clauseKeyWith_eq_of_mem_iff (pool := cfg.poolHash) hiff'
        have hkd : cfg.learnedKeys.contains (clauseKeyWith cfg.poolHash d) = true :=
          hkeys d (by rw [hdb]; exact hd)
        apply hk
        rw [SchedulerConfig.clauseKey, hkey]
        exact hkd

/-- THE SINGLE-ANALYSIS BUNDLE: one executed counted run (`analyzeEvents`)
produces BOTH the recorded analysis (via the allowance-result correspondence)
and the `reasonResolutions` increment (`cs.expansions`), so the analyze site
never runs the analyzer twice. -/
def countedAnalysisFast (cfg : SchedulerConfig leaf) (c : Clause) :
    Option ConflictAnalysis × Nat :=
  match analyzeEvents cfg.orig cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail c) (initAnalysisState c) with
  | none => (none, 0)
  | some (cs, r) =>
      ((r.map (fun p => (ConflictAnalysis.ofUIP p.1 p.2).normalized)).filter
        (fun an => !learnedRepeatsFast cfg an.learned), cs.expansions)

theorem analyzeEvents_isSome (cfg : SchedulerConfig leaf) (c : Clause) :
    (analyzeEvents cfg.orig cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail c) (initAnalysisState c)).isSome := by
  obtain ⟨cs, k, r, h, -, -⟩ :=
    analyzeEvents_complete cfg.orig cfg.branch.trail cfg.branch.level c
  rw [h]
  rfl

/-- The bundle's analysis projection is exactly the recording site's
`recordedAnalysis` (same allowance result, same fast novelty filter). -/
theorem countedAnalysisFast_fst {cfg : SchedulerConfig leaf} {c : Clause}
    (hdb : cfg.LearnedNormAligned) (hpool : cfg.PoolHashAligned)
    (hkeys : cfg.LearnedKeysSound) :
    (countedAnalysisFast cfg c).1 = recordedAnalysis cfg c := by
  unfold countedAnalysisFast recordedAnalysis
  cases h : analyzeEvents cfg.orig cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail c) (initAnalysisState c) with
  | none =>
      exfalso
      have hs := analyzeEvents_isSome cfg c
      rw [h] at hs
      cases hs
  | some p =>
      obtain ⟨cs, r⟩ := p
      rw [analyzeEvents_result_eq_analyzeAtAllowance cfg.orig cfg.branch.trail
        cfg.branch.level c h]
      simp only [learnedRepeatsFast_eq hdb hpool hkeys]

/-- The bundle's count projection is exactly the wired
`analyzeEventsExpansions`. -/
theorem countedAnalysisFast_snd (cfg : SchedulerConfig leaf) (c : Clause) :
    (countedAnalysisFast cfg c).2 =
      analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c := by
  unfold countedAnalysisFast analyzeEventsExpansions
  cases h : analyzeEvents cfg.orig cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail c) (initAnalysisState c) with
  | none => rfl
  | some p => obtain ⟨cs, r⟩ := p; rfl

/-- 4. CONFLICT ANALYSIS: record the conflict evidence — the reported
clause, the closure's entailed new clauses, and the allowance run
(`analyzeAtAllowance`, producing `none` when there is no asserting
result and the fallback must take over). Branch, pending, database, the
checkpoint list and the counters are UNCHANGED; only the evidence and the
conflict statistic change (INTERFACES §2.6). The `reasonResolutions`
increment is applied at this same site by
`SchedulerConfig.countResolutions` with B1's counted trace (§2.7).

N1 NORMALIZATION (the RECORDED decision, coordination.md Session 9 round
17): the analysis record is stored in `ConflictAnalysis.normalized` form —
the learned clause's literals and the asserting literal are normalized.
Normalization is SEMANTICALLY neutral (`Literal.norm_eval`;
`RestorationCertificate.normalized` transfers every certificate), and it
is what makes the enqueue/database obligations structural: the asserting
literal becomes its own normal form
(`ConflictAnalysis.normalized_asserting_norm`), and the learned clause is
a normalized unit on the singleton conflicts the supported kit emits.
`ConflictAnalysis.ofUIP`, `ofRun`, `analyzeWithAllowance` and the
certificate machinery stay byte-identical; ONLY this recording site
normalizes. -/
def stepAnalyzeConflict (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) : SchedulerConfig leaf :=
  { cfg with
    conflict := some
      { clause := c
        learned := learned
        analysis := recordedAnalysis cfg c }
    stats := cfg.stats.add { steps := 1, conflicts := 1 } }

/-- The `analyzeConflict` transition with C3's counted resolution number:
records the evidence and increments `events.reasonResolutions` at the
site, in one call. -/
def stepAnalyzeConflictCounted (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (n : Nat) : SchedulerConfig leaf :=
  (stepAnalyzeConflict cfg c learned).countResolutions n

/-- Record with an ALREADY-COMPUTED analysis record: the body of
`stepAnalyzeConflict` with its `recordedAnalysis` call projected out. -/
def stepAnalyzeConflictOf (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (an : Option ConflictAnalysis) :
    SchedulerConfig leaf :=
  { cfg with
    conflict := some
      { clause := c
        learned := learned
        analysis := an }
    stats := cfg.stats.add { steps := 1, conflicts := 1 } }

/-- The computed-record form is the recording site when the record is the
site's own `recordedAnalysis`. -/
theorem stepAnalyzeConflictOf_eq (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) :
    stepAnalyzeConflictOf cfg c learned (recordedAnalysis cfg c)
      = stepAnalyzeConflict cfg c learned := rfl

/-- The counted recording site with an already-computed analysis record. -/
def stepAnalyzeConflictCountedOf (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (an : Option ConflictAnalysis) (n : Nat) :
    SchedulerConfig leaf :=
  (stepAnalyzeConflictOf cfg c learned an).countResolutions n

/-- EXACTNESS (`reasonResolutions` preserved): the computed-record counted
site is the reference counted site whenever its analysis record is the
reference `recordedAnalysis`. -/
theorem stepAnalyzeConflictCountedOf_eq (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) (n : Nat) :
    stepAnalyzeConflictCountedOf cfg c learned (recordedAnalysis cfg c) n
      = stepAnalyzeConflictCounted cfg c learned n := rfl

/-- The clauses the jump ADDS to the learned database, as a prefix: the
pre-jump database is preserved as a suffix by `perform`.  The prefix is
read off the new database by length, so the runtime cache update touches
only the new clauses. -/
def freshLearned (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) : List Clause :=
  (ev.learned ++ restored.learned).take
    ((ev.learned ++ restored.learned).length - cfg.branch.learned.length)


/-- 5. LEARN/BACKJUMP/ASSERT: the successor configuration of the complete
transition. `restored` is `BackjumpPlan.perform`'s result — the learned
clause is already in the global database, the target frame and trail are
restored, the assertion has narrowed the frame, its reason is recorded,
and propagation has been resumed. This function adds the closure's
conflict payload clauses, keeps only checkpoints at or below the target
(higher checkpoints no longer identify the branch), clears the recorded
conflict, and accounts the jump: `backjumps += 1`,
`sourceLevel :=` the pre-jump level, `targetLevel := plan.target`,
`assertingEnqueues += 1` (§2.7). -/
def stepLearnBackjumpAssert (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) : SchedulerConfig leaf :=
  { cfg with
    branch := { restored with learned := ev.learned ++ restored.learned }
    checkpoints := cfg.checkpoints.filter fun cp => cp.level ≤ p.target
    conflict := none
    status := .active
    events := cfg.events.recordBackjump cfg.branch.level p.target
    stats := cfg.stats.add { steps := 1, learnedClauses := ev.learned.length + 1 }
    learnedNorm := (freshLearned cfg ev restored).map
      (fun c => c.map Literal.norm) ++ cfg.learnedNorm
    learnedKeys := insertClauseKeys cfg.poolHash cfg.learnedKeys
      ((freshLearned cfg ev restored).map fun c => c.map Literal.norm)
    prio := if cfg.actBump then
        SelectPolicy.bumpPrio cfg.prio (p.learned.map fun l => l.atom.slot)
      else cfg.prio }

/-- 6. LOCAL EXCLUSION: the branch is dead by local evidence (a refuted
frame, an exhausted slot, a database refutation, or a rejected
assertion). Register the region, keep the entailed new clauses in the
global database, and mark the branch dead — the next transition consumes
the next pending alternative or reports UNSAT. `steps` records the
transition; the remaining counters are unchanged (§2.7). -/
def stepLocalExclude (cfg : SchedulerConfig leaf) (learned : List Clause)
    (r : DeadRegion) : SchedulerConfig leaf :=
  { cfg with
    branch := { cfg.branch with learned := learned ++ cfg.branch.learned }
    log := cfg.log.register r
    status := .dead
    conflict := none
    stats := cfg.stats.add { steps := 1 }
    learnedNorm := learned.map (fun c => c.map Literal.norm) ++ cfg.learnedNorm
    learnedKeys := insertClauseKeys cfg.poolHash cfg.learnedKeys
      (learned.map fun c => c.map Literal.norm) }

/-- 7. CHRONOLOGICAL FALLBACK: the analysis produced no asserting result
(allowance `none`, or no checkpoint at the proved target). Register the
branch's dead region and mark the branch dead: the chronological
continuation resumes the next pending alternative. `steps` records the
transition; the remaining counters are unchanged (§2.7). -/
def stepChronologicalFallback (cfg : SchedulerConfig leaf) (r : DeadRegion) :
    SchedulerConfig leaf :=
  { cfg with
    log := cfg.log.register r
    status := .dead
    conflict := none
    stats := cfg.stats.add { steps := 1 } }

/-- 8a. CONSUME: resume the next pending alternative as the current
branch. The trail is rebuilt by the REPAIRED sibling resume
`resumeSibling`: the real history at or below the alternative's own level
(`restoreLevel`) plus the retirement of the head value the alternative
dropped, recovered from the ancestor checkpoint's frame — the
prefix-length route (`restored.trail = cp.trail`) asserts the failed
child's pin and is refuted by `stepConsume_resumes_without_retirement`.
When no checkpoint survives (an alternative above a backjump target), the
pending frame is its own retained snapshot (R1 repair): the trail is
reconstructed canonically by `resumePending`/`canonicalTrail` from the
frame and the original box — prefix pins plus remaining-slot falsifiers,
so the resumed branch's region is exactly the frame's own. The global
learned database is carried over in both cases. `none` means the pending
frontier is empty: the `unsat` precondition.

CHECKPOINT RETIREMENT (R2 repair): the consume drops the ENTIRE checkpoint
list. The canonical resume's trail is FRAME-DERIVED (`canonicalPins f.2 ++
canonicalFalsifiers`), while every saved checkpoint's trail is the runtime
trail of some EARLIER branch state (pins and falsifiers interleaved, plus
narrowing entries) — a stale snapshot's trail is therefore not a prefix
of the resumed trail, and retaining it would falsify the chain's soundness
condition (`Identifies`: the jump restores `cp.frame`/`cp.trail`, so a
non-identifying checkpoint would restore a foreign branch). The retired
route's survivor argument (`resumeSibling_trail_coherent`, which related
the retired checkpoint to the level-filtered trail) died with the route.
Checkpoints are re-pushed by the next fresh decision; a jump before one
takes the certified chronological fallback (a sound stutter, never a
verdict). -/
def stepConsume (cfg : SchedulerConfig leaf) : Option (SchedulerConfig leaf) :=
  match cfg.pending with
  | [] => none
  | f :: rest =>
      some { cfg with
             branch := resumePending cfg.orig cfg.branch f
             checkpoints := []
             pending := rest
             status := .active
             conflict := none }

/-! ## Transition shape lemmas (the frozen §2.6 obligations, proved) -/

@[simp] theorem stepPropagate_branch (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).branch
      = syncSlot cfg.orig
          (narrowState cfg.branch d.frame d.literal d.reason d.learned)
          d.literal.atom.slot := rfl

@[simp] theorem stepPropagate_branch_frame (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).branch.frame = d.frame := by
  simp [stepPropagate, narrowState]

@[simp] theorem stepPropagate_branch_level (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).branch.level = cfg.branch.level := by
  simp [stepPropagate, narrowState]

@[simp] theorem stepPropagate_branch_learned (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).branch.learned = d.learned ++ cfg.branch.learned := by
  simp [stepPropagate, narrowState]

/-- The synchronised propagation successor is reachable as soon as the
narrowed state is (the sync pushes valid, explained literals). -/
theorem stepPropagate_branch_reachable {orig : List Domain}
    {cfg : SchedulerConfig leaf} (d : ProductiveDeduction leaf cfg.branch)
    (horig : cfg.orig = orig) (hfits : ∀ a, leaf a = true → a.Fits orig)
    (h : ReachableState leaf orig
      (narrowState cfg.branch d.frame d.literal d.reason d.learned)) :
    ReachableState leaf orig (stepPropagate cfg d).branch := by
  subst horig
  exact syncSlot_reachable _ h hfits

@[simp] theorem stepPropagate_pending (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).pending = cfg.pending := rfl

@[simp] theorem stepPropagate_events (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).events = cfg.events := rfl

@[simp] theorem stepPropagate_orig (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).orig = cfg.orig := rfl

@[simp] theorem stepDecide_branch (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).branch
      = { (cfg.branch.decide l) with frame := cfg.branch.frame.pin k v } := rfl

@[simp] theorem stepDecide_frame (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).branch.frame
      = cfg.branch.frame.pin k v := rfl

@[simp] theorem stepDecide_level (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).branch.level = cfg.branch.level + 1 := rfl

/-- The split pushes exactly the sibling: the pinned child is the current
frame, so the successor's frontier is the two children followed by the old
pending stack — the parent frame is replaced, not retained. -/
@[simp] theorem stepDecide_pending (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).pending
      = cfg.branch.frame.retire k vs :: cfg.pending := rfl

@[simp] theorem stepDecide_frontier (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).frontier
      = cfg.branch.frame.pin k v ::
        cfg.branch.frame.retire k vs :: cfg.pending := rfl

/-- The newest checkpoint of the split is the PARENT snapshot: it sits at
RESTATED (integration fix, H4): the push records `DecisionCheckpoint.ofBranch
cfg.branch` — the PARENT level, frame and trail — not the mixed
child-trail/parent-frame record the former statement pinned. The child is
still identified at the parent level (`stepDecide_checkpoints_identify`). -/
@[simp] theorem stepDecide_checkpoint_level (cfg : SchedulerConfig leaf)
    (k : Nat) (v : Value) (vs : Domain) (l : Literal) :
    ((stepDecide cfg k v vs l).checkpoints.head?.map
      DecisionCheckpoint.level) = some cfg.branch.level := rfl

@[simp] theorem stepDecide_learned (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).branch.learned = cfg.branch.learned := rfl

@[simp] theorem stepDecide_events (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) (vs : Domain) (l : Literal) :
    (stepDecide cfg k v vs l).events = cfg.events := rfl

@[simp] theorem stepDecideSkip_events (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) :
    (stepDecideSkip cfg k v).events = cfg.events := rfl

/-- The redundant-pin skip leaves the learned database unchanged. -/
@[simp] theorem stepDecideSkip_learned (cfg : SchedulerConfig leaf)
    (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).branch.learned = cfg.branch.learned := rfl

@[simp] theorem stepAnalyzeConflict_branch (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).branch = cfg.branch := rfl

@[simp] theorem stepAnalyzeConflict_pending (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).pending = cfg.pending := rfl

@[simp] theorem stepAnalyzeConflict_orig (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).orig = cfg.orig := rfl

@[simp] theorem stepAnalyzeConflict_events (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).events = cfg.events := rfl

/-- The analyze transition records exactly the reported clause. -/
theorem stepAnalyzeConflict_clause (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).conflict.map ConflictEvidence.clause
      = some c := rfl

/-- The recorded analysis is the NORMALIZED allowance run on the pre-state's
trail and level (the evidence-coherence obligation, discharged by `rfl`). -/
theorem stepAnalyzeConflict_analysis (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) :
    ((stepAnalyzeConflict cfg c learned).conflict.map ConflictEvidence.analysis)
      = some (recordedAnalysis cfg c) := rfl

/-- The recording site's map related to the reference analysis: the
normalized allowance image is the reference `analyzeWithAllowance` record
mapped through the canonical form (the same `Option.map` chain). -/
theorem analyzeWithAllowance_eq_ofUIP_normalized (orig : List Domain) (bs : BranchState leaf)
    (c : Clause) :
    (bs.analyzeWithAllowance orig c).map ConflictAnalysis.normalized
      = (analyzeAtAllowance orig bs.trail bs.level c).map
          (fun p => (ConflictAnalysis.ofUIP p.1 p.2).normalized) := by
  rw [analyzeWithAllowance_eq_ofUIP]
  cases analyzeAtAllowance orig bs.trail bs.level c with
  | none => rfl
  | some p => cases p with
    | mk below uip => rfl

/-! ### The counted analyze site (O1 wiring)

`conflictStep` records the evidence through `stepAnalyzeConflictCounted`
with the executed analyzer run's pivot expansions
(`analyzeEventsExpansions`), so the equation lemmas and the phase cases
see the counted call. The projections below keep the counted site
interchangeable with the recording site wherever the counter is
invisible, and expose the two places it is not: `events` and the
evidence's `resolutions` field (both through
`SchedulerConfig.countResolutions`). -/

@[simp] theorem stepAnalyzeConflictCounted_branch (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).branch = cfg.branch := rfl

@[simp] theorem stepAnalyzeConflictCounted_pending (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).pending = cfg.pending := rfl

@[simp] theorem stepAnalyzeConflictCounted_orig (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig := rfl

@[simp] theorem stepAnalyzeConflictCounted_props (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).props = cfg.props := rfl

@[simp] theorem stepAnalyzeConflictCounted_checkpoints
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause)
    (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).checkpoints
      = cfg.checkpoints := rfl

@[simp] theorem stepAnalyzeConflictCounted_events (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).events
      = cfg.events.recordResolutions n := rfl

/-- The analyze site's counter accumulation: exactly the recorded run's
pivot expansions are added to `events.reasonResolutions`. -/
theorem stepAnalyzeConflictCounted_reasonResolutions
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause)
    (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).events.reasonResolutions
      = cfg.events.reasonResolutions + n := rfl

/-- The counted site records the same evidence as `stepAnalyzeConflict`,
except for the per-evidence `resolutions` field, which is incremented by
the counted run. -/
@[simp] theorem stepAnalyzeConflictCounted_conflict (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).conflict
      = (stepAnalyzeConflict cfg c learned).conflict.map
          (fun ev => { ev with resolutions := ev.resolutions + n }) := rfl

@[simp] theorem stepAnalyzeConflictCounted_clause (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).conflict.map
      ConflictEvidence.clause = some c := rfl

@[simp] theorem stepAnalyzeConflictCounted_analysis (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    ((stepAnalyzeConflictCounted cfg c learned n).conflict.map
        ConflictEvidence.analysis)
      = some (recordedAnalysis cfg c) := rfl

/-- The counted recording site's evidence, destructured: the reported
clause, the closure's new clauses, and exactly the computed-allowance
analysis of the recording configuration's own trail and level (the
`resolutions` field is the only difference from `stepAnalyzeConflict`). -/
theorem stepAnalyzeConflictCounted_evidence {cfg : SchedulerConfig leaf}
    {c : Clause} {learned : List Clause} {n : Nat} {ev : ConflictEvidence}
    (h : (stepAnalyzeConflictCounted cfg c learned n).conflict = some ev) :
    ev.clause = c ∧ ev.learned = learned ∧
      ev.analysis = recordedAnalysis cfg c := by
  simp only [stepAnalyzeConflictCounted, stepAnalyzeConflict,
    SchedulerConfig.countResolutions, Option.map_some,
    Option.some.injEq] at h
  rw [← h]
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem stepLearnBackjumpAssert_level (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf)
    (h : restored.level = p.target) :
    (stepLearnBackjumpAssert cfg p ev restored).branch.level = p.target := by
  rw [stepLearnBackjumpAssert]
  exact h

@[simp] theorem stepLearnBackjumpAssert_conflict (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).conflict = none := rfl

@[simp] theorem stepLearnBackjumpAssert_backjumps (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).events.backjumps
      = cfg.events.backjumps + 1 := rfl

@[simp] theorem stepLearnBackjumpAssert_sourceLevel (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).events.sourceLevel
      = cfg.branch.level := rfl

@[simp] theorem stepLearnBackjumpAssert_targetLevel (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).events.targetLevel = p.target := rfl

@[simp] theorem stepLearnBackjumpAssert_assertingEnqueues
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).events.assertingEnqueues
      = cfg.events.assertingEnqueues + 1 := rfl

/-- The jump only retires checkpoints above the target: the checkpoints at
or below the target still identify the restored branch. -/
theorem stepLearnBackjumpAssert_checkpoints (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).checkpoints
      = cfg.checkpoints.filter fun cp => cp.level ≤ p.target := rfl

@[simp] theorem stepLocalExclude_log (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).log = cfg.log.register r := rfl

@[simp] theorem stepLocalExclude_status (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).status = .dead := rfl

@[simp] theorem stepLocalExclude_pending (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).pending = cfg.pending := rfl

@[simp] theorem stepLocalExclude_events (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).events = cfg.events := rfl

@[simp] theorem stepChronologicalFallback_log (cfg : SchedulerConfig leaf)
    (r : DeadRegion) :
    (stepChronologicalFallback cfg r).log = cfg.log.register r := rfl

@[simp] theorem stepChronologicalFallback_status (cfg : SchedulerConfig leaf)
    (r : DeadRegion) : (stepChronologicalFallback cfg r).status = .dead := rfl

@[simp] theorem stepChronologicalFallback_events (cfg : SchedulerConfig leaf)
    (r : DeadRegion) :
    (stepChronologicalFallback cfg r).events = cfg.events := rfl

/-- The consume step is total on the pending stack: `none` exactly when
the frontier is exhausted (the `unsat` precondition). -/
theorem stepConsume_eq_none_iff (cfg : SchedulerConfig leaf) :
    stepConsume cfg = none ↔ cfg.pending = [] := by
  obtain ⟨orig, original, props, branch, checkpoints, pending, log, status,
    conflict, events, stats, poolHash, learnedNorm⟩ := cfg
  cases pending with
  | nil => unfold stepConsume; simp
  | cons f rest =>
      unfold stepConsume
      simp

/-- The consume successor's learned database is the predecessor's: the
canonical resume carries it unchanged (and so did the retired
`resumeSibling` route). -/
theorem stepConsume_learned {cfg next : SchedulerConfig leaf}
    (h : stepConsume cfg = some next) :
    next.branch.learned = cfg.branch.learned := by
  unfold stepConsume at h
  cases hp : cfg.pending with
  | nil => rw [hp] at h; cases h
  | cons f rest =>
      rw [hp] at h
      dsimp only at h
      simp only [Option.some.injEq] at h
      subst h
      exact resumePending_learned cfg.orig cfg.branch f

/-! ## The frozen transition result and the dispatcher (INTERFACES §2.5) -/

/-- One runtime transition. Each constructive case carries the successor
configuration; `sat`/`unsat` are terminal. -/
inductive SchedulerTransition (leaf : Assignment → Bool) where
  /-- propagation reached the closure's fixpoint for this phase -/
  | propagate (next : SchedulerConfig leaf)
  /-- a decision/split opened a fresh level with `decision` -/
  | decide (next : SchedulerConfig leaf) (decision : Literal)
  /-- the leaf check succeeded with this witness -/
  | sat (witness : Assignment)
  /-- the closure found a conflict; its evidence is now recorded -/
  | analyzeConflict (next : SchedulerConfig leaf) (conflict : Clause)
  /-- the complete learn/backjump/assert transition -/
  | learnBackjumpAssert (next : SchedulerConfig leaf) (plan : BackjumpPlan leaf)
      (analysis : ConflictAnalysis)
  /-- the branch is locally dead (never a global claim) -/
  | localExclude (next : SchedulerConfig leaf)
  /-- analysis produced no asserting result: chronological continuation -/
  | chronologicalFallback (next : SchedulerConfig leaf)
  /-- the frontier is exhausted (or a root contradiction was proved) -/
  | unsat

/-- The stable-branch dispatch, UNGUARDED REFERENCE: leaf SAT check, then
split (always `stepDecide`), then local exclusion of a finished-but-failing
branch. Kept as the named unguarded reference; the dispatcher uses
`stableStepGuarded`, whose redundant-pin arm is `stepDecideSkip`. -/
def stableStep (cfg : SchedulerConfig leaf) : SchedulerTransition leaf :=
  match leafWitness leaf cfg with
  | some w => .sat w
  | none =>
      match splitData cfg.branch.frame cfg.prio with
      | some (l, k, v, vs) => .decide (stepDecide cfg k v vs l) l
      | none => .localExclude (stepLocalExclude cfg [] (branchRegion cfg))

/-- THE GUARDED STABLE DISPATCH (B1, WIRED): the `.decide` arm fires
`stepDecide` only when the pin is fresh and `stepDecideSkip` when it is
redundant. `schedulerNext` calls THIS function; `stableStep` remains the
unguarded reference. Consumers split on
`TrailRedundant cfg.branch.trail l`. -/
def stableStepGuarded (cfg : SchedulerConfig leaf) : SchedulerTransition leaf :=
  match leafWitness leaf cfg with
  | some w => .sat w
  | none =>
      match splitData cfg.branch.frame cfg.prio with
      | some (l, k, v, vs) =>
          if TrailRedundant cfg.branch.trail l then
            .decide (stepDecideSkip cfg k v) l
          else .decide (stepDecide cfg k v vs l) l
      | none => .localExclude (stepLocalExclude cfg [] (branchRegion cfg))

/-- The conflict dispatch: an empty reported clause list is a database
refutation (LOCAL, never a global UNSAT); a level-0 conflict is the root
contradiction route (`UnsatEvidence`'s second disjunct); otherwise the
analysis evidence is recorded. -/
def conflictStep (cfg : SchedulerConfig leaf) (cs : List Clause)
    (learned : List Clause) : SchedulerTransition leaf :=
  match cs with
  | [] => .localExclude (stepLocalExclude cfg learned (branchRegion cfg))
  | c :: _ =>
      if cfg.branch.level = 0 then .unsat
      else .analyzeConflict (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) c

/-- THE SINGLE-RUN CONFLICT DISPATCH: the same transition as `conflictStep`,
but the analyzed conflict is computed ONCE (`countedAnalysisFast`) and both
projections — the recorded analysis and the `reasonResolutions` increment —
are read off that run. The fast novelty guard also reads the runtime caches.
Equal to `conflictStep` on every cache-aligned configuration
(`conflictStepFast_eq`), including the exact counter value. -/
def conflictStepFast (cfg : SchedulerConfig leaf) (cs : List Clause)
    (learned : List Clause) : SchedulerTransition leaf :=
  match cs with
  | [] => .localExclude (stepLocalExclude cfg learned (branchRegion cfg))
  | c :: _ =>
      if cfg.branch.level = 0 then .unsat
      else
        let ac := countedAnalysisFast cfg c
        .analyzeConflict
          (stepAnalyzeConflictCountedOf cfg c learned ac.1 ac.2) c

/-- EXACTNESS of the single-run conflict dispatch: on cache-aligned
configurations it is the reference `conflictStep`, so the recorded evidence
AND `events.reasonResolutions` are unchanged. -/
theorem conflictStepFast_eq {cfg : SchedulerConfig leaf} {cs : List Clause}
    {learned : List Clause} (hdb : cfg.LearnedNormAligned)
    (hpool : cfg.PoolHashAligned) (hkeys : cfg.LearnedKeysSound) :
    conflictStepFast cfg cs learned = conflictStep cfg cs learned := by
  unfold conflictStepFast conflictStep
  cases cs with
  | nil => rfl
  | cons c rest =>
      by_cases h : cfg.branch.level = 0
      · simp only [h, if_true]
      · simp only [h, if_false, countedAnalysisFast_fst hdb hpool hkeys,
          countedAnalysisFast_snd, stepAnalyzeConflictCountedOf_eq]

/-- The consume dispatch: resume or report UNSAT. -/
def consumeStep (cfg : SchedulerConfig leaf) : SchedulerTransition leaf :=
  match stepConsume cfg with
  | some next => .chronologicalFallback next
  | none => .unsat

/-- The chronological-fallback emission is UNSAT exactly when there is no
alternative left to consume. -/
theorem consumeStep_unsat_iff (cfg : SchedulerConfig leaf) :
    consumeStep cfg = .unsat ↔ cfg.pending = [] := by
  rw [consumeStep]
  cases h : stepConsume cfg with
  | none => exact ⟨fun _ => (stepConsume_eq_none_iff (cfg := cfg)).mp h,
      fun _ => rfl⟩
  | some next =>
      refine ⟨fun hc => ?_, fun hp => ?_⟩
      · cases hc
      · rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at h
        cases h

/-- The conflict dispatch is UNSAT exactly for a level-0 conflict with a
nonempty reported clause: the root-contradiction route of
`UnsatEvidence`. An empty reported clause list is the LOCAL case and never
yields `.unsat`. -/
theorem conflictStep_unsat_iff {cfg : SchedulerConfig leaf}
    {cs : List Clause} {learned : List Clause} :
    conflictStep cfg cs learned = .unsat ↔
      (∃ c rest, cs = c :: rest) ∧ cfg.branch.level = 0 := by
  unfold conflictStep
  cases cs with
  | nil => simp
  | cons c rest => simp

/-- The leaf check reports a witness exactly for a complete frame passing
the leaf predicate. -/
theorem leafWitness_eq_some_iff {cfg : SchedulerConfig leaf}
    {w : Assignment} :
    leafWitness leaf cfg = some w ↔
      cfg.branch.frame.assignment? = some w ∧ leaf w = true := by
  unfold leafWitness
  cases hf : cfg.branch.frame.assignment? with
  | none => simp only [hf]; simp
  | some w' =>
      cases hl : leaf w' with
      | true =>
          simp only [hf, hl, if_true, Option.some.injEq]
          exact ⟨fun h => ⟨h, by rw [← h]; exact hl⟩, fun h => h.1⟩
      | false =>
          simp only [hf, hl, if_false]
          constructor
          · intro h; cases h
          · rintro ⟨heq, hw⟩
            have hw' : w' = w := Option.some.inj heq
            rw [← hw'] at hw
            rw [hl] at hw
            cases hw

/-- The recorded-conflict dispatch: perform the allowance analysis step
and either complete the jump, fall back chronologically, or exclude the
branch locally when the assertion rejects the restored frame. -/
def backjumpStep (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) :
    SchedulerTransition leaf :=
  match ev.analysis with
  | none => .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg))
  | some an =>
      match checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg))
      | some cp =>
          let p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned
          match p.perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              -- the assertion rejects the restored ancestor: the CHECKPOINT's
              -- prefix is the dead region, not the current branch's
              .localExclude (stepLocalExclude cfg ev.learned (checkpointRegion cp))
          | some restored =>
              .learnBackjumpAssert (stepLearnBackjumpAssert cfg p ev restored) p an

/-- The scheduler's one-step transition (INTERFACES §2.5). It is
phase-driven and never repeats a step: an active branch either propagates
one deduction, records a conflict's evidence, splits, reports a witness,
or is excluded; a dead branch is consumed; recorded evidence is resolved
by the jump/fallback/exclusion decision. C2 proves per-constructor
coverage and coherence; C3 chooses the termination measure. -/
def schedulerNext (cfg : SchedulerConfig leaf) : SchedulerTransition leaf :=
  match cfg.conflict with
  | some ev => backjumpStep cfg ev
  | none =>
      match cfg.status with
      | .dead => consumeStep cfg
      | .active =>
          match explainedDeduction cfg.original cfg.props cfg.branch with
          | some d => .propagate (stepPropagate cfg d)
          | none =>
              match terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | .stable _ => stableStepGuarded cfg
              | .conflict _ cs learned => conflictStep cfg cs learned
              | .localExcluded _ _ _ learned =>
                  .localExclude (stepLocalExclude cfg learned (branchRegion cfg))

/-! ## Bridging lemmas: the dispatcher's fixpoint gate and A2's result -/

/-- The dispatch's fixpoint gate is exactly A2's: when no productive
deduction is selected, `explainedClosureResult` is `terminalResult`. -/
theorem explainedDeduction_eq_none_of_event_stable (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf)
    (h : nextPruningEvent original props bs.frame bs.learned = .stable) :
    explainedDeduction original props bs = none := by
  rw [explainedDeduction, h]

/-- When no productive deduction is selected, the closure is the identity. -/
theorem explainedClosure_eq_self_of_deduction_none (orig : List Domain)
    (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf)
    (h : explainedDeduction original props bs = none) :
    explainedClosure orig original props bs = bs := by
  rw [explainedClosure, h]

/-- At a fixpoint the result-returning closure reports A2's terminal
classification — the dispatch's `terminalResult` call agrees with
`explainedClosureResult` at every site that uses it. -/
theorem explainedClosureResult_eq_terminalResult_of_deduction_none
    (orig : List Domain) (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf)
    (h : explainedDeduction original props bs = none) :
    explainedClosureResult orig original props bs
      = terminalResult orig original props bs := by
  rw [explainedClosureResult, h]

/-! ## The component fixture (C1 done criteria)

A concrete pre-configuration on which the learn/backjump/assert transition
VISIBLY changes level and frame: the source branch sits at level 3 with a
three-slot box; the plan's checkpoint is the ancestor at level 1 (prefix
`[1]`, remaining slots `{0,1}, {0,1}`); the learned unit clause asserts
`slot 1 ≠ 0`, so restoration plus assertion narrowing removes `0` from
slot 1's remaining domain — the sibling the jump must explore. The theorem
is proved by evaluation (`rfl`/`rw`), not by a runtime test; general
forward correctness is C2's. -/

/-- Fixture leaf predicate: every assignment passes (component-level). -/
def fixtureLeaf : Assignment → Bool := fun _ => true

/-- The fixture's source frame (level 2): slots 0/1 decided to `1`/`0`,
slot 2 remaining `{0,1}` — a descendant of the checkpoint frame. -/
def fixtureSourceFrame : BranchFrame :=
  ⟨[Dom.ofList [Value.int 1], Dom.ofList [Value.int 0],
    Dom.ofList [Value.int 0, Value.int 1]], [0, 1]⟩

/-- The fixture's checkpoint frame (level 1): slot 0 decided to `1`,
slots 1 and 2 remaining `{0,1}`. -/
def fixtureTargetFrame : BranchFrame :=
  ⟨[Dom.ofList [Value.int 1], Dom.ofList [Value.int 0, Value.int 1],
    Dom.ofList [Value.int 0, Value.int 1]], [0]⟩

/-- The fixture's narrowed frame: the assertion `slot 1 ≠ 0` removes `0`
from slot 1's remaining domain. -/
def fixtureNarrowedFrame : BranchFrame :=
  ⟨[Dom.ofList [Value.int 1], Dom.ofList [Value.int 1],
    Dom.ofList [Value.int 0, Value.int 1]], [0]⟩

/-- The fixture's asserting literal: slot 1 is not 0. -/
def fixtureAsserting : Literal := posNe 1 0

/-- The fixture's learned clause: the unit assertion. -/
def fixtureLearned : Clause := [posNe 1 0]

/-- The fixture's checkpoint: the ancestor at level 1. -/
def fixtureCheckpoint : DecisionCheckpoint fixtureLeaf :=
  { level := 1, frame := fixtureTargetFrame, trail := [] }

/-- The fixture's plan, built from the checkpoint record (so the level law
is discharged by construction). -/
def fixturePlan : BackjumpPlan fixtureLeaf :=
  BackjumpPlan.ofCheckpoint fixtureCheckpoint
    { frame := fixtureSourceFrame, trail := [], level := 3, learned := [] }
    fixtureAsserting fixtureLearned

/-- The fixture's source configuration: level 3, the checkpoint at level 1. -/
def fixtureCfg : SchedulerConfig fixtureLeaf :=
  { orig := [Dom.ofList [.int 0, .int 1], Dom.ofList [.int 0, .int 1]]
    original := []
    props := []
    branch := { frame := fixtureSourceFrame, trail := [], level := 3, learned := [] }
    checkpoints := [fixtureCheckpoint]
    pending := []
    log := {} }

/-- The fixture's restored state before the frame/trail synchronisation
(the closure is the identity here because the fixture registers no
clauses/propagators, and the learned unit clause is no longer productive in
the narrowed frame). -/
def fixtureRestoredPre : BranchState fixtureLeaf :=
  { frame := fixtureNarrowedFrame
    trail := [{ literal := fixtureAsserting.norm, level := 1,
                reason := some { clause := fixtureLearned } }]
    level := 1
    learned := [fixtureLearned] }

/-- The fixture's restored state: the exact `perform` result (the
synchronised state: the narrowed frame fixes slot 1 to `1`, and the new
bound literal is recorded). -/
def fixtureRestored : BranchState fixtureLeaf :=
  syncAll fixtureCfg.orig fixtureRestoredPre

/-- The restoration/insertion/narrowing part of `perform` on the fixture,
before propagation resumes. -/
def fixtureRestoredRaw : BranchState fixtureLeaf :=
  (fixturePlan.execute (fixtureCfg.branch.learnGlobal fixturePlan.learned)).narrowFrame
    fixtureNarrowedFrame

/-- The raw restored state is the hand-written fixture state: exact
restoration, the single asserting entry, the inserted learned clause. -/
theorem fixtureRestoredRaw_eq : fixtureRestoredRaw = fixtureRestoredPre := rfl

/-- The fixture's recorded conflict evidence (analysis `none`: the jump's
evidence is the plan and the restored state here). -/
def fixtureEvidence : ConflictEvidence :=
  { clause := fixtureLearned, learned := [], analysis := none }

/-- The source frame descends from the checkpoint frame: a level-3 branch
with prefix `[1,0]` covers only assignments that the level-1 ancestor with
prefix `[1]` and remaining slots `{0,1}, {0,1}` also covers. -/
theorem fixtureFrame_descends : FrameDescendsFrom fixtureSourceFrame fixtureTargetFrame := by
  intro a ha
  refine mem_allAssigns_of_getElem? _ _ ?_ ?_
  · rw [(allAssigns_fits _ _ ha).1]
    simp [fixtureSourceFrame, fixtureTargetFrame]
  · intro j v hv
    have hsrc : v ∈ fixtureSourceFrame.doms.getD j Dom.empty :=
      (allAssigns_fits _ _ ha).2 j v hv
    cases j with
    | zero =>
        have hv1 : v = Value.int 1 := by
          have h := hsrc
          simp [fixtureSourceFrame] at h
          exact h
        subst hv1
        simp [fixtureTargetFrame]
    | succ j =>
        cases j with
        | zero =>
            have hv0 : v = Value.int 0 := by
              have h := hsrc
              simp [fixtureSourceFrame] at h
              exact h
            subst hv0
            simp [fixtureTargetFrame]
        | succ j =>
            cases j with
            | zero =>
                have hmem := hsrc
                simp [fixtureSourceFrame] at hmem
                simpa [fixtureTargetFrame] using hmem
            | succ j =>
                have hmem := hsrc
                simp [fixtureSourceFrame] at hmem

/-- The fixture's checkpoint identifies the source branch at level 1: same
level, empty trail prefix, frame descent. -/
theorem fixtureCheckpoint_identifies :
    fixtureCheckpoint.Identifies fixtureCfg.branch 1 := by
  refine ⟨rfl, ⟨[], ?_, ?_⟩, ?_⟩
  · rfl
  · intro e he
    cases he
  · exact fixtureFrame_descends

/-- The fixture's plan identifies its source branch (the level law comes
from the checkpoint record, not from a caller premise). -/
theorem fixturePlan_identifies : fixturePlan.Identifies fixtureCfg.branch :=
  BackjumpPlan.ofCheckpoint_identifies fixtureCheckpoint_identifies

/-- The fixture's plan filters the restored frame exactly to the narrowed
frame: the assertion `slot 1 ≠ 0` removes `0` from slot 1's domain and
leaves the prefix alone. -/
theorem fixturePlan_filter :
    filterFrame fixtureAsserting fixtureTargetFrame = some fixtureNarrowedFrame :=
  rfl

/-- `perform` on the fixture yields exactly the restored state: insertion,
exact restoration, assertion narrowing, recorded reason, and resumed
propagation (the fixture's closure is the identity). -/
theorem fixturePlan_perform :
    fixturePlan.perform fixtureCfg.branch fixtureCfg.orig [] [] = some fixtureRestored := by
  have hnone : explainedDeduction ([] : List Clause) ([] : List Propagator)
      (syncAll fixtureCfg.orig fixtureRestoredRaw) = none := rfl
  have hraw : (fixturePlan.execute
        (fixtureCfg.branch.learnGlobal fixturePlan.learned)).narrowFrame
        fixtureNarrowedFrame = fixtureRestoredRaw := rfl
  unfold BackjumpPlan.perform BackjumpPlan.restoreNarrow
  rw [show filterFrame fixturePlan.asserting fixturePlan.checkpoint.frame
      = some fixtureNarrowedFrame from rfl]
  simp only [Option.map_some]
  rw [hraw, explainedClosure_eq_self_of_deduction_none _ _ _ _ hnone,
    fixtureRestoredRaw_eq]
  rfl

/-- The fixture's source and narrowed frames differ (their prefixes have
different lengths) — the frame change the fixture exhibits. -/
theorem fixture_frames_differ : fixtureSourceFrame ≠ fixtureNarrowedFrame := by
  intro h
  have hlen : fixtureSourceFrame.2.length = fixtureNarrowedFrame.2.length := by
    rw [h]
  simp [fixtureSourceFrame, fixtureNarrowedFrame] at hlen

/-- The fixture's source configuration sits at level 3. -/
theorem fixtureCfg_level : fixtureCfg.branch.level = 3 := rfl

/-- **THE COMPONENT FIXTURE (C1 done criteria).** For the concrete
pre-configuration, the learn/backjump/assert step's successor configuration
answers with the TARGET level, the NARROWED target frame, a level strictly
below the source level, a frame visibly different from the source frame,
and the §2.7 counters recorded at the site. -/
theorem backjump_fixture_moves_level_and_frame :
    (stepLearnBackjumpAssert fixtureCfg fixturePlan fixtureEvidence
        fixtureRestored).branch.level = 1 ∧
    (stepLearnBackjumpAssert fixtureCfg fixturePlan fixtureEvidence
        fixtureRestored).branch.frame = fixtureNarrowedFrame ∧
    (stepLearnBackjumpAssert fixtureCfg fixturePlan fixtureEvidence
        fixtureRestored).branch.level ≠ fixtureCfg.branch.level ∧
    fixtureSourceFrame ≠ fixtureNarrowedFrame ∧
    (stepLearnBackjumpAssert fixtureCfg fixturePlan fixtureEvidence
        fixtureRestored).events =
      { backjumps := 1, sourceLevel := 3, targetLevel := 1,
        assertingEnqueues := 1 } := by
  refine ⟨rfl, rfl, ?_, fixture_frames_differ, ?_⟩
  · rw [fixtureCfg_level]
    decide
  · rw [stepLearnBackjumpAssert, fixtureCfg, fixturePlan, BackjumpPlan.ofCheckpoint,
      fixtureCheckpoint, RuntimeEvents.recordBackjump]

end LeanFzn.Solver.UIP
