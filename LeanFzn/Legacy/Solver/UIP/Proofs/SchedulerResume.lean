/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerResume.lean

Purpose:
  Dead-region registration soundness, local exclusion, chronological
  fallback, pending-alternative resume and provenance for the scheduler
  of `LeanFzn/Solver/UIP/SchedulerStep.lean`.

  * REGISTRATION SOUNDNESS at the real registration sites: the log-level
    `ExhaustionLog.Sound` is preserved by registering a region whose
    exclusion is proved (`local_exclusion_ofFrame_sound` for the branch
    frame's region, `DeadRegion.byFalse_sound`/`byAllTrue_sound` for the
    literal regions), and it composes with `ClassificationSound.retains`
    (`classification_next_within_pending`): a leaf solution is never
    "covered" by an exhaustion region.
  * LOCAL EXCLUSION / CHRONOLOGICAL FALLBACK check of `branchRegion` and
    `checkpointRegion`: both register `DeadRegion.byPrefix` of a *narrowed*
    frame's chosen prefix. `narrowed_prefix_region_not_sound` is the
    counterexample — the prefix region of a narrowed frame contains a leaf
    solution of a live sibling. The honest, exactly-covering region is
    `DeadRegion.ofFrame` (`narrowed_frame_region_sound`).
  * RESUME: `stepConsume`'s checkpoint-by-prefix-length path is REPAIRED.
    `stepConsume_resumes_without_retirement` exhibits the failed
    child/live sibling configuration: the resumed trail is the ancestor
    checkpoint's trail, which carries no falsifier for the dropped value,
    so `ResumeCoherent` is unsatisfiable for it. The repair `resumeSibling`
    (in `BackjumpFrontier.lean`) restores by level and records the
    retirement; `resumeSibling_retires` is its correctness theorem.
  * PROVENANCE: a registered region stays registered under every later
    registration (`ExhaustionLog.registered_permanent`) and contains no
    leaf solution (`ExhaustionLog.Sound`), so resume cannot recreate
    exhausted work (`registered_region_excludes_solutions`).
  * REGRESSIONS: failed child with a live sibling
    (`C2b_resume_failed_child_live_sibling`) and a sparse, typed domain
    where the int-view region conflates `.bool true` with `.int 1`
    (`C2b_sparse_typed_region`).

Dependencies:
  - LeanFzn.Solver.UIP.SchedulerStep: `stepConsume`, `ResumeCoherent`,
    `branchRegion`, `checkpointRegion`, `SchedulerConfig`
  - LeanFzn.Solver.Propagation.BackjumpFrontier: `DeadRegion`, `ExhaustionLog`,
    `DeadRegion.ofFrame`, `resumeSibling`, `resumeSibling_retires`
  - LeanFzn.Solver.Core.Enumerate: `mem_allAssigns_singleton`

DAG:
  SchedulerStep -> Proofs.SchedulerResume (this module; leaf, consumed by
  C2c/C2d and by the coordinator's registration).
-/

import LeanFzn.Legacy.Solver.UIP.SchedulerStep
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Registration soundness at the real sites -/

/-- LOCAL EXCLUSION registration: the branch frame's region is sound when
the branch is dead (no leaf solution is covered by the frame). This is the
obligation the `stepLocalExclude` arms of `stableStep`/`conflictStep` must
discharge; `branchRegion`'s larger prefix region does not satisfy it (see
`narrowed_prefix_region_not_sound`). -/
theorem local_exclusion_ofFrame_sound {leaf : Assignment → Bool}
    {f : BranchFrame}
    (hdead : ∀ a, leaf a = true → FrameCovers f a → False) :
    DeadRegion.Sound leaf (DeadRegion.ofFrame f) :=
  DeadRegion.ofFrame_sound hdead

/-- CHRONOLOGICAL FALLBACK registration: the same obligation for the
fallback arm (the analysis produced no asserting result and the branch is
locally dead). -/
theorem fallback_ofFrame_sound {leaf : Assignment → Bool} {f : BranchFrame}
    (hdead : ∀ a, leaf a = true → FrameCovers f a → False) :
    DeadRegion.Sound leaf (DeadRegion.ofFrame f) :=
  local_exclusion_ofFrame_sound hdead

/-- Log-level soundness of one registration step: registering a proved-dead
region preserves `ExhaustionLog.Sound`, the invariant resumed branches may
not contradict. -/
theorem register_dead_region_sound {leaf : Assignment → Bool}
    {log : ExhaustionLog} {f : BranchFrame}
    (hsound : log.Sound leaf)
    (hdead : ∀ a, leaf a = true → FrameCovers f a → False) :
    (log.register (DeadRegion.ofFrame f)).Sound leaf :=
  ExhaustionLog.register_sound hsound (local_exclusion_ofFrame_sound hdead)

/-- PROVENANCE (the "resume cannot recreate exhausted work" half at region
level): every later registration sequence keeps a registered region
registered, and — because the log is sound — no leaf solution is inside it.
The bridge to `ClassificationSound.retains` is immediate: the `retains`
third disjunct (region membership) can justify *deleting* an alternative,
never *covering* a leaf solution, so `CoversRemainingLeaves` has no
exhaustion disjunct. -/
theorem registered_region_excludes_solutions {leaf : Assignment → Bool}
    {log : ExhaustionLog} {r : DeadRegion} (hsound : log.Sound leaf)
    (hmem : r ∈ log.regions) (extra : List DeadRegion) :
    r ∈ (extra.foldl ExhaustionLog.register log).regions ∧
      ∀ a, leaf a = true → r.mem a = true → False :=
  ⟨ExhaustionLog.registered_permanent hmem extra, hsound r hmem⟩

/-- The shrinking half of the composition: a sound classification never
enumerates a solution the pending frontier did not. -/
theorem classification_next_within_pending {leaf : Assignment → Bool}
    {pending next : List BranchFrame} {log : ExhaustionLog}
    {db : List Clause}
    (h : ClassificationSound (leaf := leaf) pending next log db) :
    ∀ a, FrontierCovers next a → FrontierCovers pending a :=
  h.noNew

/-! ## Small assignment-shape helpers (no `BEq Value` in this cone) -/

/-- Membership in a singleton list is equality (instance-free form). -/
private theorem mem_singleton_eq {α : Type} {a b : α} (h : a ∈ [b]) : a = b := by
  rcases List.mem_cons.mp h with h | h
  · exact h
  · cases h

/-- The single-slot assignments of `[Dom.ofList [x]]` are exactly `[x]`. -/
private theorem allAssigns_single {x : Value} {tail : Assignment} :
    tail ∈ allAssigns ([Dom.ofList [x]] : List Domain) → tail = [x] := by
  intro h
  obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp h
  have hw' : w = x := by
    have hwE : w ∈ Dom.enum (Dom.ofList [x]) := (DomainLike.mem_iff _ _).mp hw
    rw [Dom.enum_ofList] at hwE
    exact mem_singleton_eq hwE
  have ha'' : a' = [] := by
    simpa [allAssigns] using ha'
  rw [hw', ha'']

/-- A single-value domain frame covers exactly its own assignment. -/
theorem frameCovers_single {x y : Value}
    (h : FrameCovers (⟨[Dom.ofList [x]], []⟩ : BranchFrame) [y]) : y = x := by
  have ht : [y] = [x] := allAssigns_single h
  exact (List.cons.inj ht).1

/-- A single-value frame covers its own assignment. -/
private theorem self_mem_allAssigns_single {x : Value} :
    ([x] : Assignment) ∈ allAssigns ([Dom.ofList [x]] : List Domain) :=
  mem_allAssigns_cons_iff.mpr
    ⟨x, (DomainLike.mem_iff _ _).mpr (by rw [domElems_eq_enum, Dom.enum_ofList]; exact List.mem_cons_self ..),
      [], by simp [allAssigns], rfl⟩

/-- Region membership is false exactly when the frame does not cover the
assignment (the `Bool`-valued form used by the regressions). -/
private theorem ofFrame_mem_false {f : BranchFrame} {a : Assignment}
    (h : ¬ FrameCovers f a) : (DeadRegion.ofFrame f).mem a = false := by
  cases hb : (DeadRegion.ofFrame f).mem a with
  | false => rfl
  | true => exact absurd (DeadRegion.ofFrame_mem_iff.mp hb) h

/-! ## The regions of the real transition functions are not rich enough -/

/-- COUNTEREXAMPLE (local exclusion / chronological fallback): the prefix
region of a *narrowed* frame is not sound. The frame `([[]], [])` below is
the root frame of a one-slot problem narrowed to the value `5` by a
branch-local reason: it is dead, but the region `branchRegion` registers is
`byPrefix []`, which contains every assignment — including the leaf
solution `9` the narrowing removed. Registering it deletes live work.

This is the plan's warning made concrete: a narrowed frame's failure need
not exclude every extension of its prefix. -/
theorem narrowed_prefix_region_not_sound :
    ¬ DeadRegion.Sound
      (fun a => decide (slotInt a 0 = some 9))
      (DeadRegion.byPrefix ([] : Assignment)) := by
  intro h
  exact h [Value.int 9] (by rfl) (by rfl)

/-- The narrowed frame of `narrowed_prefix_region_not_sound` is dead, and
the honest frame region is sound for it (the prefix region is not). -/
theorem narrowed_frame_region_sound :
    DeadRegion.Sound (fun a => decide (slotInt a 0 = some 9))
      (DeadRegion.ofFrame (⟨[Dom.ofList [Value.int 5]], []⟩ : BranchFrame)) := by
  refine DeadRegion.ofFrame_sound ?_
  rintro a hl hcov
  have hy : a = [Value.int 5] := allAssigns_single hcov
  rw [hy] at hl
  exact absurd hl (by decide)

/-! ## The frozen `stepConsume` resume -/

/-- The failed child / live sibling configuration: slot 0 has the domain
`{1, 2}`; the child decided `1` (frame `([[]], [1])`, level 1), the sibling
`([[2]], [])` is pending, and the only surviving checkpoint is the root one
(level 0, chosen prefix `[]`). -/
def failedChildConfig (leaf : Assignment → Bool) : SchedulerConfig leaf where
  orig := [Dom.ofList [Value.int 1, Value.int 2]]
  original := []
  props := []
  branch :=
    { frame := ⟨[Dom.ofList [Value.int 1]], [0]⟩
      trail := [{ literal := negNe 0 1, level := 1, reason := none }]
      level := 1
      learned := [] }
  checkpoints := [rootCheckpoint [Dom.ofList [Value.int 1, Value.int 2]]]
  pending := [⟨[Dom.ofList [Value.int 2]], []⟩]
  log := {}

/-- C2b-int COMPATIBILITY UPDATE (R2 repair, second stage): the
characterization of `stepConsume` at the counterexample configuration,
restated for the single canonical route. The checkpoint list is EMPTIED
(stale snapshots cannot identify the frame-derived trail) and the branch is
the canonical resume of the pending frame — the entry the old
prefix-length route could not supply. The counterexample theorem
`stepConsume_resumes_without_retirement` below remains valid: it is about
the incoherent empty-trail state, which no runtime route produces. -/
theorem failedChildConfig_stepConsume :
    stepConsume (failedChildConfig leaf) =
      some { (failedChildConfig leaf) with
             branch := resumePending (failedChildConfig leaf).orig
               (failedChildConfig leaf).branch (⟨[Dom.ofList [Value.int 2]], []⟩ : BranchFrame)
             checkpoints := []
             pending := []
             status := .active
             conflict := none } := rfl

/-- THE `stepConsume` COUNTEREXAMPLE: the resumed configuration is not
`ResumeCoherent`. The sibling frame `([[2]], [])` retires the value `1` at
its head slot, so coherence demands a falsifying trail entry for `1`; the
resumed trail is empty, and — this is the defect, not an accident of this
instance — the checkpoint at level `[]` was saved *before* slot 0 was
split, so no prefix-length checkpoint ever carries that falsifier. The
repair is `resumeSibling` in `BackjumpFrontier.lean`, which recovers the
dropped value from the ancestor checkpoint's frame and records the
retirement (`resumeSibling_retires`). -/
theorem stepConsume_resumes_without_retirement
    (leaf : Assignment → Bool) :
    ¬ ∃ cp : DecisionCheckpoint leaf,
      ResumeCoherent [Dom.ofList [Value.int 1, Value.int 2]]
        (⟨[Dom.ofList [Value.int 2]], []⟩ : BranchFrame) cp
        { frame := ⟨[Dom.ofList [Value.int 2]], []⟩
          trail := []
          level := 0
          learned := [] } := by
  rintro ⟨cp, _hframe, _htrail, _hlevel, _hfits, hretire⟩
  have hmem : Value.int 1 ∈
      ([Dom.ofList [Value.int 1, Value.int 2]] : List Domain).getD 0 Dom.empty := by
    show Value.int 1 ∈ Dom.ofList [Value.int 1, Value.int 2]
    exact (DomainLike.mem_iff _ _).mpr
      (by rw [domElems_eq_enum, Dom.enum_ofList]; exact List.mem_cons_self ..)
  have hnot : Value.int 1 ∉
      ([Dom.ofList [Value.int 2]] : List Domain).getD 0 Dom.empty := by
    show Value.int 1 ∉ Dom.ofList [Value.int 2]
    intro hc
    have hcE : Value.int 1 ∈ Dom.enum (Dom.ofList [Value.int 2]) :=
      (DomainLike.mem_iff _ _).mp hc
    rw [Dom.enum_ofList] at hcE
    have h12 : (1 : Int) = 2 := Value.int.inj (mem_singleton_eq hcE)
    omega
  obtain ⟨e, he, _⟩ := hretire 0 (by simp) (Value.int 1) hmem hnot
  exact List.not_mem_nil he

/-- The repaired resume at the same configuration: it records the
retirement of the dropped head value `1`, recovered from the ancestor
checkpoint's frame, so the resumed sibling trail carries the falsifier the
frozen `stepConsume` trail cannot supply. -/
theorem repaired_resume_retires (leaf : Assignment → Bool)
    (bs : BranchState leaf) :
    ∃ e ∈ (resumeSibling bs (⟨[Dom.ofList [Value.int 2]], []⟩ : BranchFrame)
            0 (Value.int 1)).trail,
      e.literal.atom.slot = 0 ∧ e.literal.valueHolds (Value.int 1) = false :=
  resumeSibling_retires (k := 0) (v := Value.int 1) rfl

/-! ## Regressions (PLAN C2b: failed child/live sibling, sparse domain) -/

/-- REGRESSION 1 (failed child / live sibling). Slot 0 of the original box
`{1, 2}` was narrowed to `1` for the child (a branch-local reason), the
child is dead, and the sibling frame `([[2]], [])` is live: `[2]` is a leaf
solution. The honest child region is sound and excludes `[2]`; the *parent*
prefix region — what `branchRegion` registers for the parent frame —
contains `[2]`, so registering it would delete live work. -/
theorem C2b_resume_failed_child_live_sibling :
    (fun a => decide (slotInt a 0 = some 2)) [Value.int 2] = true ∧
    DeadRegion.Sound (fun a => decide (slotInt a 0 = some 2))
      (DeadRegion.ofFrame (⟨[Dom.ofList [Value.int 1]], []⟩ : BranchFrame)) ∧
    (DeadRegion.ofFrame (⟨[Dom.ofList [Value.int 1]], []⟩ : BranchFrame)).mem [Value.int 2] = false ∧
    ¬ DeadRegion.Sound (fun a => decide (slotInt a 0 = some 2))
      (DeadRegion.byPrefix ([] : Assignment)) ∧
    (DeadRegion.byPrefix ([] : Assignment)).mem [Value.int 2] = true := by
  refine ⟨by rfl, ?_, ?_, ?_, by rfl⟩
  · -- the dead child's own region is sound
    refine DeadRegion.ofFrame_sound ?_
    rintro a hl hcov
    have hy : a = [Value.int 1] := allAssigns_single hcov
    rw [hy] at hl
    exact absurd hl (by decide)
  · -- and it does not contain the sibling's solution
    refine ofFrame_mem_false ?_
    intro hcov
    have hy : Value.int 2 = Value.int 1 := frameCovers_single hcov
    have : (2 : Int) = 1 := Value.int.inj hy
    omega
  · -- the parent-prefix region does contain it: unsound registration
    intro h
    exact h [Value.int 2] (by rfl) (by rfl)

/-- REGRESSION 2 (sparse, typed domain). The int-view regions
`below`/`above` conflate `.bool true` with `.int 1`: a numerically justified
dead region contains a Boolean leaf solution, so a sound registration must
use the frame region (or the literal vocabulary), never a bare numeric
bound. The sparse-narrowed frame `([[.int 5]], [])` likewise does not cover
the `9` solution, while the empty-prefix region does. -/
theorem C2b_sparse_typed_region :
    ¬ DeadRegion.Sound
        (fun a => (posBool 0 true).eval a == some true)
        (DeadRegion.below 0 2) ∧
      ¬ FrameCovers (⟨[Dom.ofList [Value.int 5]], []⟩ : BranchFrame) [Value.int 9] ∧
      (DeadRegion.byPrefix ([] : Assignment)).mem [Value.int 9] = true := by
  refine ⟨?_, ?_, by rfl⟩
  · intro h
    exact h [Value.bool true] (by rfl) (by rfl)
  · intro hcov
    have h95 : Value.int 9 = Value.int 5 := frameCovers_single hcov
    have : (9 : Int) = 5 := Value.int.inj h95
    omega

/-! ## Concrete consume exports (S2 gate)

Both resume routes are characterized against the ACTUAL predecessor
(`cfg.pending = f :: rest`): the shape lemmas expose frame/pending/log/
database, the coverage export is the `fallback_retains_consume` instance at
the real frontier (head deadness is the site evidence; the resumed sibling
is never discarded), and the coherence exports are the `ResumeCoherent`
components at the restored state. The retirement conjunct's head slot is
DISCHARGED by `resumeSibling_retires`; its deeper slots are the explicit
residual supplied by the split equations (`resumeSibling_resumeCoherent_falsifiers`,
consumed at C2c's dispatcher). -/

/-- SHAPE of the consuming route: both resume routes put the consumed
alternative in the current frame and the rest on the pending stack; the
log, database and original box are carried over unchanged. -/
theorem stepConsume_some_shape {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    next.branch.frame = f ∧ next.pending = rest ∧ next.log = cfg.log ∧
      next.branch.learned = cfg.branch.learned ∧ next.orig = cfg.orig := by
  unfold stepConsume at h
  rw [hp] at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨resumePending_frame _ _ _, rfl, rfl, resumePending_learned _ _ _, rfl⟩

/-- The successor's work list is the predecessor's work list minus its dead
head: the consumed alternative becomes the current frame. -/
theorem stepConsume_frontier_of_pending_cons {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    next.frontier = f :: rest := by
  obtain ⟨hf, hpend, -, -, -⟩ := stepConsume_some_shape hp h
  show next.branch.frame :: next.pending = f :: rest
  rw [hf, hpend]

/-- THE SINGLE RESUME ROUTE (R2 repair): the successor's branch is ALWAYS
the canonical resume of the pending head — the checkpoint-consulting route
(`resumeSibling`) is retired (a genuine reachable run refutes it:
`resumeSibling_shadow_not_represents`, Proofs/PendingRun.lean §4). No
consumer may derive the branch from `checkpointAt`. -/
theorem stepConsume_branch {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    next.branch = resumePending cfg.orig cfg.branch f := by
  unfold stepConsume at h
  rw [hp] at h
  simp only [Option.some.injEq] at h
  subst h
  rfl

/-- COMPATIBILITY WRAPPER (retained name): the missing-checkpoint route's
equation is now UNCONDITIONAL — every consume is the canonical resume, so
the old checkpoint-lookup premise is no longer needed (kept, unused, for
name compatibility). -/
theorem stepConsume_branch_of_no_checkpoint {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest)
    (_hcp : checkpointAt cfg.checkpoints f.level = none)
    (h : stepConsume cfg = some next) :
    next.branch = resumePending cfg.orig cfg.branch f :=
  stepConsume_branch hp h

/-- WHAT THE MISSING-CHECKPOINT ROUTE DOES ESTABLISH (restated by R1): the
trail is exactly the canonical reconstruction (prefix pins at levels
`1..L` and remaining-slot falsifiers at the resumed level), the frame is
the sibling's, the pending stack is the tail and the database is carried.
The trail is backed by the FRAME's own snapshot, not by projected current
history. -/
theorem stepConsume_missing_checkpoint_no_retirement
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest)
    (hcp : checkpointAt cfg.checkpoints f.level = none)
    (h : stepConsume cfg = some next) :
    (∃ ex, next.branch.trail = canonicalTrail cfg.orig f ++ ex ∧
      ∀ e ∈ ex, e.level = f.level) ∧
      next.branch.level = f.level ∧ next.pending = rest ∧
      next.branch.learned = cfg.branch.learned := by
  have hbranch := stepConsume_branch_of_no_checkpoint hp hcp h
  obtain ⟨-, hpend, -, hlearn, -⟩ := stepConsume_some_shape hp h
  refine ⟨?_, ?_, hpend, hlearn⟩
  · rw [hbranch]
    exact resumePending_trail cfg.orig cfg.branch f
  · rw [hbranch]
    exact resumePending_level cfg.orig cfg.branch f

/-- COVERAGE OF THE CONSUME STEP AT THE ACTUAL PREDECESSOR: every leaf
solution enumerated by the old work list (`branch.frame :: f :: rest`) is
enumerated by the successor's work list, or excluded by a registered region
(sound log) or by the carried database. The only premise is the site's head
deadness justification for the failed frame; the resumed sibling is not
discarded, so no premise about it is needed. -/
theorem stepConsume_coverage {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      (∃ r ∈ cfg.log.regions, r.mem a = true) ∨
      (∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a)) :
    ∀ a, leaf a = true → FrontierCovers cfg.frontier a →
      FrontierCovers next.frontier a ∨
      (∃ r ∈ next.log.regions, r.mem a = true) ∨
      (∃ c ∈ next.branch.learned, ¬ c.SatisfiedBy a) := by
  obtain ⟨hf, hpend, hlog, hlearn, -⟩ := stepConsume_some_shape hp h
  intro a ha hfron
  have hfron' : FrontierCovers (cfg.branch.frame :: f :: rest) a := by
    have := hfron
    unfold SchedulerConfig.frontier at this
    rw [hp] at this
    exact this
  rcases fallback_retains_consume (leaf := leaf) hdead a ha hfron' with
    hrest | hreg | hcl
  · refine Or.inl ?_
    show FrontierCovers (next.branch.frame :: next.pending) a
    rw [hf, hpend]
    exact hrest
  · exact Or.inr (Or.inl (by rw [hlog]; exact hreg))
  · exact Or.inr (Or.inr (by rw [hlearn]; exact hcl))

/-- The `ClassificationSound` form of the same export, against the
predecessor's work list. -/
theorem stepConsume_classificationSound {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      (∃ r ∈ cfg.log.regions, r.mem a = true) ∨
      (∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a)) :
    ClassificationSound (leaf := leaf) (cfg.branch.frame :: f :: rest)
      next.frontier next.log next.branch.learned := by
  obtain ⟨hf, hpend, hlog, hlearn, -⟩ := stepConsume_some_shape hp h
  show ClassificationSound (leaf := leaf) (cfg.branch.frame :: f :: rest)
    (next.branch.frame :: next.pending) next.log next.branch.learned
  rw [hf, hpend, hlog, hlearn]
  exact classificationSound_consume hdead

/-! ### Coherence of the repaired resume from the actual predecessor -/

/-- The retirement entries `resumeSibling` appends for a saved frame: the
negation of the dropped head value's pin at the sibling's level (`[]` when
the frame's first remaining slot is empty or the lookup fails). -/
def resumedRetired (f : BranchFrame) (k : Nat) (v : Value) :
    List TrailEntry :=
  (retiredEntryAt f.level k v).toList

/-- `resumeSibling`'s trail is the level-restored history followed by
`resumedRetired` (definitional restatement with the named list). -/
theorem resumeSibling_trail_retired (bs : BranchState leaf) (f : BranchFrame)
    (k : Nat) (v : Value) :
    (resumeSibling bs f k v).trail =
      (bs.restoreLevel f.level).trail ++ resumedRetired f k v := rfl

/-- Every retirement entry sits at the sibling's level. -/
theorem resumedRetired_levels {f : BranchFrame} {k : Nat} {v : Value}
    {e : TrailEntry} (he : e ∈ resumedRetired f k v) :
    f.level ≤ e.level := by
  unfold resumedRetired at he
  cases hv : valueLiteral k v with
  | none => simp [retiredEntryAt, hv, Option.toList] at he
  | some l =>
      have he' : e = { literal := l.negate.norm, level := f.level,
                       reason := none } := by
        simpa [retiredEntryAt, hv, Option.toList] using he
      rw [he']
      exact Nat.le_refl _

/-- TRAIL CONJUNCT of `ResumeCoherent` from the actual predecessor: if the
checkpoint identifies the branch at the sibling's level (`Identifies` gives
`cp.trail ++ mid`) and the checkpoint trail lies at or below its own level,
then the repaired resume's trail is exactly the checkpoint trail followed by
entries at or above the sibling's level (the restored history plus the
retirement). -/
theorem resumeSibling_trail_coherent {bs : BranchState leaf} {f : BranchFrame}
    {k : Nat} {v : Value} {cp : DecisionCheckpoint leaf} {mid : List TrailEntry}
    (hident : bs.trail = cp.trail ++ mid)
    (hmid : ∀ e ∈ mid, f.level ≤ e.level)
    (hlev : cp.trail.filter (fun e => e.level ≤ f.level) = cp.trail) :
    ∃ extra : List TrailEntry,
      (resumeSibling bs f k v).trail = cp.trail ++ extra ∧
        ∀ e ∈ extra, f.level ≤ e.level := by
  refine ⟨mid.filter (fun e => e.level ≤ f.level) ++ resumedRetired f k v,
    ?_, ?_⟩
  · rw [resumeSibling_trail_retired]
    have hrestore : (bs.restoreLevel f.level).trail =
        bs.trail.filter (fun e => e.level ≤ f.level) := rfl
    rw [hrestore, hident, List.filter_append, hlev]
    exact List.append_assoc _ _ _
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmid e (List.mem_filter.mp he).1
    · exact resumedRetired_levels he

/-! ### The retired checkpoint route (R2 repair)

The checkpoint-consulting resume is GONE from the runtime (see
`stepConsume`'s docstring): a genuine reachable run refutes it
(`resumeSibling_shadow_not_represents`, `Proofs/PendingRun.lean` §4 — a
re-ascent pushes a newer same-level checkpoint, so `checkpointAt` can
return a foreign ancestor whose frame supplies the WRONG retired value,
and the resumed trail then falsifies a value of its own frame). The
former consume-level coherence exports (`stepConsume_head_falsifier`,
`stepConsume_resumeCoherent`) are therefore RETIRED with the route; their
canonical-route content is subsumed by `resumePending_reachable`
(`NarrowingComplete` falsifiers for every dropped original value,
`Proofs/PendingBacked.lean`). The `resumeSibling_*` algebra above remains
as the retained record of the retired route. -/

/-! ### The missing-checkpoint residual (S2 priority 2) -/

/-- The failed-child configuration with NO saved checkpoint at the sibling's
level: the missing-checkpoint route (`restoreLevel` alone) runs, and the
retirement cannot be recovered (no ancestor frame exists). -/
def missingCheckpointConfig (leaf : Assignment → Bool) : SchedulerConfig leaf where
  orig := [Dom.ofList [Value.int 1, Value.int 2]]
  original := []
  props := []
  branch :=
    { frame := ⟨[Dom.ofList [Value.int 1]], [0]⟩
      trail := [{ literal := negNe 0 1, level := 1, reason := none }]
      level := 1
      learned := [] }
  checkpoints := []
  pending := [⟨[Dom.ofList [Value.int 2]], []⟩]
  log := {}

/-- The missing-checkpoint route's successor at that configuration (R1
REPAIR): the branch is the CANONICAL resume of the pending frame —
the trail is reconstructed from the frame and the box (`resumePending` /
`canonicalTrail`), so the dropped head value's retirement is no longer
lost. The old `restoreLevel`-only successor (`trail := []`) is what
`stepConsume_resumes_without_retirement` refutes as incoherent. -/
theorem missingCheckpointConfig_stepConsume :
    stepConsume (missingCheckpointConfig leaf) =
      some { (missingCheckpointConfig leaf) with
             branch := resumePending (missingCheckpointConfig leaf).orig
               (missingCheckpointConfig leaf).branch (⟨[Dom.ofList [Value.int 2]], []⟩ : BranchFrame)
             pending := []
             status := .active
             conflict := none } := by
  unfold stepConsume missingCheckpointConfig
  rfl

/-- RESIDUAL (missing checkpoint, route-(a) predicate): at the concrete
configuration above, the OLD `restoreLevel`-only successor satisfies no
`ResumeCoherent`. The sibling retires the value `1` at slot 0 and the
level-filtered trail carries no falsifier for it — exactly the
counterexample `stepConsume_resumes_without_retirement`, now retired by
the canonical route (`missingCheckpointConfig_stepConsume` carries the
reconstructed trail instead). `ResumeCoherent` remains the route-(a)
(checkpoint-backed) predicate; the canonical route exports its coherence
separately (R1/R2). -/
theorem missing_checkpoint_resume_residual (leaf : Assignment → Bool) :
    ¬ ∃ cp : DecisionCheckpoint leaf,
      ResumeCoherent [Dom.ofList [Value.int 1, Value.int 2]]
        (⟨[Dom.ofList [Value.int 2]], []⟩ : BranchFrame) cp
        { frame := ⟨[Dom.ofList [Value.int 2]], []⟩, trail := [], level := 0,
          learned := [] } :=
  stepConsume_resumes_without_retirement leaf

/-- The dispatcher route for consume: `.chronologicalFallback` with the
resumed successor — never a verdict; `unsat` only when the pending stack is
empty (`consumeStep_unsat_iff`). -/
theorem consumeStep_route_chronologicalFallback {cfg next : SchedulerConfig leaf}
    (h : stepConsume cfg = some next) :
    consumeStep cfg = .chronologicalFallback next := by
  unfold consumeStep
  rw [h]

/-! ### Failed narrowed child vs live sibling (S2 priority 3) -/

/-- The computable frame region claims nothing outside the frame: an
assignment the frame does not cover has `mem = false`. Only the sound
direction (`DeadRegion.coversB_sound`) is needed, because `Bool` has two
values. -/
theorem byFrame_mem_false_of_not_covers {f : BranchFrame} {a : Assignment}
    (h : ¬ FrameCovers f a) : (DeadRegion.byFrame f).mem a = false := by
  cases hm : (DeadRegion.byFrame f).mem a with
  | false => rfl
  | true =>
      exact absurd
        (DeadRegion.coversB_sound (show DeadRegion.coversB f a = true from hm)) h

/-- RUNTIME-SITE EXCLUSION (S2 priority 3): a dead narrowed child's
registration region contains no sibling solution — the split covers every
parent assignment by the child or the sibling, and the child's region only
claims child-covered assignments. This is the registration-soundness
obligation at the concrete sites, not a retained-log membership statement. -/
theorem failed_child_region_spares_sibling {parent child sibling : BranchFrame}
    {a : Assignment}
    (hsplit : SplitCovers parent child sibling)
    (hpar : FrameCovers parent a)
    (hnotchild : ¬ FrameCovers child a) :
    (DeadRegion.byFrame child).mem a = false ∧ FrameCovers sibling a :=
  ⟨byFrame_mem_false_of_not_covers hnotchild,
    (hsplit a hpar).resolve_left hnotchild⟩

/-- The `localExclude` registration leaves the work list untouched (only
log, status and database change): the failed child's exclusion cannot
discard a pending sibling. -/
theorem stepLocalExclude_frontier (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).frontier = cfg.frontier := rfl

/-- RUNTIME SITE (S2 priority 3): registering the dead child's region in
`localExclude` (a) contains no sibling solution (`mem = false`) and (b)
keeps the sibling on the work list — the failed narrowed child discards
neither the live sibling nor the parent prefix it still covers. -/
theorem stepLocalExclude_spares_sibling {cfg : SchedulerConfig leaf}
    {learned : List Clause} {parent f : BranchFrame} {rest : List BranchFrame}
    {a : Assignment}
    (hp : cfg.pending = f :: rest)
    (hsplit : SplitCovers parent cfg.branch.frame f)
    (hpar : FrameCovers parent a)
    (hnotchild : ¬ FrameCovers cfg.branch.frame a) :
    (branchRegion cfg).mem a = false ∧
      FrontierCovers (stepLocalExclude cfg learned (branchRegion cfg)).frontier a := by
  obtain ⟨hmem, hf⟩ := failed_child_region_spares_sibling hsplit hpar hnotchild
  refine ⟨?_, ?_⟩
  · simpa only [branchRegion] using hmem
  · refine ⟨f, ?_, hf⟩
    rw [stepLocalExclude_frontier]
    show f ∈ cfg.branch.frame :: cfg.pending
    rw [hp]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- HEAD DEADNESS REGISTRATION (S2 priority 1a): the deadness evidence of
the actual predecessor frame registers a SOUND computable region and
preserves `ExhaustionLog.Sound` — the justification the consume coverage
consumes, derived from the site evidence and `DeadRegion.byFrame_sound`,
never from retained-log membership. -/
theorem branchRegion_registration_sound {cfg : SchedulerConfig leaf}
    {learned : List Clause}
    (hsound : ExhaustionLog.Sound leaf cfg.log)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    DeadRegion.Sound leaf (branchRegion cfg) ∧
      ExhaustionLog.Sound leaf
        (stepLocalExclude cfg learned (branchRegion cfg)).log := by
  have hr : DeadRegion.Sound leaf (branchRegion cfg) := by
    simpa only [branchRegion] using DeadRegion.byFrame_sound hdead
  exact ⟨hr, ExhaustionLog.register_sound hsound hr⟩

end LeanFzn.Solver.UIP
