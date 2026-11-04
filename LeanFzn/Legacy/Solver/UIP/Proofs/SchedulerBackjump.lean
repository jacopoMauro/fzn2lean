/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerBackjump.lean

Purpose:
  Checkpoint SELECTION identity and the learn/backjump/assert preservation
  of the C2c-owned fields of `SchedulerInvariant` — `reachable`,
  `checkpoints_identify`, `log_sound`, `coverage` — plus the proved
  fallback/exclusion routes for a missing checkpoint and a rejected
  assertion (never `unsat`).

  * SELECTION (PLAN C2c (a)): `checkpointAt_identifies` — the checkpoint
    the runtime lookup returns identifies the ACTUAL ancestor at the
    requested level (`Identifies` at `target`, not at a caller-supplied
    level); `selected_plan_identifies` — the plan built from it carries
    `BackjumpPlan.Identifies`, so no caller assumes the checkpoint level
    (`ofCheckpoint_identifies` discharges it from the record).
    `checkpointAt_eq_none_of_ne` — a `none` lookup PROVES no saved
    ancestor sits at that level: the fallback trigger, not an assumption.

  * RESTORATION CERTIFICATE APPLIED (PLAN C2c (b)): the L1/L2/L4/L5
    fields of `stepLearnBackjumpAssert` are definitional (`_orig`,
    `_pending`, `_status`, `_log`, `_learned`); the runtime checkpoint
    filter keeps exactly the levels `≤ target` (`_checkpoints_below`,
    `_checkpoints_subset`); E3's recorded certificate supplies the plan
    activity; E1's restoration lemmas supply the database entailment
    (`hmono`, a NAMED PREMISE below — see the report).

  * INVARIANT PRESERVATION (PLAN C2c (c)): `coverage_of_backjumpCovers`
    is the conservation theorem — old frontier coverage + the transition's
    `BackjumpCovers` obligation + database monotonicity yield the new
    coverage; `stepLearnBackjumpAssert_coverage` instantiates it, and
    `schedulerInvariant_after_backjump` assembles the full invariant from
    the seven field obligations (each named, none assumed by the
    transition definition). `coverage` is a GENUINE preservation, never a
    stability weakening.

  * FALLBACK / EXCLUSION (PLAN C2c (e)): `restoreNarrow_eq_none_of_filterFrame_none`
    and `perform_eq_none_of_restoreNarrow_eq_none` prove the rejected
    assertion yields NO jump result (so no jump verdict can be claimed);
    `assertion_reject_routes_local` pairs that with C2b's PROVED
    frame-region exclusion (`local_exclusion_ofFrame_sound`, consuming the
    repaired `DeadRegion.ofFrame`); `stepLocalExclude_log_sound` /
    `stepChronologicalFallback_log_sound` preserve `log_sound` at the two
    registration sites. Neither transition emits a verdict — the dispatcher
    half (no `unsat` arm) is E3's `backjumpStep_ne_unsat`.

  * CONSUME (PLAN C2c (a) second half): `resumeSibling_resumeCoherent_falsifiers`
    consumes C2b's repaired `resumeSibling_retires` and derives the
    falsifier conjunct of `ResumeCoherent` for the retired sibling — the
    conjunct the frozen prefix-length `stepConsume` could not supply
    (`stepConsume_resumes_without_retirement`, cited, not re-proved).

Dependencies:
  - LeanFzn.Solver.UIP.Proofs.SchedulerResume (C2b: registration soundness,
    repaired forms)
  - LeanFzn.Solver.UIP.Proofs.SchedulerForward (C2a: `CheckpointsBelow` and the
    forward-preservation API this module mirrors)
  - LeanFzn.Solver.UIP.Proofs.BackjumpFrontier (C2c extension: `Identifies`
    composition under restoration), transitively `SchedulerInvariant`

DAG:
  SchedulerResume/SchedulerForward/BackjumpFrontier -> this module
  (leaf; consumed by C2d assembly; registered by the coordinator).

Named-owner premises carried by the INSTANCE theorems below (never by the
combinators):
  * `hmono` — the restored/learned database contains the pre-jump learned
    database. Owner: C2d/integration (E1's `learnedProvenance_restoreFrame`
    supplies it once `perform` is wired).
  * `hbc` — the transition's `BackjumpCovers` obligation. Owner:
    C2d/integration (needs `filterFrame` semantics + trail algebra of
    `perform`).
  * `hreach` — `ReachableState leaf orig restored`. Owner:
    C2d/integration (A1/A2 reachability of `perform`'s result).
  * `hident` — surviving-checkpoint identity for the restored branch.
    Owner: C2d/integration, using `DecisionCheckpoint.Identifies.restore_extend`
    (this module's extension) on each surviving checkpoint.
  * `hpend`/`hbfit`/`hlent` — the static provenance fields of the restored
    configuration; same owner.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerResume
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerForward
import LeanFzn.Legacy.Solver.UIP.Proofs.BackjumpFrontier
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Checkpoint selection identifies the actual ancestor -/

/-- SELECTION IDENTITY (PLAN C2c (a)): a checkpoint returned by the runtime
lookup identifies the ACTUAL ancestor at the requested level. No caller
assumption about the checkpoint exists beyond the invariant itself:
`hident` is exactly `SchedulerInvariant.checkpoints_identify`, and the
level comes from `checkpointAt_level`, not from a premise. -/
theorem checkpointAt_identifies {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {bs : BranchState leaf}
    {target : Nat} {cp : DecisionCheckpoint leaf}
    (hident : ∀ cp ∈ cps, cp.Identifies bs cp.level)
    (h : checkpointAt cps target = some cp) :
    cp.Identifies bs target := by
  have hlev : cp.level = target := checkpointAt_level h
  rw [← hlev]
  exact hident cp (checkpointAt_mem h)

/-- The selected checkpoint's level is a genuine ancestor level: with the
`CheckpointsBelow` law every saved checkpoint satisfies, the returned
checkpoint sits at or below the branch's level (so it cannot be a future
state). -/
theorem checkpointAt_level_le {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {target lvl : Nat}
    {cp : DecisionCheckpoint leaf}
    (hbelow : ∀ cp ∈ cps, cp.level ≤ lvl)
    (h : checkpointAt cps target = some cp) :
    cp.level ≤ lvl :=
  hbelow cp (checkpointAt_mem h)

/-- CHECKPOINT USABILITY UNDER THE R1 RETIREMENT: the checkpoint found by
`checkpointAt cps t` always SURVIVES the `(fun cp => cp.level ≤ t)` filter,
because its level equals `t` — so the R1 consume retirement keeps exactly
the resume-relevant checkpoints and drops only strictly deeper ones. -/
theorem checkpointAt_mem_filter_self {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {t : Nat}
    {cp : DecisionCheckpoint leaf} (h : checkpointAt cps t = some cp) :
    cp ∈ cps.filter (fun cp => cp.level ≤ t) := by
  refine List.mem_filter.mpr ⟨checkpointAt_mem h, ?_⟩
  simp only [decide_eq_true_eq, checkpointAt_level h]
  exact Nat.le_refl t

/-- MISSING CHECKPOINT IS PROVED, NOT ASSUMED: an empty lookup proves that
NO saved ancestor sits at the requested level. This is the exact
precondition of the `chronologicalFallback` route (PLAN C2c (e)); the
caller never assumes existence. -/
theorem checkpointAt_eq_none_of_ne {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {target : Nat}
    (h : ∀ cp ∈ cps, cp.level ≠ target) :
    checkpointAt cps target = none := by
  induction cps with
  | nil => rfl
  | cons cp' rest ih =>
      simp only [checkpointAt, List.find?_cons]
      split
      · rename_i hb
        exact absurd (beq_iff_eq.mp hb) (h cp' (List.mem_cons_self ..))
      · exact ih (fun cp hcp => h cp (List.mem_cons_of_mem _ hcp))

/-- THE PLAN BUILT FROM THE SELECTED CHECKPOINT IDENTIFIES THE BRANCH
(PLAN C2c (a), INTERFACES §2.4(a)): the level law of
`BackjumpPlan.Identifies` is discharged from the checkpoint record, so the
learn/backjump/assert transition never takes a caller premise
`p.checkpoint.level = p.target` — this is the removed assumption. -/
theorem selected_plan_identifies {leaf : Assignment → Bool}
    {cps : List (DecisionCheckpoint leaf)} {bs : BranchState leaf}
    {target : Nat} {cp : DecisionCheckpoint leaf} {l : Literal} {c : Clause}
    (hident : ∀ cp ∈ cps, cp.Identifies bs cp.level)
    (h : checkpointAt cps target = some cp) :
    (BackjumpPlan.ofCheckpoint cp bs l c).Identifies bs := by
  refine BackjumpPlan.ofCheckpoint_identifies ?_
  rw [checkpointAt_level h]
  exact checkpointAt_identifies hident h

/-! ## The learn/backjump/assert transition: definitional field shape -/

@[simp] theorem stepLearnBackjumpAssert_orig (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).orig = cfg.orig := rfl

@[simp] theorem stepLearnBackjumpAssert_pending (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).pending = cfg.pending := rfl

@[simp] theorem stepLearnBackjumpAssert_status (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).status = .active := rfl

/-- The jump REGISTERS NOTHING: the exhaustion log is untouched, so
`log_sound` is carried through unchanged (`stepLearnBackjumpAssert_log_sound`). -/
@[simp] theorem stepLearnBackjumpAssert_log (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).log = cfg.log := rfl

/-- The ENQUEUE: the new database is the conflict payload followed by the
restored database (the learned clause itself is inserted by
`BackjumpPlan.perform` inside `restored`). -/
@[simp] theorem stepLearnBackjumpAssert_learned (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).branch.learned
      = ev.learned ++ restored.learned := rfl

/-- `log_sound` PRESERVATION (C2c-owned invariant field): the jump makes no
registration, so a sound log stays sound. -/
theorem stepLearnBackjumpAssert_log_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hsound : ExhaustionLog.Sound leaf cfg.log) :
    ExhaustionLog.Sound leaf
      (stepLearnBackjumpAssert cfg p ev restored).log :=
  hsound

/-- THE RUNTIME FILTER DISCHARGES THE LEVEL LAW of every surviving
checkpoint: `cfg.checkpoints.filter fun cp => cp.level ≤ p.target`. -/
theorem stepLearnBackjumpAssert_checkpoints_below {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {cp : DecisionCheckpoint leaf}
    (h : cp ∈ (stepLearnBackjumpAssert cfg p ev restored).checkpoints) :
    cp.level ≤ p.target := by
  have hmem : cp ∈ cfg.checkpoints.filter (fun cp => cp.level ≤ p.target) := by
    simpa only [stepLearnBackjumpAssert_checkpoints] using h
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- Survivors are saved ancestors: the filter only removes checkpoints, so
every survivor is a member of the pre-jump list (the provenance half of
`checkpoints_identify` after the jump). -/
theorem stepLearnBackjumpAssert_checkpoints_subset {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {cp : DecisionCheckpoint leaf}
    (h : cp ∈ (stepLearnBackjumpAssert cfg p ev restored).checkpoints) :
    cp ∈ cfg.checkpoints := by
  have hmem : cp ∈ cfg.checkpoints.filter (fun cp => cp.level ≤ p.target) := by
    simpa only [stepLearnBackjumpAssert_checkpoints] using h
  exact (List.mem_filter.mp hmem).1

/-- `learnBackjumpAssert` preserves the checkpoint-level discipline: the
runtime filter keeps exactly the checkpoints at or below `p.target`, which
IS the restored branch's level (`restored.level = p.target`). -/
theorem checkpointsBelow_learnBackjumpAssert {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (h : CheckpointsBelow cfg) (hlv : restored.level = p.target) :
    CheckpointsBelow (stepLearnBackjumpAssert cfg p ev restored) := by
  intro cp hmem
  rw [stepLearnBackjumpAssert_level _ _ _ _ hlv]
  exact stepLearnBackjumpAssert_checkpoints_below hmem

/-! ## Coverage conservation (the C2c-owned `coverage` field) -/

/-- COVERAGE CONSERVATION (the core combinator): if the old frontier covers
every remaining leaf solution, and a transition maps old-covered solutions
to new-covered solutions or to a clause in the (monotone) new database,
then the new frontier covers every remaining leaf solution. This is a
GENUINE conservation, not a stability weakening: no solution leaves the
frontier except through clause exclusion. -/
theorem coversRemainingLeaves_of_step {leaf : Assignment → Bool}
    {orig : List Domain} {pending pending' : List BranchFrame}
    {db db' : List Clause}
    (hcov : CoversRemainingLeaves leaf orig pending db)
    (hstep : ∀ a, OriginalLeaves leaf orig a → FrontierCovers pending a →
      FrontierCovers pending' a ∨ ∃ c ∈ db', ¬ c.SatisfiedBy a)
    (hmono : ∀ c ∈ db, c ∈ db') :
    CoversRemainingLeaves leaf orig pending' db' := by
  intro a ha
  rcases hcov a ha with h | ⟨c, hc, hcs⟩
  · exact hstep a ha h
  · exact Or.inr ⟨c, hmono c hc, hcs⟩

/-- `SchedulerConfig.coverage` after a backjump: E3's `BackjumpCovers`
obligation plus database monotonicity (E1's restoration discipline)
conserve coverage. `orig` is fixed by the runtime transition (`rfl`). -/
theorem coverage_of_backjumpCovers {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf}
    (hcov : cfg.coverage)
    (hbc : BackjumpCovers leaf cfg.orig cfg next)
    (hmono : ∀ c ∈ cfg.branch.learned, c ∈ next.branch.learned)
    (hnextorig : next.orig = cfg.orig) :
    next.coverage := by
  intro a ha
  have ha' : OriginalLeaves leaf cfg.orig a := by
    unfold OriginalLeaves at ha
    rw [hnextorig] at ha
    exact ha
  rcases hcov a ha' with h | ⟨c, hc, hcs⟩
  · exact hbc a ha' h
  · exact Or.inr ⟨c, hmono c hc, hcs⟩

/-- The instance at the real `learnBackjumpAssert` transition. The two
premises are NAMED (`hbc`: the transition's coverage obligation, owner
C2d/integration; `hmono`: database monotonicity through restoration, owner
C2d/integration via E1); the `orig` law is definitional. -/
theorem stepLearnBackjumpAssert_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hcov : cfg.coverage)
    (hbc : BackjumpCovers leaf cfg.orig cfg
      (stepLearnBackjumpAssert cfg p ev restored))
    (hmono : ∀ c ∈ cfg.branch.learned,
      c ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned) :
    (stepLearnBackjumpAssert cfg p ev restored).coverage :=
  coverage_of_backjumpCovers hcov hbc hmono rfl

/-! ## Invariant assembly for the backjump family -/

/-- ASSEMBLY (PLAN C2c (c)): the seven field obligations of
`SchedulerInvariant` at a jump successor, each supplied by the task that
owns it (see the module header for the named owners). The transition
definition itself carries no preservation field: this theorem consumes
only proved field obligations. -/
theorem schedulerInvariant_after_backjump {leaf : Assignment → Bool}
    {next : SchedulerConfig leaf}
    (hreach : ReachableState leaf next.orig next.branch)
    (hident : ∀ cp ∈ next.checkpoints, cp.Identifies next.branch cp.level)
    (hpend : ∀ f ∈ next.pending, ∀ i v,
      v ∈ (Frame.domains f).getD i Dom.empty → v ∈ next.orig.getD i Dom.empty)
    (hbfit : ∀ i v, v ∈ (Frame.domains next.branch.frame).getD i Dom.empty →
      v ∈ next.orig.getD i Dom.empty)
    (hlog : ExhaustionLog.Sound leaf next.log)
    (hcov : next.coverage)
    (hlent : ∀ c ∈ next.branch.learned, LearnedEntailed leaf [c]) :
    SchedulerInvariant next :=
  ⟨hreach, hident, hpend, hbfit, hlog, hcov, hlent⟩

/-! ## Proved fallback / exclusion routes (never `unsat`) -/

/-- A rejected assertion filter yields NO restored state — the jump
transition produces no result, so no jump verdict can be claimed for it. -/
theorem restoreNarrow_eq_none_of_filterFrame_none {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    (h : filterFrame p.asserting p.checkpoint.frame = none) :
    p.restoreNarrow bs = none := by
  unfold BackjumpPlan.restoreNarrow
  rw [h]

/-- Consequently the complete transition is `none`: the rejected assertion
routes AWAY from the jump (PLAN C2c (e)), never to a verdict. -/
theorem perform_eq_none_of_restoreNarrow_eq_none {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    (h : p.restoreNarrow bs = none) :
    p.perform bs orig original props = none := by
  unfold BackjumpPlan.perform
  rw [h]
  rfl

/-- ASSERTION-FILTER FAILURE ROUTES TO PROVED EXCLUSION: the transition has
no result AND the checkpoint frame's exact region — C2b's repaired
`DeadRegion.ofFrame`, not the unsound prefix region
(`narrowed_prefix_region_not_sound`, cited) — is a sound exclusion whenever
the frame is dead. This is the registration obligation of the
`localExclude`/`chronologicalFallback` arm for the rejected assertion. -/
theorem assertion_reject_routes_local {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    (h : p.restoreNarrow bs = none)
    (hdead : ∀ a, leaf a = true → FrameCovers p.checkpoint.frame a → False) :
    p.perform bs orig original props = none ∧
      DeadRegion.Sound leaf (DeadRegion.ofFrame p.checkpoint.frame) :=
  ⟨perform_eq_none_of_restoreNarrow_eq_none h,
    local_exclusion_ofFrame_sound (f := p.checkpoint.frame) hdead⟩

/-- `log_sound` at the `localExclude` registration site: registering a
sound region preserves the C2c-owned `log_sound` field. -/
theorem stepLocalExclude_log_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (hsound : ExhaustionLog.Sound leaf cfg.log)
    (hdead : DeadRegion.Sound leaf r) :
    ExhaustionLog.Sound leaf (stepLocalExclude cfg learned r).log :=
  ExhaustionLog.register_sound hsound hdead

/-- The same at the `chronologicalFallback` registration site (the route a
missing checkpoint takes: `checkpointAt_eq_none_of_ne`). -/
theorem stepChronologicalFallback_log_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (hsound : ExhaustionLog.Sound leaf cfg.log)
    (hdead : DeadRegion.Sound leaf r) :
    ExhaustionLog.Sound leaf (stepChronologicalFallback cfg r).log :=
  ExhaustionLog.register_sound hsound hdead

/-- The branch-frame instance of the exclusion route: a dead current branch
registers its OWN frame's region soundly. -/
theorem branch_frame_region_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    DeadRegion.Sound leaf (DeadRegion.ofFrame cfg.branch.frame) :=
  local_exclusion_ofFrame_sound hdead

/-! ## The repaired consume: coherence for the retired sibling

C2b PROVED that the prefix-length `stepConsume` resume is unsound for
narrowed frames: `stepConsume_resumes_without_retirement` (cited, not
re-proved here) exhibits the failed-child/live-sibling configuration whose
resumed trail carries no falsifier, so no checkpoint makes it
`ResumeCoherent`. The repair is `resumeSibling`, whose correctness theorem
`resumeSibling_retires` this section consumes to derive the falsifier
conjunct of `ResumeCoherent` — the half the frozen form cannot supply. -/

/-- REPAIRED-RESUME COHERENCE: given the split equations (`cp`'s frame heads
its first remaining slot with `v`, the sibling `f` keeps the tail `rest`),
the sibling's head-slot retirement is supplied by
`resumeSibling_retires`, and deeper-slot falsifiers are supplied by the
tail hypothesis (narrowings below the split slot, which the retirement
mechanism does not touch — the same shape the parent's `ResumeCoherent`
had). -/
theorem resumeSibling_resumeCoherent_falsifiers {leaf : Assignment → Bool}
    {bs : BranchState leaf} {f : BranchFrame} {k : Nat} {v : Value}
    {vs : Domain} {l : Literal} {orig : List Domain}
    (hkv : f.doms[k]? = some vs)
    (hdom : Dom.enum (orig.getD k Dom.empty) = v :: vs.enum)
    (hv : valueLiteral k v = some l)
    (hfresh : k ∉ f.order)
    (htail : ∀ j ∉ f.order, j ≠ k → ∀ w, w ∈ orig.getD j Dom.empty →
      w ∉ f.doms.getD j Dom.empty →
      ∃ e ∈ (resumeSibling bs f k v).trail,
        e.literal.atom.slot = j ∧ e.literal.valueHolds w = false) :
    ∀ j ∉ f.order, ∀ w, w ∈ orig.getD j Dom.empty → w ∉ f.doms.getD j Dom.empty →
      ∃ e ∈ (resumeSibling bs f k v).trail,
        e.literal.atom.slot = j ∧ e.literal.valueHolds w = false := by
  intro j hj w hw hnot
  by_cases hjk : j = k
  · rw [hjk] at hw hnot ⊢
    have hwv : w = v := by
      have hwE : w ∈ Dom.enum (orig.getD k Dom.empty) := by
        simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw
      rw [hdom] at hwE
      rcases List.mem_cons.mp hwE with h | h
      · exact h
      · exfalso
        apply hnot
        rw [List.getD_eq_getElem?_getD, hkv, Option.getD_some]
        exact (DomainLike.mem_iff _ _).mpr (by simpa [domElems_eq_enum] using h)
    subst hwv
    exact resumeSibling_retires hv
  · exact htail j hj hjk w hw hnot

/-! ## S3 — the ACTUAL `perform` result: shape, trail algebra, reachability

These exports derive the successor's static facts from the real runtime
equations, not from caller-supplied conclusions:

* `restoreNarrow_eq_some_iff` / `perform_eq_some_iff`: the exact shape of
  a performed plan — the assertion filter's frame `g`, the executed
  restore-and-enqueue, and the RESUMED CLOSURE
  `explainedClosure original props ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)`.
  The `learned` insertion (`bs.learnGlobal p.learned`) and the asserting
  entry are inside `execute`/`restoreNarrow`, so `hlent`/frame facts never
  need a redeclaration of the transition.
* `perform_trail_extends`: the successor's trail extends the executed
  trail by target-level entries only (`explainedClosure_trail_extends`,
  `Proofs/BackjumpFrontier.lean`), which is the trail algebra `hident`'s
  residual consumes.
* `perform_reachable_of_pre`: reachability of the ACTUAL result, consuming
  A2's `explainedClosure_reachable` under the closure contract — no
  successor `hreach` is assumed; the sole residual is named by
  `RestorationPreReachable` (owner S5: the selected checkpoint must be a
  reachable snapshot of `orig` and the assertion filter must narrow it;
  the filtering/enqueue algebra is the checkpoint-snapshot invariant,
  maintained at the push sites by S1/S2/S4).
* `jump_learned_entailed`: the successor database's entailment — the
  closure payload half is the named premise owned by S4/D0
  (`ClosureContract.conflictEntailed`), the restored half comes from the
  closure's own `ReachableState.wf`, never from a fresh assumption. -/

/-- A performed restore-and-narrow is exactly: some assertion-filtered
frame `g` of the checkpoint (`filterFrame` returning `some` — a `none`
result is the rejected-assertion route, not a jump), with the learned
clause inserted into the database (`learnGlobal`), the checkpoint + single
asserting entry restored (`execute`), and the frame narrowed (`narrowFrame`). -/
theorem restoreNarrow_eq_some_iff {p : BackjumpPlan leaf}
    {bs s : BranchState leaf} :
    p.restoreNarrow bs = some s ↔
      ∃ g : BranchFrame, filterFrame p.asserting p.checkpoint.frame = some g ∧
        s = (p.execute (bs.learnGlobal p.learned)).narrowFrame g := by
  unfold BackjumpPlan.restoreNarrow
  cases hg : filterFrame p.asserting p.checkpoint.frame with
  | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨g, hg', -⟩
        cases hg'
  | some g =>
      constructor
      · intro h
        exact ⟨g, rfl, (Option.some.inj h).symm⟩
      · rintro ⟨g', hg', rfl⟩
        cases hg'
        rfl

/-- THE `perform` RESULT, EXACT: the complete transition's result is the
resumed (synchronised) closure of the frame/trail synchronisation (R1d
`syncAll`) of the restored-and-narrowed state. This is the equation
every successor-field derivation starts from (no field of the successor is
an assumption; each is computed from this shape). -/
theorem perform_eq_some_iff {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator} :
    p.perform bs orig original props = some s ↔
      ∃ g : BranchFrame, filterFrame p.asserting p.checkpoint.frame = some g ∧
        s = explainedClosure orig original props (syncAll orig
              ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)) := by
  unfold BackjumpPlan.perform
  constructor
  · intro h
    cases hr : p.restoreNarrow bs with
    | none =>
        rw [hr] at h
        cases h
    | some t =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨g, hg, hgt⟩ := restoreNarrow_eq_some_iff.mp hr
        exact ⟨g, hg, by rw [← h, hgt]⟩
  · rintro ⟨g, hg, rfl⟩
    rw [restoreNarrow_eq_some_iff.mpr ⟨g, hg, rfl⟩]
    rfl

/-- TRAIL ALGEBRA OF THE SUCCESSOR: the performed plan's trail extends the
executed trail by entries at the plan's target level only. No entry below
the target is added, so every restored checkpoint prefix survives. -/
theorem perform_trail_extends {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    ∃ extra : List TrailEntry,
      s.trail = (p.execute (bs.learnGlobal p.learned)).trail ++ extra ∧
        ∀ e ∈ extra, e.level = p.target := by
  obtain ⟨g, hg, rfl⟩ := perform_eq_some_iff.mp h
  obtain ⟨ex1, hex1, hlev1⟩ := syncAll_trail_shape orig
    ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)
  obtain ⟨extra, hextra, hlev⟩ :=
    explainedClosure_trail_extends orig original props
      (syncAll orig ((p.execute (bs.learnGlobal p.learned)).narrowFrame g))
  refine ⟨ex1 ++ extra, ?_, ?_⟩
  · rw [hextra, hex1, List.append_assoc]
    rfl
  · intro e he
    rcases List.mem_append.mp he with he | he
    · rw [hlev1 e he]
      rfl
    · rw [hlev e he, syncAll_level]
      rfl

/-- TRAIL PREFIX OF THE SELECTED CHECKPOINT: the performed plan's trail
extends the SELECTED checkpoint's saved trail by entries at target level or
above (the asserting entry plus the closure's narrowing entries) — the
prefix conjunct of `Identifies` at `target := p.target`. -/
theorem perform_trail_prefix_checkpoint {p : BackjumpPlan leaf}
    {bs s : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    ∃ extra : List TrailEntry,
      s.trail = p.checkpoint.trail ++ extra ∧ ∀ e ∈ extra, p.target ≤ e.level := by
  obtain ⟨extra, hextra, hlev⟩ := perform_trail_extends h
  refine ⟨p.assertExtra ++ extra, ?_, ?_⟩
  · rw [hextra, BackjumpPlan.execute_trail, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · rw [BackjumpPlan.assertExtra_mem p he]
      exact Nat.le_refl _
    · exact Nat.le_of_eq (hlev e he).symm

/-- FRAME DESCENT OF THE PERFORMED PLAN: the successor's frame descends
from the selected checkpoint's frame — `execute` restores it, the
assertion filters it, and the closure only narrows further. -/
theorem perform_frame_descends {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    FrameDescendsFrom s.frame p.checkpoint.frame := by
  obtain ⟨g, hg, rfl⟩ := perform_eq_some_iff.mp h
  have hmid : FrameDescendsFrom
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).frame
      p.checkpoint.frame :=
    fun a hc =>
      FrameCovers_of_subsets (filterFrame_rem_length hg) (filterFrame_subsets hg)
        (by simpa only [BranchState.narrowFrame] using hc)
  refine FrameDescendsFrom.trans
    (explainedClosure_frame_descends orig original props
      (syncAll orig ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)))
    ?_
  rw [syncAll_frame]
  exact hmid

/-- **THE `hident` ENGINE**: every surviving checkpoint of the jump
successor identifies the successor branch at its own level — from the
checkpoint chain, the selected checkpoint, and the actual `perform`
result. No gate is consumed (this is why the joint producer is
non-circular): the level bound is the runtime filter, the trail witness is
`perform_trail_prefix_checkpoint` composed with the chain's pairwise
prefix, and the frame descent is `perform_frame_descends` composed with
the chain's descent. -/
theorem stepLearnBackjumpAssert_hident_of_chain {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp cp' : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hchain : CpChain cfg.checkpoints)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hperform : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
        an.learned).perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hmem : cp' ∈ (stepLearnBackjumpAssert cfg
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
        ev restored).checkpoints) :
    cp'.Identifies (stepLearnBackjumpAssert cfg
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
        ev restored).branch cp'.level := by
  have hsub := stepLearnBackjumpAssert_checkpoints_subset hmem
  have hleq : cp'.level ≤ cp.level :=
    stepLearnBackjumpAssert_checkpoints_below hmem
  obtain ⟨-, ⟨mid, hmid, hmidlev⟩, hdesc⟩ :=
    CpChain.pair_of_checkpointAt hchain hcp hsub hleq
  obtain ⟨extra, hextra, hextralev⟩ := perform_trail_prefix_checkpoint hperform
  have hdesc' : FrameDescendsFrom restored.frame cp'.frame :=
    FrameDescendsFrom.trans (perform_frame_descends hperform) hdesc
  refine DecisionCheckpoint.identifies_of_parts rfl ⟨mid ++ extra, ?_, ?_⟩ hdesc'
  · show restored.trail = cp'.trail ++ (mid ++ extra)
    have hpt : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
        an.learned).checkpoint.trail = cp.trail := rfl
    rw [hextra, hpt, hmid, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmidlev e he
    · exact Nat.le_trans hleq (hextralev e he)

/-- REACHABILITY OF THE ACTUAL `perform` RESULT from the pre-closure
state: A2's `explainedClosure_reachable` under the closure contract. The
successor's `hreach` is DERIVED here; the pre-closure reachability is the
residual named below (owner S5), never a second assumed `hreach`.

UNIT DISCIPLINE (P1 round-2 repair): the closure is called with the
payload-maintenance field `hpay`, the predecessor database's unit
discipline `hu`, and the inserted plan clause's unit discipline `hplanU`
(the pre-closure state's learned database is `p.learned :: bs.learned`, so
`unitDB_append` composes the latter two). -/
theorem perform_reachable_of_narrowFrame {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hc : ClosureContract leaf orig original props)
    (hpay : UnitPayload original props)
    {p : BackjumpPlan leaf} {bs s : BranchState leaf} {g : BranchFrame}
    (hu : UnitDB bs.learned) (hplanU : UnitDB [p.learned])
    (hg : filterFrame p.asserting p.checkpoint.frame = some g)
    (hpre : ReachableState leaf orig
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g))
    (h : p.perform bs orig original props = some s) :
    ReachableState leaf orig s := by
  obtain ⟨g', hg', rfl⟩ := perform_eq_some_iff.mp h
  rw [hg] at hg'
  cases hg'
  have hu' : UnitDB
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g).learned := by
    show UnitDB (p.learned :: bs.learned)
    exact unitDB_append hplanU hu
  exact explainedClosure_reachable hc _ hpay (syncAll_reachable hpre hc.leafFits)
    (by rw [syncAll_learned]; exact hu')

/-- RESIDUAL (owner S5), stated rather than assumed: the executed-and-narrowed
pre-closure state is a reachable branch state. Its two ingredients are
(a) the SELECTED checkpoint is a reachable snapshot of `orig` — the
checkpoint-chain invariant maintained where checkpoints are pushed
(S1's decide, S2's consume/exclusion; `Identifies` alone is strictly
weaker, R1's F1 finding) — including the freshness of the asserting
enqueue for `ReachableState.distinct`, and (b) the assertion filter
narrows that state (`filterFrame`) exactly as the canonical
`explainedStep_narrow_reachable` proves for propagation narrowing. Once
this is supplied by its owner, `perform_reachable_of_pre` yields the
successor's `hreach` from the ACTUAL result. -/
def RestorationPreReachable (leaf : Assignment → Bool) (orig : List Domain)
    (p : BackjumpPlan leaf) (bs : BranchState leaf) : Prop :=
  ∃ g : BranchFrame, filterFrame p.asserting p.checkpoint.frame = some g ∧
    ReachableState leaf orig
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)

/-- SUCCESSOR `hreach` FROM THE ACTUAL RESULT: the residual above plus the
closure contract give `ReachableState` of `perform`'s result. Carries the
same unit-discipline triple as `perform_reachable_of_narrowFrame`. -/
theorem perform_reachable_of_pre {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hc : ClosureContract leaf orig original props)
    (hpay : UnitPayload original props)
    {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (hu : UnitDB bs.learned) (hplanU : UnitDB [p.learned])
    (hpre : RestorationPreReachable leaf orig p bs)
    (h : p.perform bs orig original props = some s) :
    ReachableState leaf orig s := by
  obtain ⟨g, hg, hgpre⟩ := hpre
  exact perform_reachable_of_narrowFrame hc hpay hu hplanU hg hgpre h

/-- The successor database's entailment from the two real sources: the
closure payload (owner S4/D0 via `ClosureContract.conflictEntailed`) and
the restored database, whose entailment is the closure result's own
coherence field (`ReachableState.wf`) — never a fresh assumption. -/
theorem jump_learned_entailed {orig : List Domain}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hent : LearnedEntailed leaf ev.learned)
    (hreach : ReachableState leaf orig restored) :
    ∀ c ∈ ev.learned ++ restored.learned, LearnedEntailed leaf [c] := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · intro c' hc' a hleaf
    have hcc : c' = c := by simpa using hc'
    rw [hcc]
    exact hent c hc a hleaf
  · obtain ⟨-, -, -, -, hlearn⟩ := hreach.wf
    intro c' hc' a hleaf
    have hcc : c' = c := by simpa using hc'
    rw [hcc]
    exact hlearn c hc a hleaf

end LeanFzn.Solver.UIP
