/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerArmsComplete.lean

Purpose: close the CHECKPOINT-CHAIN route to the last named jump-arm
residual (`RestorationPreReachable`, PLAN item 3), and record the exact
result of attempting it.

CONTENT.

  §1 `CheckpointSnapshot leaf orig cp` — the weakest snapshot form: SOME
     reachable state carries exactly the record's frame, trail and level.
     `ReachableCpSnapshots leaf orig cfg` — the checkpoint-chain
     invariant: every saved checkpoint of `cfg` is such a snapshot.
     This property is independent of `cfg.branch`, so it is preserved by
     EVERY transition that keeps a checkpoint SUBLIST (all arms except
     the decide push) — `ReachableCpSnapshots.of_sublist` proves that
     once and for all.

  §2 THE ASSEMBLED INDUCTION (`reachableCpSnapshots_of_step`): if every
     real dispatcher step either keeps a sublist or pushes one snapshot,
     then the checkpoint-chain invariant holds along every
     `SchedulerReachable` run (root `rootCheckpoint orig` is the snapshot
     of the root state). The only per-arm work left is the push site.

  §3 THE FINDING (historical, kernel-checked) AND ITS REPAIR (LANDED):
     `decide_push_not_snapshot` — the FORMER `stepDecide` push record
     (`{level := decided.level, frame := cfg.branch.frame, trail :=
     decided.trail}`) CANNOT be a reachable snapshot whenever the decision
     is a GENUINE branch (a frame-covered assignment falsifies the pin —
     the same witness `ReachableState.fresh_of_not_forced` consumes). The
     snapshot's `agrees` field would force the decision entry to hold at
     every assignment the parent frame covers, and the mixed record
     (parent frame + child trail) violates this at the covering witness.
     REPAIR LANDED (integration fix): the runtime now pushes
     `DecisionCheckpoint.ofBranch cfg.branch` (parent level/frame/trail) —
     `stepDecide_checkpoints_push_snapshot` discharges the push site of
     §2 from the parent's own reachability via
     `checkpointSnapshot_ofBranch`, and the record still `Identifies` the
     decided child at the parent level (trail prefix + frame descent +
     level law are the same three conjuncts,
     `stepDecide_checkpoints_identify` in `Proofs.SchedulerForward`).

  §4 THE CONSUMER INTERFACE (J1 round 2, SUCCESS-GUARDED):
     `RestorationStepPreserves leaf`. The former unguarded form quantified
     over rejecting sites too, where `RestorationPreReachable` is false
     (its filter conjunct is the complement of `restoreNarrow = none`), so
     it was uninhabitable and had no producer. The gate now takes the
     ACTUAL successful runtime event (`perform = some restored`, the
     `.learnBackjumpAssert` arm's own equation) plus the per-site branch
     reachability. The rejection route stays with E1's
     `hdeadCheckpointRegion`.

  §5 THE FIELD DECOMPOSITION AND ITS PRODUCER (J1 round 2):
     `RestorationStepObligations` factors the gate into the eight
     `ReachableState` fields plus the jump guard, and the producer
     `restorationObligations_of_snapshot` DERIVES them from the snapshot
     record and the named site obligations: the analyzer certificate
     (`RestorationCertificate.learnedEntailed`/`assertingMem` via
     `asserting_norm_mem_of_stable`, chronology via `othersBelow` +
     `restore_chronology_of_certificate`), the surviving prefix (`hsurv`),
     the enqueue absence check (`hfresh` — not derivable from the
     certificate, whose `assertingSurvives` speaks about the NEGATION),
     normalization stability (`hstable`/`hneg`) and the asserting
     literal's in-range discipline (`hrange`). `restorationPreReachable_of_success`
     then extracts the filter witness from the real `perform` equation, and
     `restorationStepPreserves_of_site` PROVES `RestorationStepPreserves`
     from the raw push bundle plus the site obligations — no instance of
     the conclusion is assumed anywhere.

NO `sorry`, NO custom axiom.

DAG: Proofs.SchedulerArmsPreserve -> this module (leaf).
Registration: umbrella import `LeanFzn.Solver.UIP.Proofs.SchedulerArmsComplete`.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The checkpoint-chain invariant -/

/-- A checkpoint record is a REACHABLE SNAPSHOT of `orig`: some reachable
branch state carries exactly the record's frame, trail and level. (This is
the exact extra content `Identifies` + branch reachability fail to
supply for the restoration: the carry is a property of the RECORD.) -/
def CheckpointSnapshot (leaf : Assignment → Bool) (orig : List Domain)
    (cp : DecisionCheckpoint leaf) : Prop :=
  ∃ bs : BranchState leaf, ReachableState leaf orig bs ∧
    bs.frame = cp.frame ∧ bs.trail = cp.trail ∧ bs.level = cp.level

/-- The checkpoint-chain invariant: every saved checkpoint of `cfg` is a
reachable snapshot of `cfg`'s own original box. -/
def ReachableCpSnapshots (leaf : Assignment → Bool) (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Prop :=
  ∀ cp ∈ cfg.checkpoints, CheckpointSnapshot leaf orig cp

/-- The state's OWN checkpoint (`ofBranch`) is a snapshot of itself — the
repaired push site's obligation is definitional from the branch's
reachability. -/
theorem checkpointSnapshot_ofBranch {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) :
    CheckpointSnapshot leaf orig (DecisionCheckpoint.ofBranch bs) :=
  ⟨bs, h, rfl, rfl, rfl⟩

/-- MONOTONICITY: checkpoint snapshots survive every checkpoint-subset
transition (all dispatcher arms except the decide push; the jump's filter
is the only other checkpoint-changing site). -/
theorem ReachableCpSnapshots.of_sublist {leaf : Assignment → Bool}
    {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (h : ReachableCpSnapshots leaf orig cfg)
    (hsub : List.Sublist cfg'.checkpoints cfg.checkpoints) :
    ReachableCpSnapshots leaf orig cfg' :=
  fun cp hcp => h cp (hsub.subset hcp)

/-- The ROOT is a snapshot chain: `SchedulerConfig.init` registers exactly
the root checkpoint, which carries the root state's frame/trail/level. -/
theorem reachableCpSnapshots_init {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    ReachableCpSnapshots leaf orig
      (SchedulerConfig.init (leaf := leaf) orig original props) := by
  intro cp hcp
  simp only [SchedulerConfig.init, List.mem_singleton] at hcp
  subst hcp
  exact checkpointSnapshot_ofBranch (reachable_init leaf orig)

/-- The jump arm's checkpoint FILTER keeps a sublist: the only
checkpoint-changing non-push site is discharged for free. -/
theorem checkpoints_sublist_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf) :
    List.Sublist (stepLearnBackjumpAssert cfg p ev restored).checkpoints
      cfg.checkpoints := by
  rw [stepLearnBackjumpAssert_checkpoints]
  exact List.filter_sublist

/-- **THE PUSH BUNDLE (reach-aware)**: every real dispatcher successor
either keeps a checkpoint sublist or pushes ONE reachable snapshot. The
decide (fresh) arm needs the pre-state branch reachability — the input the
run-wide joint inductions carry — so this is the honest variant of the
`hpush` premise the restoration producers consume. Every other arm is a
sublist via the landed filter/keep lemmas. -/
theorem checkpoints_push_or_sublist_of_successor {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hs : (schedulerNext cfg).successor = some cfg') :
    List.Sublist cfg'.checkpoints cfg.checkpoints ∨
      ∃ cp, cfg'.checkpoints = cp :: cfg.checkpoints ∧
        CheckpointSnapshot leaf cfg.orig cp := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (backjumpStep)
    rw [hnext] at hs
    unfold backjumpStep at hs
    cases ha : ev.analysis with
    | none =>
        rw [ha] at hs
        simp only [] at hs
        simp only [successor_chronologicalFallback, Option.some.injEq] at hs
        subst hs
        exact Or.inl (by simpa only [stepChronologicalFallback]
          using List.Sublist.refl cfg.checkpoints)
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            rw [hcp] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            exact Or.inl (by simpa only [stepChronologicalFallback]
              using List.Sublist.refl cfg.checkpoints)
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                rw [hp] at hs
                simp only [] at hs
                simp only [successor_localExclude, Option.some.injEq] at hs
                subst hs
                exact Or.inl (by simpa only [stepLocalExclude]
                  using List.Sublist.refl cfg.checkpoints)
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
                exact Or.inl (checkpoints_sublist_stepLearnBackjumpAssert cfg
                  (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned) ev restored)
  · -- ===== ROUTE 2: dead branch — the consume route
    rw [hnext] at hs
    unfold consumeStep at hs
    split at hs
    · rename_i next hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at hs
      subst hs
      cases hpend : cfg.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
          cases hcs
      | cons f rest => exact Or.inl (stepConsume_checkpoints_sublist hpend hcs)
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
      exact Or.inl (by simpa only [stepPropagate]
        using List.Sublist.refl cfg.checkpoints)
    · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
      rw [hnt] at hs
      unfold stableStepGuarded at hs
      split at hs
      · simp only [successor_sat] at hs
        cases hs
      · split at hs
        · rename_i l v vs doms hsp
          split at hs
          · -- SKIP arm
            simp only [successor_decide, Option.some.injEq] at hs
            subst hs
            exact Or.inl (by simpa only [stepDecideSkip]
              using List.Sublist.refl cfg.checkpoints)
          · -- FRESH arm: the push
            simp only [successor_decide, Option.some.injEq] at hs
            subst hs
            exact Or.inr ⟨DecisionCheckpoint.ofBranch cfg.branch, rfl,
              checkpointSnapshot_ofBranch hreach⟩
        · -- no split data: localExclude
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact Or.inl (by simpa only [stepLocalExclude]
            using List.Sublist.refl cfg.checkpoints)
    · -- ARM 8 / ARM 4: the conflict dispatch
      rw [hnt] at hs
      cases cs with
      | nil =>
          simp only [conflictStep] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact Or.inl (by simpa only [stepLocalExclude]
            using List.Sublist.refl cfg.checkpoints)
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
            cases hs
          · simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hs
            subst hs
            exact Or.inl (by simpa only [stepAnalyzeConflictCounted,
              stepAnalyzeConflict, SchedulerConfig.countResolutions]
                using List.Sublist.refl cfg.checkpoints)
    · -- ARM 6: localExcluded → localExclude
      rw [hnt] at hs
      simp only [successor_localExclude, Option.some.injEq] at hs
      subst hs
      exact Or.inl (by simpa only [stepLocalExclude]
        using List.Sublist.refl cfg.checkpoints)

/-! ## §2 The assembled induction -/

/-- **THE ASSEMBLED INDUCTION (checkpoint-chain route).** If every real
dispatcher step either keeps a checkpoint sublist or pushes one snapshot
(the push-site bundle), then `ReachableCpSnapshots` holds along every
`SchedulerReachable` run, at every configuration's OWN `orig` (transported
across each link by W1's `schedulerNext_succ_orig`). Every non-push arm's
discharge is `ReachableCpSnapshots.of_sublist` (or `rfl`); the decide push
is the only remaining per-arm obligation, and §3 shows it must be REPAIRED
to be inhabitable. -/
theorem reachableCpSnapshots_of_step {leaf : Assignment → Bool}
    (hstep : ∀ {cfg cfg' : SchedulerConfig leaf},
      SchedulerReachable cfg → (schedulerNext cfg).successor = some cfg' →
      List.Sublist cfg'.checkpoints cfg.checkpoints ∨
        ∃ cp, cfg'.checkpoints = cp :: cfg.checkpoints ∧
          CheckpointSnapshot leaf cfg.orig cp) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableCpSnapshots leaf cfg.orig cfg := by
  intro cfg h
  induction h with
  | init orig original props => exact reachableCpSnapshots_init orig original props
  | step hnext hsucc hr ih =>
      rcases hstep hr (hnext ▸ hsucc) with hsub | ⟨cp, hpush, hsnap⟩
      · rw [W1.schedulerNext_succ_orig (hnext ▸ hsucc)]
        exact ReachableCpSnapshots.of_sublist ih hsub
      · rw [W1.schedulerNext_succ_orig (hnext ▸ hsucc)]
        intro c hc
        rw [hpush] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hsnap
        · exact ih c hc

/-! ## §3 The finding (historical) and the repaired push site -/

/-- **THE REPAIRED PUSH SITE (integration fix, H4).** `stepDecide` pushes
`DecisionCheckpoint.ofBranch cfg.branch` — the PARENT level/frame/trail —
so the push-site obligation of `reachableCpSnapshots_of_step` is discharged
from the parent branch's own reachability alone, by
`checkpointSnapshot_ofBranch`. The pushed record still identifies the
decided child at the parent level (`stepDecide_checkpoints_identify`,
`Proofs.SchedulerForward`). -/
theorem stepDecide_checkpoints_push_snapshot {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {v : Value}
    {vs : Domain} {doms : List Domain} {l : Literal}
    (h : ReachableState leaf orig cfg.branch) :
    ∃ cp, (stepDecide cfg v vs doms l).checkpoints = cp :: cfg.checkpoints ∧
      CheckpointSnapshot leaf orig cp :=
  ⟨DecisionCheckpoint.ofBranch cfg.branch, rfl, checkpointSnapshot_ofBranch h⟩

/-- **FINDING (limitation-3 blocker, kernel-checked; HISTORICAL).** The
FORMER `stepDecide` push record (`frame := parent frame`, `trail := child
trail`, `level := parent level + 1`) admits NO reachable snapshot whenever
the decision is a GENUINE branch: a frame-covered witness falsifying the
pin (the exact witness `ReachableState.fresh_of_not_forced` consumes) is
covered by the record's frame, but `ReachableState.agrees` would force the
child's decision entry to hold at it. REPAIRED by the integration fix
(push `DecisionCheckpoint.ofBranch cfg.branch`, see
`stepDecide_checkpoints_push_snapshot`); this statement is retained as the
refutation of the old shape. -/
theorem decide_push_not_snapshot {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {l : Literal}
    (hw : ∃ a, FrameCovers bs.frame a ∧ l.norm.eval a ≠ some true) :
    ¬ CheckpointSnapshot leaf orig
      { level := bs.level + 1, frame := bs.frame,
        trail := (bs.decide l).trail } := by
  rintro ⟨bs', hreach, hframe, htrail, -⟩
  obtain ⟨a, hcov, hne⟩ := hw
  have hmem : ({ literal := l.norm, level := bs.level + 1, reason := none }
      : TrailEntry) ∈ (bs.decide l).trail := by
    simp [BranchState.decide]
  have h := hreach.agrees _ (by rw [htrail]; exact hmem) a (by rw [hframe]; exact hcov)
  exact hne h

/-! ## §4 The consumer interface: the SUCCESS-GUARDED restoration gate

HISTORICAL PROBLEM (fixed here). The former §4 interface quantified over
EVERY conflict configuration with a recorded analysis and a selected
checkpoint — including the configurations where the runtime REJECTS the
checkpoint: `backjumpStep` (`LeanFzn/Solver/UIP/SchedulerStep.lean`) matches
`perform` and routes the `none` case to
`localExclude (checkpointRegion cp)`. At those configurations
`RestorationPreReachable` is FALSE: its first conjunct
`∃ g, filterFrame … = some g` is exactly the complement of the rejection
condition (`restoreNarrow = none ↔ filterFrame … = none` by the definition
of `restoreNarrow`, and `perform = none ↔ restoreNarrow = none` because
`perform` is `restoreNarrow` composed with `Option.map`). The unguarded
interface therefore had no inhabitant and no producer.

THE REPAIR. The gate is RESTATED at the ACTUAL successful runtime event:
the `some restored` equation of `backjumpStep`'s `perform` match (the
`.learnBackjumpAssert` arm). That equation is exactly what the arm hands to
`stepLearnBackjumpAssert`; no Bool/degenerately-true test remains. The
rejection route keeps its own obligation (`hdeadCheckpointRegion`, E1: the
sound `DeadRegion` of `checkpointRegion cp`), so a failed restoration stays
an explicit exclusion/fallback case and the branch SAT/UNSAT semantics are
unchanged (rejection is a local exclusion, success is the jump).

The separate hypothesis `ReachableState leaf cfg.orig cfg.branch` is the
per-site branch input the producer needs in order to discharge the restored
database's entailment (`ReachableState.wf`'s learned conjunct is about the
conflict state's ACTUAL current database, which the snapshot record does
not carry). It is the same per-site input the typed-pin gates
(`hpin`/`hskip`) already carry, and it is in scope at every consumer site
(`ReachableArmsPreserveReach`'s `hbs`, the joint induction's `ih.1`,
`SchedulerInvariant.reachable`). -/
def RestorationStepPreserves (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf},
    SchedulerReachable cfg → ReachableState leaf cfg.orig cfg.branch →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
      RestorationPreReachable leaf cfg.orig
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
        cfg.branch

/-- THE REJECTION CHARACTERIZATION (the formal content of the §4 doc
claim): `perform` fails exactly when the assertion filter rejects the
checkpoint frame. Consequently the former unguarded gate was uninhabitable
at every rejecting site (its first conjunct is the negation of this
condition), and the E1 dead-region task's site premise `perform = none`
is exactly a filter-rejection. -/
theorem perform_eq_none_iff_filterFrame_eq_none {p : BackjumpPlan leaf}
    {bs : BranchState leaf} {original : List Clause} {props : List Propagator} :
    p.perform bs orig original props = none ↔
      filterFrame p.asserting p.checkpoint.frame = none := by
  unfold BackjumpPlan.perform BackjumpPlan.restoreNarrow
  cases hg : filterFrame p.asserting p.checkpoint.frame <;> simp

/-! ## §5 THE REDUCTION OF `RestorationStepPreserves` TO FIELD OBLIGATIONS

The §4 gate is factored into the EXACT `ReachableState` fields of the
restored-and-narrowed state (`restorationState`), so each conjunct is
independently ownable and checkable. `restorationStepPreserves_of_residual`
shows the named residual `RestorationStepResidual` — a per-field bundle,
NOT the conclusion restated — is sufficient. The four shape lemmas below
are free (`rfl`-level) and demonstrate the decomposition is not vacuous.

J1 ROUND 2 (landed): the bundle now HAS a producer
(`restorationObligations_of_snapshot`), whose hypotheses are the ACTUAL
site facts. What each field costs after the producer:

  * `filter_ok`: DERIVED from the successful-perform equation
    (`perform_eq_some_iff`, §4) — never assumed.
  * `length_ok`/`full_fits`: from the snapshot via `filterSlots_length` +
    `Frame.domains_subsets` (proved).
  * `prefix_forced`: from the snapshot (the trail only grew; proved).
  * `agrees`: retained entries `filterFrame_refines` from the snapshot,
    the ASSERTING entry from the filter's own semantics
    (`filterFrame_literal_holds`; proved, needs the named range fact).
  * `narrowing_complete`: filtered-slot removals by the asserting entry
    (`filterFrame_removal_witness`), other slots from the snapshot (proved).
  * `wf`: reason validity of the asserting entry =
    `RestorationCertificate.learnedEntailed` + asserting membership
    (`asserting_norm_mem_of_stable`, needs stable normalization);
    chronology = `othersBelow` + surviving-prefix (`hsurv`) + `NegStable`;
    learned-database entailment = certificate + the site branch
    reachability. NAMED site facts: the certificate, `hstable`, `hneg`,
    `hsurv`.
  * `sorted`: `levelSorted_append` from the snapshot (proved).
  * `distinct`: the enqueue's absence check `hfresh` — NOT implied by the
    certificate (`assertingSurvives` is about the NEGATION) nor by the
    snapshot (`restore_filter_enqueue_distinct` documents the gap); NAMED
    site fact.
  * `filter_ok` on the REJECTION side: never consumed by this bridge — the
    `restoreNarrow = none` route is classified by the local-exclusion arm
    (`hdeadCheckpointRegion`, E1), keeping failure explicit.

Remaining named site obligations (owners): the snapshot
(`CheckpointSnapshot`, the chain joint induction — R2/I1), the analyzer
certificate (P1/N1 provenance), `hstable`/`hneg` (N1 normalization),
`hsurv` (R2 checkpoint identity), `hfresh` (enqueue absence check, S5/E3)
and the asserting literal's in-range discipline (`hrange`, analyzer
output). -/

/-- The restored-and-narrowed state of the §4 bridge at the plan built
from `cp` and the conflict analysis `an`. -/
def restorationState (cp : DecisionCheckpoint leaf) (bs : BranchState leaf)
    (an : ConflictAnalysis) (g : BranchFrame) : BranchState leaf :=
  ((BackjumpPlan.ofCheckpoint cp bs an.asserting an.learned).execute
    (bs.learnGlobal an.learned)).narrowFrame g

/-- Shape: the restored-and-narrowed state's frame IS the filter's `g`. -/
theorem restorationState_frame (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) (g : BranchFrame) :
    (restorationState cp bs an g).frame = g := rfl

/-- Shape: its level is the checkpoint's level (the plan's target). -/
theorem restorationState_level (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) (g : BranchFrame) :
    (restorationState cp bs an g).level = cp.level := rfl

/-- Shape: its learned database is the current one with the payload
inserted head-first (`learnGlobal`). -/
theorem restorationState_learned (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) (g : BranchFrame) :
    (restorationState cp bs an g).learned = an.learned :: bs.learned := by
  simp [restorationState, BranchState.narrowFrame, BranchState.learnGlobal,
    BackjumpPlan.ofCheckpoint, BackjumpPlan.execute]

/-- Shape: its trail is the checkpoint trail, plus the single asserting
entry at the checkpoint's level (with the payload as reason) unless the
asserting literal is already on the checkpoint trail (runtime guard). -/
theorem restorationState_trail_cases (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) (g : BranchFrame) :
    ((restorationState cp bs an g).trail = cp.trail ∧
      ∃ e ∈ cp.trail, e.literal = an.asserting.norm) ∨
    ((restorationState cp bs an g).trail = cp.trail ++
      [{ literal := an.asserting.norm, level := cp.level,
         reason := some { clause := an.learned } }] ∧
      ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm) :=
  BackjumpPlan.execute_trail_cases
    (BackjumpPlan.ofCheckpoint cp bs an.asserting an.learned)
    (bs.learnGlobal an.learned)

theorem restorationState_mem {cp : DecisionCheckpoint leaf}
    {bs : BranchState leaf} {an : ConflictAnalysis} {g : BranchFrame}
    {e : TrailEntry} (he : e ∈ (restorationState cp bs an g).trail) :
    e ∈ cp.trail ∨ e =
      { literal := an.asserting.norm, level := cp.level,
        reason := some { clause := an.learned } } := by
  rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h] at he; exact Or.inl he
  · rw [h] at he
    rcases List.mem_append.mp he with he | he
    · exact Or.inl he
    · exact Or.inr (List.mem_singleton.mp he)

/-- THE FIELD OBLIGATIONS of §4, one conjunct per `ReachableState` field
of `restorationState`. The traversal obligation is split out as
`filter_ok` (the jump guard, not a field of the successor). -/
structure RestorationStepObligations (leaf : Assignment → Bool)
    (orig : List Domain) (cp : DecisionCheckpoint leaf)
    (bs : BranchState leaf) (an : ConflictAnalysis) (g : BranchFrame) : Prop where
  /-- the assertion filter narrows the checkpoint frame (the jump guard) -/
  filter_ok : filterFrame an.asserting cp.frame = some g
  /-- field 1 (`length_ok`) -/
  length_ok : (fullDomains g).length = orig.length
  /-- field 2 (`full_fits`) -/
  full_fits : ∀ i v, v ∈ (fullDomains g).getD i [] → v ∈ orig.getD i []
  /-- field 3 (`prefix_forced`) -/
  prefix_forced : PrefixForced (restorationState cp bs an g).trail orig g.2
  /-- field 4 (`agrees`) -/
  agrees : ∀ e ∈ (restorationState cp bs an g).trail, ∀ a, FrameCovers g a →
    e.literal.eval a = some true
  /-- field 5 (`narrowing_complete`) -/
  narrowing_complete : NarrowingComplete (restorationState cp bs an g).trail
    orig g
  /-- field 6 (`wf`) -/
  wf : (restorationState cp bs an g).WellFormed
  /-- field 7 (`sorted`) -/
  sorted : TrailLevelSorted (restorationState cp bs an g).trail
  /-- field 8 (`distinct`) -/
  distinct : TrailLiteralsDistinct (restorationState cp bs an g).trail

/-- Assembly: the field obligations ARE a reachable state of
`restorationState`. -/
theorem _root_.LeanFzn.Solver.Propagation.ReachableState.of_restorationObligations
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {g : BranchFrame}
    (ho : RestorationStepObligations leaf orig cp bs an g) :
    ReachableState leaf orig (restorationState cp bs an g) :=
  ⟨ho.length_ok, ho.full_fits, ho.prefix_forced, ho.agrees,
    ho.narrowing_complete, ho.wf, ho.sorted, ho.distinct⟩

/-- Converse (completeness of the decomposition): every reachable
`restorationState` satisfies the per-field bundle. The obligations are
therefore exactly the eight fields plus the guard — nothing weaker is
claimed, nothing extra is smuggled in. -/
theorem restorationObligations_of_reachableState
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {g : BranchFrame}
    (hguard : filterFrame an.asserting cp.frame = some g)
    (h : ReachableState leaf orig (restorationState cp bs an g)) :
    RestorationStepObligations leaf orig cp bs an g :=
  ⟨hguard, h.length_ok, h.full_fits, h.prefix_forced, h.agrees,
    h.narrowing_complete, h.wf, h.sorted, h.distinct⟩

/-- **THE §4 BRIDGE FROM THE FIELD BUNDLE.** The snapshot and branch data
are not needed as separate hypotheses here: the obligations already
name every fact about the restored-and-narrowed state (the snapshot enters
in their DISCHARGE, via `bs'.frame = cp.frame`/`bs'.trail = cp.trail`). -/
theorem restorationPreReachable_of_obligations {orig : List Domain}
    {cfg : SchedulerConfig leaf} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf} {g : BranchFrame}
    (ho : RestorationStepObligations leaf orig cp cfg.branch an g) :
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch :=
  ⟨g, ho.filter_ok, ReachableState.of_restorationObligations ho⟩

/-- **THE SUCCESS-SITE PRODUCER (J1 round 2, the J1 core).** The §5 field
bundle at the ACTUAL successful restoration site: the snapshot record of
the selected checkpoint plus the six named site obligations produce the
whole per-field bundle — hence `RestorationPreReachable` (see
`restorationPreReachable_of_success` below). Every field is DERIVED; the
hypotheses are strictly different facts about the site:

  * `hsnap`: the selected checkpoint is a reachable snapshot (chain);
  * `hbs`: the conflict state's branch reachability (for the restored
    database's entailment — the snapshot does not carry `learned`);
  * `hcert`: the analyzer certificate at the recording site;
  * `hstable`: the recorded analysis's asserting literal is normalized
    (N1's recording-site normalization makes this structural);
  * `hneg`: the recorded analysis's learned clause is negation-stable on
    its NON-ASSERTING literals (`NegStableAvoiding`; J1 round 2 — the
    whole-clause form is refuted for canonical Boolean learned literals,
    `negStable_posBool_refuted`);
  * `hsurv`: the surviving-prefix invariant of the checkpoint;
  * `hfresh`: the asserting enqueue's absence check (NOT derivable from
    the certificate, whose `assertingSurvives` speaks about the NEGATION —
    `restore_filter_enqueue_distinct`, RestorationCertificate.lean);
  * `hrange`: the asserting literal names an in-range slot of the box;
  * `hg`: the assertion-filter success (the runtime's `some` branch; the
    full equation is `restorationPreReachable_of_success`'s input). -/
theorem restorationObligations_of_snapshot {orig : List Domain}
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {g : BranchFrame}
    (hsnap : CheckpointSnapshot leaf orig cp)
    (hbs : ReachableState leaf orig bs)
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : an.asserting.atom.slot < orig.length)
    (hg : filterFrame an.asserting cp.frame = some g) :
    RestorationStepObligations leaf orig cp bs an g := by
  obtain ⟨bs', hbs', hf, ht, hl⟩ := hsnap
  have hgpre : g.2 = cp.frame.2 := filterFrame_prefix hg
  have hglen : g.1.length = cp.frame.1.length := filterFrame_rem_length hg
  -- the snapshot payload at the conflict branch's own coordinates
  have hsub : ∀ e ∈ bs'.trail, e ∈ cp.trail := fun e he => by
    rw [ht] at he
    exact he
  have hsub' : ∀ e ∈ cp.trail, e ∈ bs'.trail := fun e he => by
    rw [← ht] at he
    exact he
  have hsorted : TrailLevelSorted cp.trail := by
    rw [← ht]
    exact hbs'.sorted
  have hdistinct : TrailLiteralsDistinct cp.trail := by
    rw [← ht]
    exact hbs'.distinct
  have hnormT : ∀ e ∈ cp.trail, e.literal = e.literal.norm :=
    fun e he => hbs'.wf.2.1 e (hsub' e he)
  obtain ⟨hlev, hnorm, hreason, hchron0, -⟩ := hbs'.wf
  -- frame-length transfer g ← cp.frame ← bs'.frame
  have hlen : (fullDomains g).length = orig.length := by
    have h1 : (fullDomains g).length = (fullDomains cp.frame).length := by
      rw [fullDomains_length, fullDomains_length, hgpre, hglen]
    have h2 : (fullDomains cp.frame).length = (fullDomains bs'.frame).length := by
      rw [← hf]
    exact h1.trans (h2.trans hbs'.length_ok)
  refine ⟨hg, hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- full_fits
    intro i v hv
    exact hbs'.full_fits i v (by
      rw [hf]
      exact Frame.domains_subsets hg i v hv)
  · -- prefix_forced (the trail only grew, the prefix is unchanged)
    intro a htrail hfit i hi
    have hi' : i < bs'.frame.2.length := by
      rw [hf, ← hgpre]
      exact hi
    have h := hbs'.prefix_forced a
      (fun e he => htrail e (List.mem_append.mpr (Or.inl (hsub e he))))
      hfit i hi'
    rw [hf, ← hgpre] at h
    exact h
  · -- agrees: retained entries by refinement, the asserting entry by the filter
    intro e he a hcov
    replace he := restorationState_mem he
    rcases he with he | he
    · exact hbs'.agrees e (hsub' e he) a (by
        rw [hf]
        exact filterFrame_refines hg hcov)
    · subst he
      exact filterFrame_literal_holds hg hcov (by rw [hlen]; exact hrange)
  · -- narrowing_complete
    intro i w horig hnot
    have horig' : w ∈ orig.getD (cp.frame.2.length + i) [] := by
      rw [hgpre] at horig
      exact horig
    by_cases hwas : w ∈ cp.frame.1.getD i []
    · -- dropped by this filter: the asserting entry falsifies it
      obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hg hwas hnot
      obtain ⟨e0, he0, hel⟩ : ∃ e0 ∈ (restorationState cp bs an g).trail,
          e0.literal = an.asserting.norm := by
        rcases restorationState_trail_cases cp bs an g with ⟨h, e0, he0, hel⟩ | ⟨h, -⟩
        · exact ⟨e0, by rw [h]; exact he0, hel⟩
        · refine ⟨{ literal := an.asserting.norm, level := cp.level,
                      reason := some { clause := an.learned } }, ?_, rfl⟩
          rw [h]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      refine ⟨e0, he0, ?_, ?_⟩
      · show e0.literal.atom.slot = g.2.length + i
        rw [hel, norm_atom_slot, hslot, hgpre]
      · rw [hel]; rwa [norm_valueHolds]
    · -- already excluded: the snapshot's own witness, transported
      have horig'' : w ∈ orig.getD (bs'.frame.2.length + i) [] := by
        rw [hf]
        exact horig'
      have hnot' : w ∉ bs'.frame.1.getD i [] := by
        rw [hf]
        exact hwas
      obtain ⟨e, he, hslot, hfalse⟩ := hbs'.narrowing_complete i w horig'' hnot'
      refine ⟨e, ?_, ?_, hfalse⟩
      · rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]; exact hsub e he
        · rw [h]; exact List.mem_append.mpr (Or.inl (hsub e he))
      · show e.literal.atom.slot = g.2.length + i
        rw [hslot, hgpre, ← hf]
  · -- wf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- trail levels
      intro e he
      replace he := restorationState_mem he
      show e.level ≤ cp.level
      rcases he with he | he
      · simpa only [hl] using hlev e (hsub' e he)
      · subst he
        exact Nat.le_refl _
    · -- normalization
      intro e he
      replace he := restorationState_mem he
      rcases he with he | he
      · exact hnorm e (hsub' e he)
      · subst he
        exact (norm_norm an.asserting).symm
    · -- reason validity: the asserting entry's reason is the certificate's
      intro e he r hr
      replace he := restorationState_mem he
      rcases he with he | he
      · exact hreason e (hsub' e he) r hr
      · subst he
        have hr1 : { clause := an.learned } = r := by
          simpa only [Option.mem_some_iff] using hr
        rw [← hr1]
        exact ⟨hcert.learnedEntailed,
          hcert.asserting_norm_mem_of_stable hstable⟩
    · -- chronology: `othersBelow` + surviving prefix + negation stability
      intro e he r hr l hl hne
      rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h] at he ⊢
        obtain ⟨e'', he'', heq, hlt⟩ :=
          hchron0 e (hsub' e he) r hr l hl hne
        refine ⟨e'', hsub e'' he'', heq, ?_⟩
        rw [ht] at hlt
        exact hlt
      rw [h] at he ⊢
      rcases List.mem_append.mp he with he | he
      · obtain ⟨e'', he'', heq, hlt⟩ :=
          hchron0 e (hsub' e he) r hr l hl hne
        refine ⟨e'', ?_, heq, ?_⟩
        · exact List.mem_append.mpr (Or.inl (hsub e'' he''))
        · rw [ht] at hlt
          exact earlierThan_extend hlt
      · rw [List.mem_singleton] at he
        subst he
        have hr1 : { clause := an.learned } = r := by
          simpa only [Option.mem_some_iff] using hr
        have hl' : l ∈ an.learned := by simpa only [← hr1] using hl
        obtain ⟨e'', he'', heq⟩ :=
          restore_chronology_of_certificate hcert hstable hsurv hneg l hl' hne
        refine ⟨e'', ?_, heq, ?_⟩
        · exact List.mem_append.mpr (Or.inl he'')
        · exact earlierThan_append_last he''
    · -- the learned database: certificate + the site branch's entailment
      intro c hc
      rw [restorationState_learned] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hcert.learnedEntailed _ (List.mem_singleton_self _)
      · exact hbs.wf.2.2.2.2 c hc
  · -- sorted
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hsorted
    rw [h]
    refine levelSorted_append hsorted ?_
    intro e' he'
    have hle := hlev e' (hsub' e' he')
    rw [hl] at hle
    show e'.level ≤ cp.level
    exact hle
  · -- distinct: the runtime guard skips an already-present asserting literal
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, hfresh⟩
    · rw [h]; exact hdistinct
    rw [h]
    exact TrailLiteralsDistinct.enqueue hdistinct hnormT hfresh

/-- **THE `hpre` PRODUCER AT THE ACTUAL SUCCESS EVENT.** The runtime's
`some restored` equation (`perform`) plus the site facts yields
`RestorationPreReachable`. The `∃ g` and the filter guard are EXTRACTED
from `perform`'s own value (`perform_eq_some_iff`), never assumed; the
reachability conclusion is the §5 bundle at that same `g`.

J1 ROUND 2: the honest negation-stability family is
`NegStableAvoiding an.asserting an.learned` (see
`restorationObligations_of_snapshot`); this is the variant the J1 chain
consumes. -/
theorem restorationPreReachable_of_success_avoiding {orig : List Domain}
    {cfg : SchedulerConfig leaf} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf} {restored : BranchState leaf}
    (hsnap : CheckpointSnapshot leaf orig cp)
    (hbs : ReachableState leaf orig cfg.branch)
    (hcert : RestorationCertificate leaf cfg.branch an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : an.asserting.atom.slot < orig.length)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch := by
  obtain ⟨g, hg, -⟩ := perform_eq_some_iff.mp hp
  exact restorationPreReachable_of_obligations
    (restorationObligations_of_snapshot hsnap hbs hcert hstable hneg hsurv
      hrange hg)

/-- COMPATIBILITY WRAPPER (legacy whole-clause `NegStable` signature):
retained solely so the out-of-scope caller `supportedHpre_of_premises`
(SupportedProviders §3-bis, owned elsewhere) keeps compiling. Its `hneg`
family is the refuted whole-clause form (`negStable_posBool_refuted`);
new sites must use `restorationPreReachable_of_success_avoiding`. -/
theorem restorationPreReachable_of_success {orig : List Domain}
    {cfg : SchedulerConfig leaf} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf} {restored : BranchState leaf}
    (hsnap : CheckpointSnapshot leaf orig cp)
    (hbs : ReachableState leaf orig cfg.branch)
    (hcert : RestorationCertificate leaf cfg.branch an)
    (hstable : an.asserting.norm = an.asserting)
    (hneg : NegStable an.learned)
    (hsurv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : an.asserting.atom.slot < orig.length)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch :=
  restorationPreReachable_of_success_avoiding hsnap hbs hcert hstable
    hneg.avoiding hsurv hrange hp

/-- THE NAMED RESIDUAL of `RestorationStepPreserves`: exactly the
per-field bundle at every reachable conflict configuration's SUCCESSFUL
jump site. This is a strict decomposition, NOT the conclusion restated:
the eight fields are separately ownable (see the §5 header table), and the
converse `restorationObligations_of_reachableState` shows the bundle is
precisely the fields + the jump guard. -/
def RestorationStepResidual (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf},
    SchedulerReachable cfg → ReachableState leaf cfg.orig cfg.branch →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
    ∃ g : BranchFrame, RestorationStepObligations leaf cfg.orig cp cfg.branch an g

/-- `RestorationStepResidual` proves `RestorationStepPreserves`: the §4
consumer interface is closed by the per-field bundle alone. -/
theorem restorationStepPreserves_of_residual
    (h : RestorationStepResidual leaf) : RestorationStepPreserves leaf :=
  fun hreach hbs hconf hana hcp hp =>
    let ⟨_, ho⟩ := h hreach hbs hconf hana hcp hp
    restorationPreReachable_of_obligations ho

/-- **THE SITE-INDEXED PRODUCER (J1 acceptance).** `RestorationStepPreserves`
is PROVED, not assumed: from the raw checkpoint-push bundle (`hpush`, the
same chain premise the §2 `reachableCpSnapshots_of_step` induction
consumes) and the six named per-site obligations. Each obligation is
strictly weaker than the conclusion and independently ownable:

  * chain/snapshot: `reachableCpSnapshots_of_step hpush` (R2/I1's joint
    scheduler/chain induction supplies `hpush` from predecessor
    reachability — the same input the decide push site consumes);
  * `hcert`/`hstable`/`hneg`: the analyzer certificate and the
    normalization stability of the recorded analysis (N1's recording-site
    normalization makes the latter two structural);
  * `hsurv`: the surviving-prefix invariant (R2 checkpoint identity);
  * `hfresh`: the enqueue absence check (S5/E3; the certificate cannot
    supply it, see `restore_filter_enqueue_distinct`);
  * `hrange`: the analyzer's asserting literal names an in-range slot. -/
theorem restorationStepPreserves_of_site {leaf : Assignment → Bool}
    (hpush : ∀ {cfg cfg' : SchedulerConfig leaf},
      SchedulerReachable cfg → (schedulerNext cfg).successor = some cfg' →
      List.Sublist cfg'.checkpoints cfg.checkpoints ∨
        ∃ cp, cfg'.checkpoints = cp :: cfg.checkpoints ∧
          CheckpointSnapshot leaf cfg.orig cp)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hstable : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.norm = an.asserting)
    (hneg : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SchedulerReachable cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.atom.slot < cfg.orig.length) :
    RestorationStepPreserves leaf := by
  intro cfg ev an cp restored hreach hbs hconf hana hcp hp
  have hsnap : CheckpointSnapshot leaf cfg.orig cp :=
    reachableCpSnapshots_of_step hpush hreach cp (checkpointAt_mem hcp)
  exact restorationPreReachable_of_success_avoiding hsnap hbs
    (hcert hreach hconf hana)
    (hstable hreach hconf hana) (hneg hreach hconf hana)
    (hsurv hreach hconf hana hcp)
    (hrange hreach hconf hana) hp

end LeanFzn.Solver.UIP
