/-
Purpose (PLAN.md row S4, prereq S3): backjump coverage for the CONCRETE
jump successor `stepLearnBackjumpAssert cfg p ev restored`.

What this module PROVES (from predecessor facts, no successor field is
  re-assumed):
  * `hpend`: pending is carried unchanged by the jump, so the
    predecessor's `pending_fits` transfers definitionally
    (`stepLearnBackjumpAssert_pending_fits`).
  * `hbfit`: the successor branch frame fits `orig` — the successor's own
    reachability (`arm 5`'s `hreach`, S3's route) `branch_fits` field
    (`stepLearnBackjumpAssert_branch_fits`).
  * `hcov`: `BackjumpCovers` for the concrete successor composes from
    (a) `JumpFrameAlternative` — every original leaf covered by the
    pre-jump branch frame is either covered by the restored frame or
    falsifies a NEWLY LEARNED clause — plus (b) the unchanged pending
    (`backjumpCovers_of_frame_alternative`), and then
    `stepLearnBackjumpAssert_coverage_from_facts` instantiates the frozen
    `stepLearnBackjumpAssert_coverage` combinator. No live solution is
    lost: the entailment side condition makes the database disjunct
    vacuous on leaf solutions (`entailed_db_never_excludes`), so the
    frames must carry them.
  * `hmono`: learned-database monotonicity through the restoration,
    `RestorationKeepsLearned` (the named S3/L1 residual from `perform`'s
    `learnGlobal`) gives `cfg.branch.learned ⊆ succ.branch.learned`
    (`stepLearnBackjumpAssert_learned_mono`).
  * LOG CAVEAT (named): `registration_is_exclusion_not_progress` — log
    membership only ever justifies EXCLUSION of dead byFrame regions (no
    live leaf inside them, via `ExhaustionLog.Sound` at the registration
    site; `DeadRegion.byFrame_sound`) together with membership
    persistence (`ExhaustionLog.registered_permanent`). It is NOT, and no
    theorem here derives from it, a progress/no-revisit claim: that is
    P3/P4's obligation.

RESIDUALS (stated, never assumed; owners tagged):
  * `JumpFrameAlternative` — REDUCED (this module): the frame algebra
    half is DERIVED (`jumpFrameAlternative_of_recorded_analysis`) from
    the single premise `FalsifiedByTrail cfg.branch an.learned`
    (`RecordedAnalysisFalsified`, owner B2/A3: `AnalysisContract.
    falsifiedAtConflict` via `BelowFalsified` + `assertedLevel`), so it is
    no longer an independent residual.
  * `RestorationKeepsLearned` — DISCHARGED (`perform_learned_mono`,
    `restorationKeepsLearned_of_perform`): `learnGlobal` head insertion
    survives `execute`/`narrowFrame` (`rfl`) and the closure
    (`explainedClosure_learned_mono`). The residual remains only as the
    name of the statement, proved at the `perform` shape.

DAG: Proofs/SchedulerBackjump -> this module. No runtime module imports it.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerBackjump
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Field laws of the concrete jump successor -/

section FieldLaws

variable {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
  {p : BackjumpPlan leaf} {ev : ConflictEvidence} {restored : BranchState leaf}

/-- The successor frontier is the restored frame followed by the untouched
pending stack (the `orig`/`pending`/`learned`/`log` field laws are the
`@[simp]` lemmas of `Proofs/SchedulerBackjump.lean`). -/
@[simp] theorem stepLearnBackjumpAssert_frontier :
    (stepLearnBackjumpAssert cfg p ev restored).frontier
      = restored.frame :: cfg.pending := rfl

end FieldLaws

/-! ## §2 `hpend` and `hbfit` from predecessor facts -/

/-- `hpend` (owner S4, INTERFACES R0 ledger): pending frames stay inside
`orig`. DERIVED from the predecessor's `pending_fits` —
`stepLearnBackjumpAssert` does not touch `pending` or `orig`, so no
successor obligation is assumed. -/
theorem stepLearnBackjumpAssert_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (h : ∀ f ∈ cfg.pending, ∀ i v,
      v ∈ (Frame.domains f).getD i [] → v ∈ cfg.orig.getD i []) :
    ∀ f ∈ (stepLearnBackjumpAssert cfg p ev restored).pending, ∀ i v,
      v ∈ (Frame.domains f).getD i [] →
        v ∈ (stepLearnBackjumpAssert cfg p ev restored).orig.getD i [] :=
  h

/-- `hbfit` (owner S4): the successor branch frame fits `orig`. DERIVED
from the successor branch's own `ReachableState` (`ReachableState.branch_fits`,
the A1 field `full_fits`); the jump's `learned` update does not touch the
frame. -/
theorem stepLearnBackjumpAssert_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hreach : ReachableState leaf
      (stepLearnBackjumpAssert cfg p ev restored).orig
      (stepLearnBackjumpAssert cfg p ev restored).branch) :
    ∀ i v, v ∈ (Frame.domains
      (stepLearnBackjumpAssert cfg p ev restored).branch.frame).getD i [] →
        v ∈ (stepLearnBackjumpAssert cfg p ev restored).orig.getD i [] :=
  hreach.branch_fits

/-! ## §3 Database monotonicity (`hmono`) -/

/-- NAMED RESIDUAL (owner S3/L1 producers; see module header): the
restored branch database contains the pre-jump learned database —
`perform`'s `learnGlobal p.learned` insertion survives `execute`,
`narrowFrame` and the resumed closure. This is the exact statement every
`restored` produced by `p.perform bs original props = some restored`
satisfies; it is a premise of the monotonicity theorem below, never of
`hmono` itself. -/
def RestorationKeepsLearned {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (restored : BranchState leaf) : Prop :=
  ∀ c ∈ cfg.branch.learned, c ∈ restored.learned

/-- `hmono` (owner S4): `cfg.branch.learned ⊆ succ.branch.learned` from
the named restoration residual. The successor prepends the closure
payload `ev.learned`, so containment is `List.mem_append`'s right
injection — nothing is removed. -/
theorem stepLearnBackjumpAssert_learned_mono {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (h : RestorationKeepsLearned cfg restored) :
    ∀ c ∈ cfg.branch.learned,
      c ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned :=
  fun c hc => List.mem_append.mpr (Or.inr (h c hc))

/-! ### Discharge of `RestorationKeepsLearned`

The residual is now a THEOREM at the real `perform` shape: the
`learnGlobal` head insertion survives `execute`/`narrowFrame` (`rfl`), and
the resumed `explainedClosure` keeps the database (`narrowState` appends
the old one). -/

/-- `narrowState` keeps the learned database: the narrowed state's
database is `learned ++ bs.learned` (`ExplainedPropagation.narrowState`),
so every old clause survives by right injection. -/
theorem narrowState_learned_mono {leaf : Assignment → Bool}
    {bs : BranchState leaf} {g : BranchFrame} {l : Literal} {c : Clause}
    {learned : List Clause} :
    ∀ cl ∈ bs.learned,
      cl ∈ (narrowState bs g l c learned).learned :=
  fun cl hcl => List.mem_append.mpr (Or.inr (show cl ∈ bs.learned from hcl))

/-- The resumed explained closure keeps the learned database (no step of
the closure ever removes a clause). Induction on the frame-mass fuel,
the same motor the closure's other preservation lemmas use. -/
theorem explainedClosure_learned_mono {leaf : Assignment → Bool}
    (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) :
    ∀ c ∈ bs.learned, c ∈ (explainedClosure original props bs).learned := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      ∀ c ∈ bs.learned,
        c ∈ (explainedClosure original props bs).learned from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle c hc
      rw [explainedClosure]
      split
      · exact hc
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle c hc
      rw [explainedClosure]
      split
      · exact hc
      · rename_i d _
        refine ih (narrowState bs d.frame d.literal d.reason d.learned) ?_
          c (narrowState_learned_mono c hc)
        have hdec := d.decreases
        simp only [narrowState] at hdec ⊢
        omega

/-- `restoreNarrow` keeps the learned database: `learnGlobal` head-inserts
`p.learned`, `execute`/`narrowFrame` carry `learned` unchanged, so the
restored state's database is `p.learned :: bs.learned`. -/
theorem restoreNarrow_learned_mono {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf} {s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    ∀ c ∈ bs.learned, c ∈ s.learned := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · next g _ =>
      cases h
      intro c hc
      simpa only [BranchState.narrowFrame, BackjumpPlan.execute,
        BranchState.learnGlobal] using (List.mem_cons.mpr (Or.inr hc))

/-- **RESIDUAL DISCHARGED**: `perform`'s restoration keeps the pre-jump
learned database. `learnGlobal` (head insertion) survives `execute`,
`narrowFrame` (both `rfl`) and the resumed closure
(`explainedClosure_learned_mono`). -/
theorem perform_learned_mono {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    {restored : BranchState leaf}
    (h : p.perform bs original props = some restored) :
    ∀ c ∈ bs.learned, c ∈ restored.learned := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at h
      cases h
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      rw [← h]
      intro c hc
      exact explainedClosure_learned_mono original props s c
        (restoreNarrow_learned_mono hr c hc)

/-- **RESIDUAL DISCHARGED** (`RestorationKeepsLearned`, formerly the named
S3/L1 residual): the actual `perform` result keeps `cfg.branch`'s learned
database. No premise beyond the `perform` equation and the identification
of the pre-jump branch. -/
theorem restorationKeepsLearned_of_perform {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {p : BackjumpPlan leaf} {original : List Clause}
    {props : List Propagator} {restored : BranchState leaf}
    (hb : cfg.branch = bs) (h : p.perform bs original props = some restored) :
    RestorationKeepsLearned cfg restored := by
  unfold RestorationKeepsLearned
  rw [hb]
  exact perform_learned_mono h

/-- Same, with the `perform` arguments read off the configuration: the
shape used at the jump site (`cfg.original`, the scheduler's
propagators). -/
theorem restorationKeepsLearned_of_perform_cfg {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {props : List Propagator} {restored : BranchState leaf}
    (h : p.perform cfg.branch cfg.original props = some restored) :
    RestorationKeepsLearned cfg restored :=
  perform_learned_mono h

/-- The plan's own learned clause is IN the restored database: the
`learnGlobal` head insertion is kept by `execute`/`narrowFrame` and the
closure appends the old database behind it. -/
theorem restoreNarrow_learned_own {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf} {s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    p.learned ∈ s.learned := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · next g _ =>
      cases h
      simp only [BranchState.narrowFrame, BackjumpPlan.execute,
        BranchState.learnGlobal, List.mem_cons_self]

/-- The plan's own learned clause is in the `perform` result's database. -/
theorem perform_learned_mem_own {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    {restored : BranchState leaf}
    (h : p.perform bs original props = some restored) :
    p.learned ∈ restored.learned := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at h
      cases h
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact explainedClosure_learned_mono original props s p.learned
        (restoreNarrow_learned_own hr)

/-! ### Covered-leaf falsification of the recorded analysis clause -/

/-- A trail-falsified clause is false at every assignment satisfying the
trail: every clause literal is the negation of a trail literal, and the
trail literal holds at the assignment, so the clause literal fails. -/
theorem not_satisfiedBy_of_falsifiedByTrail {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {a : Assignment}
    (hfals : FalsifiedByTrail bs c)
    (htrail : ∀ e ∈ bs.trail, e.literal.eval a = some true) :
    ¬ c.SatisfiedBy a := by
  rintro ⟨l, hl, hlt⟩
  obtain ⟨e, he, hlit⟩ := hfals l hl
  have hev := htrail e he
  rw [hlit] at hev
  have hfalse := (Literal.eval_negate_false_iff l a).mp hev
  rw [hfalse] at hlt
  exact absurd hlt (by simp)

/-! ## §4 `BackjumpCovers` and `hcov` for the concrete successor -/

/-- NAMED SEMANTIC RESIDUAL (owner: S4 frame algebra, producers S2/S3; see
module header). For every ORIGINAL leaf solution `a` covered by the
pre-jump branch frame: the restored frame covers `a`, or `a` falsifies one
of the newly learned clauses (`ev.learned ++ restored.learned`). This is
the frame half of "the jump only abandons the branch part the asserting
literal excludes, and every abandoned leaf falsifies the learned clause":
a solution that survives the JUMP is still enumerated by the successor
frontier. Discharge route: `FilterFrame`'s coverage split on the asserting
literal (satisfied → `filterFrame` covers it; falsified → the UIP clause
`p.learned` is falsified, via `BackjumpPlan.execute_represents_forward`'s
frame conjunct and the closure's `narrowState` frame discipline). -/
def JumpFrameAlternative (leaf : Assignment → Bool) (orig : List Domain)
    (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) : Prop :=
  ∀ a, OriginalLeaves leaf orig a → FrameCovers cfg.branch.frame a →
    FrameCovers restored.frame a ∨
      ∃ c ∈ ev.learned ++ restored.learned, ¬ c.SatisfiedBy a

/-- `BackjumpCovers` for the CONCRETE jump successor, from the named frame
residual and the unchanged pending stack. The `cfg.frontier` case split is
`List.mem_cons`: the head is the pre-jump branch frame (residual), a
pending alternative stays covered by the untouched `succ.pending`. -/
theorem backjumpCovers_of_frame_alternative {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (halt : JumpFrameAlternative leaf orig cfg ev restored) :
    BackjumpCovers leaf orig cfg
      (stepLearnBackjumpAssert cfg p ev restored) := by
  intro a ha hcov
  obtain ⟨f, hf, hfc⟩ := hcov
  rcases List.mem_cons.mp hf with rfl | hf
  · rcases halt a ha hfc with h | h
    · exact Or.inl ⟨restored.frame, by
        show restored.frame ∈ restored.frame :: cfg.pending
        exact List.mem_cons_self, h⟩
    · exact Or.inr h
  · exact Or.inl ⟨f, by
      show f ∈ restored.frame :: cfg.pending
      exact List.mem_cons.mpr (Or.inr hf), hfc⟩

/-- **REDUCTION of `JumpFrameAlternative`** (residual is no longer
independent): it holds as soon as the RECORDED analysis's learned clause
is trail-falsified at the pre-jump branch — the plan puts it in the
database (`learnGlobal` via `perform_learned_mem_own`), and every leaf
covered by the pre-jump frame agrees with the trail
(`ReachableState.agrees`), hence falsifies it. `hana` pins `an` to the
recorded evidence; no disjunct is assumed. -/
theorem jumpFrameAlternative_of_recorded_analysis {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis}
    {p : BackjumpPlan leaf} {original : List Clause} {props : List Propagator}
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hana : ev.analysis = some an) (hplan : p.learned = an.learned)
    (hperform : p.perform bs original props = some restored)
    (hfals : FalsifiedByTrail bs an.learned) :
    JumpFrameAlternative leaf orig cfg ev restored := by
  have _ := hana
  intro a _ha hcov
  rw [hb] at hcov
  refine Or.inr ⟨an.learned, ?_, ?_⟩
  · exact List.mem_append.mpr (Or.inr (by
      rw [← hplan]
      exact perform_learned_mem_own hperform))
  · exact not_satisfiedBy_of_falsifiedByTrail hfals
      (fun e he => hreach.agrees e he a hcov)

/-! ### Residual ledger after this wave

`JumpFrameAlternative` is NO LONGER an independent residual: it is
derived (`jumpFrameAlternative_of_recorded_analysis`) from the single
remaining premise

  `FalsifiedByTrail cfg.branch an.learned`   (`RecordedAnalysisFalsified`),

NAMELY: for the recorded analysis `an` of the reachable event, every
literal of `an.learned` is the negation of a `cfg.branch.trail` entry.
This is `AnalysisContract.falsifiedAtConflict` (`ConflictResolution.lean:104`)
specialised to the recorded run; it is NOT on record as a produced
theorem. Producer route: `reachable_analysis_success` exposes
`an = ConflictAnalysis.ofUIP below uip` (`Proofs/SchedulerConflict.lean`),
B2's completion invariant `BelowFalsified`
(`AnalysisCompletion.lean:776,1169`) trail-falsifies the `below` pairs,
and the UIP literal's negation is the asserting literal whose
conflict-level trail entry is B1's `assertedLevel`
(`ConflictResolution.lean:113`). Owner: B2/A3 producers (AnalysisCompletion
+ ConflictResolution), with S3 wiring to the recorded event. Until that
premise is produced, the only irreducible residual of this module is
exactly this statement — `RestorationKeepsLearned` (proved: `perform_learned_mono`)
and the frame-algebra half of `JumpFrameAlternative` are discharged. -/

/-- `hcov` (owner S4, INTERFACES R0 ledger): successor coverage for the
concrete jump, from predecessor facts only — the predecessor's coverage,
the named frame residual, and the named restoration-monotonicity residual.
Composes the frozen `stepLearnBackjumpAssert_coverage` combinator. -/
theorem stepLearnBackjumpAssert_coverage_from_facts {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hcov : cfg.coverage)
    (halt : JumpFrameAlternative leaf cfg.orig cfg ev restored)
    (hmono : RestorationKeepsLearned cfg restored) :
    (stepLearnBackjumpAssert cfg p ev restored).coverage :=
  stepLearnBackjumpAssert_coverage hcov
    (backjumpCovers_of_frame_alternative halt)
    (stepLearnBackjumpAssert_learned_mono hmono)

/-- **`hcov` with BOTH former residuals discharged**: coverage for the
concrete jump follows from the predecessor's coverage and the single
remaining premise `FalsifiedByTrail bs an.learned` for the recorded
analysis (named `RecordedAnalysisFalsified` in the section below; owner
B2/A3). `RestorationKeepsLearned` is now a theorem
(`restorationKeepsLearned_of_perform`) and the frame half of
`JumpFrameAlternative` is derived
(`jumpFrameAlternative_of_recorded_analysis`). -/
theorem stepLearnBackjumpAssert_coverage_of_recorded_analysis
    {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {p : BackjumpPlan leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {original : List Clause}
    {props : List Propagator}
    (hcov : cfg.coverage) (hb : cfg.branch = bs)
    (hreach : ReachableState leaf cfg.orig bs)
    (hana : ev.analysis = some an) (hplan : p.learned = an.learned)
    (hperform : p.perform bs original props = some restored)
    (hfals : FalsifiedByTrail bs an.learned) :
    (stepLearnBackjumpAssert cfg p ev restored).coverage :=
  stepLearnBackjumpAssert_coverage_from_facts hcov
    (jumpFrameAlternative_of_recorded_analysis hb hreach hana hplan hperform
      hfals)
    (restorationKeepsLearned_of_perform hb hperform)

/-- ENTAILMENT, NOT ASSUMPTION: if every clause of a database is entailed
by the leaf semantics, the database disjunct of
`CoversRemainingLeaves`/`BackjumpCovers` can NEVER cover a leaf solution —
so a live leaf is necessarily carried by the FRAME disjunct. This is the
kernel-checked sanity condition that the learned-clause escape hatch in
`JumpFrameAlternative` cannot be abused to "cover" a real solution. -/
theorem entailed_db_never_excludes {leaf : Assignment → Bool}
    {db : List Clause} (hent : LearnedEntailed leaf db) :
    ∀ a, leaf a = true → ¬ ∃ c ∈ db, ¬ c.SatisfiedBy a := by
  rintro a hl ⟨c, hc, hcs⟩
  exact hcs (hent c hc a hl)

/-! ## §5 The log caveat: membership justifies EXCLUSION only -/

/-- LOG CAVEAT (named; PLAN S4 item 4): a registered region is sound BY
ITS REGISTRATION SITE's deadness evidence — the `ExhaustionLog.Sound`
field. This is the ONLY thing log membership yields. -/
theorem registered_region_excludes_only {leaf : Assignment → Bool}
    {log : ExhaustionLog} {r : DeadRegion}
    (hsound : ExhaustionLog.Sound leaf log) (hmem : r ∈ log.regions) :
    DeadRegion.Sound leaf r :=
  hsound r hmem

/-- LOG CAVEAT, byFrame instance: no LIVE LEAF lies inside a registered
`DeadRegion.byFrame` region (the computable registration sites'
`DeadRegion.byFrame_sound` + `ExhaustionLog.Sound`). -/
theorem registered_byFrame_no_live_leaf {leaf : Assignment → Bool}
    {log : ExhaustionLog} {f : BranchFrame}
    (hsound : ExhaustionLog.Sound leaf log)
    (hmem : DeadRegion.byFrame f ∈ log.regions) :
    ∀ a, leaf a = true → (DeadRegion.byFrame f).mem a = true → False :=
  hsound _ hmem

/-- LOG CAVEAT, complete shape: membership yields EXCLUSION and
PERSISTENCE (`ExhaustionLog.registered_permanent`), and exactly those two.
It is NOT a progress/no-revisit claim — nothing here (or in any consumer
added by this module) derives "this work cannot recur" from `r ∈ log.regions`;
progress is P3/P4's separately owned obligation, and the byFrame region's
soundness is always re-derived from its registration site's deadness
evidence, never from membership alone. -/
theorem registration_is_exclusion_not_progress {leaf : Assignment → Bool}
    {log : ExhaustionLog} {f : BranchFrame}
    (hsound : ExhaustionLog.Sound leaf log)
    (hmem : DeadRegion.byFrame f ∈ log.regions) :
    (∀ a, leaf a = true → (DeadRegion.byFrame f).mem a = true → False) ∧
    (∀ extra : List DeadRegion, DeadRegion.byFrame f ∈
      (extra.foldl ExhaustionLog.register log).regions) :=
  ⟨registered_byFrame_no_live_leaf hsound hmem,
    fun extra => ExhaustionLog.registered_permanent hmem extra⟩

end LeanFzn.Solver.UIP
