/-
File: LeanFzn/Solver/UIP/Proofs/ExtendedPoolProducers.lean
vocabulary producers and the run-wide trail-vocabulary induction; owner C1)

Purpose: complete the C1 extended-pool port. The landed `litPoolExt orig dcs`
(= `SchedulerVocabulary.litPoolWith (constraintAtomPool dcs) orig`,
`Proofs/EmissionVocabulary.lean` §5) carries the premise-free unit emission
membership; this module re-keys the trail vocabulary and the database
alignment — the two consumers of the emission vocabulary — to an ARBITRARY
finite pool extension `litPoolWith extra orig` (so BOTH the original
`litPool orig = litPoolWith [] orig` and the unit-route `litPoolExt` are
instances).

  * §1 the pool-parametric vocabulary layer: `TrailVocabularyAt` and
    `DatabaseAlignedAt` (definitionally the landed `TrailVocabulary` /
    `DatabaseAligned` at `pool := litPool orig`) plus their algebra.
  * §2 the parametric per-family producers (the `Proofs/SupportedDatabaseFacts`
    §5–§6 and `Proofs/TrailVocabularyProducers` §1–§4 proofs with the pool
    abstracted): the deduction literal, the closure/restoration trail facts,
    the per-arm laws and the recorded-analysis alignment + asserting-literal
    producers — all at any `litPoolWith extra orig`.
  * §3 **THE hrec DISCHARGE**: the joint forward invariant
    `TrailInvWith` (branch vocabulary ∧ database alignment ∧ checkpoint-trail
    vocabulary ∧ recorded-evidence payload alignment), preserved by EVERY
    real dispatcher arm (`trailInvWith_step`) and maintained along the whole
    supported run (`trailInvWith_of_supportedRun`). This is route (i) of the
    C1 task: vocabulary at EVERY state, so the conflict-RECORDING arm's
    successor (whose predecessor has `conflict = none`) is reached by the
    induction hypothesis and the recording-site premise `hrec` of
    `Proofs/TrailVocabularyProducers.lean` §5 is NO LONGER NEEDED.
  * §4 the exports: the universal and site-form trail-vocabulary producers,
    the extended-pool `halignDB` producer and the checkpoint-vocabulary
    producer, in the unit-route instantiation (`hprops` + `hSupp`) and in
    the `hvocab`-keyed instantiation.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.ExtendedPoolProducers` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.TrailVocabularyProducers
import LeanFzn.Solver.UIP.Proofs.PendingRun
import LeanFzn.Solver.UIP.Proofs.SchedulerConflict
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The pool-parametric vocabulary layer -/

/-- The trail vocabulary at an ARBITRARY literal pool: every trail entry's
normalized literal lies in `pool`. At `pool := litPool orig` this is exactly
the landed `TrailVocabulary` (`trailVocabulary_iff_at`). -/
def TrailVocabularyAt (pool : List Literal) (trail : List TrailEntry) : Prop :=
  ∀ e ∈ trail, e.literal.norm ∈ pool

/-- The branch-level form of `TrailVocabularyAt`. -/
def BranchTrailVocabularyAt {leaf : Assignment → Bool} (pool : List Literal)
    (bs : BranchState leaf) : Prop :=
  TrailVocabularyAt pool bs.trail

/-- The landed `TrailVocabulary` IS the pool-parametric form at the box's own
pool (definitional). -/
theorem trailVocabulary_iff_at {orig : List Domain} {trail : List TrailEntry} :
    TrailVocabulary orig trail ↔ TrailVocabularyAt (litPool orig) trail :=
  Iff.rfl

theorem trailVocabularyAt_mono {pool pool' : List Literal}
    {trail : List TrailEntry} (hsub : ∀ l ∈ pool, l ∈ pool')
    (h : TrailVocabularyAt pool trail) : TrailVocabularyAt pool' trail :=
  fun e he => hsub _ (h e he)

theorem trailVocabularyAt_nil (pool : List Literal) :
    TrailVocabularyAt pool [] := by
  intro e he
  cases he

/-- Extend the pool-parametric vocabulary by one pooled entry. -/
theorem trailVocabularyAt_append_entry {pool : List Literal}
    {trail : List TrailEntry} {e : TrailEntry}
    (h : TrailVocabularyAt pool trail) (he : e.literal.norm ∈ pool) :
    TrailVocabularyAt pool (trail ++ [e]) := by
  intro e' he'
  rcases List.mem_append.mp he' with h1 | h1
  · exact h e' h1
  · rcases List.mem_singleton.mp h1
    exact he

/-- The landed vocabulary transports into any extended pool. -/
theorem trailVocabularyAt_of_trailVocabulary {orig : List Domain}
    {extra : List Atom} {trail : List TrailEntry}
    (h : TrailVocabulary orig trail) :
    TrailVocabularyAt (litPoolWith extra orig) trail :=
  trailVocabularyAt_mono (fun _ hl => litPool_mem_litPoolWith hl) h

/-- The database-side literal-pool alignment at an ARBITRARY literal pool
(the `halignDB` discipline; at `pool := litPool orig` this is the landed
`DatabaseAligned`, definitionally). -/
def DatabaseAlignedAt (pool : List Literal) (db : List Clause) : Prop :=
  ∀ c ∈ db, ∀ q ∈ c, q.norm ∈ pool

/-- The landed `DatabaseAligned` IS the pool-parametric form at the box's own
pool (definitional). -/
theorem databaseAligned_iff_at {orig : List Domain} {db : List Clause} :
    DatabaseAligned orig db ↔ DatabaseAlignedAt (litPool orig) db :=
  Iff.rfl

theorem databaseAlignedAt_mono {pool pool' : List Literal} {db : List Clause}
    (hsub : ∀ l ∈ pool, l ∈ pool') (h : DatabaseAlignedAt pool db) :
    DatabaseAlignedAt pool' db :=
  fun c hc q hq => hsub _ (h c hc q hq)

theorem databaseAlignedAt_nil (pool : List Literal) :
    DatabaseAlignedAt pool [] :=
  fun _ hc => absurd hc (List.not_mem_nil)

theorem databaseAlignedAt_append {pool : List Literal} {db₁ db₂ : List Clause}
    (h₁ : DatabaseAlignedAt pool db₁) (h₂ : DatabaseAlignedAt pool db₂) :
    DatabaseAlignedAt pool (db₁ ++ db₂) := by
  intro c hc q hq
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc q hq
  · exact h₂ c hc q hq

theorem databaseAlignedAt_of_sub {pool : List Literal} {db db' : List Clause}
    (hsub : ∀ c ∈ db, c ∈ db') (h : DatabaseAlignedAt pool db') :
    DatabaseAlignedAt pool db :=
  fun c hc q hq => h c (hsub c hc) q hq

theorem databaseAlignedAt_of_eq {pool : List Literal} {db db' : List Clause}
    (heq : db = db') (h : DatabaseAlignedAt pool db') :
    DatabaseAlignedAt pool db :=
  heq ▸ h

/-- The landed alignment transports into any extended pool. -/
theorem databaseAlignedAt_of_databaseAligned {orig : List Domain}
    {extra : List Atom} {db : List Clause} (h : DatabaseAligned orig db) :
    DatabaseAlignedAt (litPoolWith extra orig) db :=
  databaseAlignedAt_mono (fun _ hl => litPool_mem_litPoolWith hl) h

/-- The pool-parametric pool closures the producers consume, at
`litPoolWith extra orig` (reused from the landed `SchedulerVocabulary`
algebra). -/
theorem litPoolWith_negate_norm_mem {extra : List Atom} {orig : List Domain}
    {l : Literal} (h : l.norm ∈ litPoolWith extra orig) :
    l.negate.norm ∈ litPoolWith extra orig := by
  rw [Literal.negate_norm_eq]
  exact litPoolWith_norm_closed (litPoolWith_negate_closed h)

/-! ## §2 The parametric per-family producers -/

/-- **PARAMETRIC NORM-FALSIFIED ALIGNMENT**: if every literal of `c` has a
recorded normalized falsifier on a trail whose vocabulary holds at `pool`,
then every normalized literal of `c` is in `pool` — given `pool`'s
negation-normalization closure (for `litPoolWith`:
`litPoolWith_negate_norm_mem`). -/
theorem normFalsified_learned_poolAligned_at {pool : List Literal}
    {trail : List TrailEntry} {c : Clause}
    (hnegnorm : ∀ l : Literal, l.norm ∈ pool → l.negate.norm ∈ pool)
    (htrail : TrailVocabularyAt pool trail)
    (hfals : ∀ q ∈ c, ∃ e ∈ trail, e.literal = (q.negate).norm) :
    ∀ q ∈ c, q.norm ∈ pool := by
  intro q hq
  obtain ⟨e, he, heq⟩ := hfals q hq
  have h1 : ((q.negate).norm).norm ∈ pool := by
    have := htrail e he
    rwa [heq] at this
  rw [norm_norm] at h1
  have h2 : (q.negate).negate.norm ∈ pool := hnegnorm (q.negate) h1
  rwa [Literal.negate_negate] at h2

/-- **PARAMETRIC RECORDED-ANALYSIS CLAUSE ALIGNMENT** (the jump payload): at
a recorded-evidence site whose branch carries the `pool` vocabulary, the
analysis's learned clause is `pool`-aligned. -/
theorem recordedAnalysis_learned_poolAligned_at {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis} {pool : List Literal}
    (hnegnorm : ∀ l : Literal, l.norm ∈ pool → l.negate.norm ∈ pool)
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hcfg : SchedulerReachable cfg)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (htrail : BranchTrailVocabularyAt pool bs) :
    ∀ q ∈ an.learned, q.norm ∈ pool :=
  normFalsified_learned_poolAligned_at hnegnorm htrail
    (recordedAnalysis_normFalsified hb hreach hcfg hconf hana)

/-- **PARAMETRIC ASSERTING-LITERAL PRODUCER**: the recorded analysis's
asserting literal is `pool`-pooled as soon as its learned clause is — from
the R1 provenance `an = (ConflictAnalysis.ofUIP below uip).normalized`, the
asserting literal is the normalized head of the learned clause. NO extra
premise (no `NegStable`, no unit-shape hypothesis). -/
theorem recordedAnalysis_asserting_poolAligned_at {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {pool : List Literal}
    (hcfg : SchedulerReachable cfg)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (halign : ∀ q ∈ an.learned, q.norm ∈ pool) :
    an.asserting.norm ∈ pool := by
  obtain ⟨below, uip, -, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hcfg hconf hana
  have hhead : (uip.negate).norm ∈ an.learned := by
    rw [hcanon, ConflictAnalysis.normalized_learned, ConflictAnalysis.ofUIP_learned]
    exact List.mem_cons_self ..
  have hass : an.asserting = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting]
  have hpool : (uip.negate).norm ∈ pool := by
    have h := halign ((uip.negate).norm) hhead
    rwa [norm_norm] at h
  rw [hass, norm_norm]
  exact hpool

/-- A database holding the single normalized unit clause `[q]` is aligned at
any pool. -/
theorem databaseAlignedAt_of_unit {pool : List Literal} {c : Clause}
    (h : ∃ q : Literal, c = [q] ∧ q.norm ∈ pool) :
    DatabaseAlignedAt pool [c] := by
  obtain ⟨q, rfl, hq⟩ := h
  intro c' hc' q' hq'
  have hc1 : c' = [q] := List.mem_singleton.mp hc'
  have hq1 : q' ∈ ([q] : Clause) := by rwa [hc1] at hq'
  have hq2 : q' = q := List.mem_singleton.mp hq1
  subst hq2
  exact hq

/-- A freshness-filtered unit payload (`if b then [c] else []`) is aligned
at any pool from the unit evidence of `c`. -/
theorem databaseAlignedAt_if_singleton {pool : List Literal} {c : Clause}
    {b : Bool} (hunit : ∃ q : Literal, c = [q] ∧ q.norm ∈ pool) :
    DatabaseAlignedAt pool (if b then [c] else []) := by
  cases b with
  | false => simpa using databaseAlignedAt_nil pool
  | true => simpa using databaseAlignedAt_of_unit hunit

/-- **PARAMETRIC DEDUCTION-LITERAL PRODUCER**: a selected deduction's literal
is `pool`-pooled — propagator-sourced events from the pool-parametric
emission vocabulary, database-sourced events from the `pool`-alignment of the
state's own learned database. -/
theorem deduction_literal_pooled_at {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (hdb : DatabaseAlignedAt pool bs.learned)
    (hd : explainedDeduction original props bs = some d) :
    d.literal.norm ∈ pool := by
  obtain ⟨c, lr, fl, hev, -, -⟩ := explainedDeduction_learned_shape hd
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨hmem, -, hrem⟩ := scanDatabase_implied_facts hsrc
    have hl : d.literal ∈ c := by
      have h1 : d.literal ∈ clauseRemaining bs.frame c := by
        rw [hrem]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp h1).1
    exact hdb c hmem d.literal hl
  · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, -, hlq, -, hqpool⟩ :=
      hvocab.1 p hpm (frameState bs.frame) d.literal r hrun
    rw [hlq]
    exact hqpool

/-- **PARAMETRIC PROPAGATE-ARM PAYLOAD PRODUCER**. -/
theorem databaseAlignedAt_deduction_learned {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (hd : explainedDeduction original props bs = some d) :
    DatabaseAlignedAt pool d.learned := by
  obtain ⟨c, lr, fl, hev, -, hlearned⟩ := explainedDeduction_learned_shape hd
  rw [hlearned]
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨-, hlr, -⟩ := scanDatabase_implied_facts hsrc
    rw [hlr]
    rw [if_neg (by simp)]
    exact databaseAlignedAt_nil pool
  · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, hq, -, -, hqpool⟩ :=
      hvocab.1 p hpm (frameState bs.frame) d.literal r hrun
    exact databaseAlignedAt_if_singleton ⟨q, by rw [hcl, hq], hqpool⟩

/-- **PARAMETRIC LOCALEXCLUDE / EVIDENCE PAYLOAD PRODUCER**. -/
theorem databaseAlignedAt_conflict_learned {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {cs : List Clause} {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (hev : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    DatabaseAlignedAt pool
      (cs.filter fun c => !(bs.learned.contains c)) := by
  rcases nextPruningEvent_conflict_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨-, -, -, hcs⟩ := scanDatabase_conflict_facts hsrc
    rw [hcs, List.filter_nil]
    exact databaseAlignedAt_nil pool
  · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
    rw [hcs]
    rcases hvocab.2 p hpm (frameState bs.frame) c hrun with
      hnil | ⟨q, hcq, -, hqpool⟩
    · rw [hnil]
      show DatabaseAlignedAt pool
        (List.filter (fun c => !(bs.learned.contains c)) [])
      rw [List.filter_nil]
      exact databaseAlignedAt_nil pool
    · by_cases hempty : c.isEmpty = true
      · rw [hempty]
        show DatabaseAlignedAt pool
          (List.filter (fun c => !(bs.learned.contains c)) [])
        rw [List.filter_nil]
        exact databaseAlignedAt_nil pool
      · rw [if_neg hempty]
        refine databaseAlignedAt_of_sub
          (fun c' hc' => (List.mem_filter.mp hc').1) ?_
        exact databaseAlignedAt_of_unit ⟨q, hcq, hqpool⟩

/-- The terminal-conflict payload of `terminalResult` is `pool`-aligned. -/
theorem databaseAlignedAt_terminalResult_conflict {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs bs' : BranchState leaf} {cs learned : List Clause}
    {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (ht : terminalResult original props bs = .conflict bs' cs learned) :
    DatabaseAlignedAt pool learned := by
  rw [terminalResult] at ht
  split at ht
  · cases ht
  · rename_i cs' hev
    cases ht
    exact databaseAlignedAt_conflict_learned hvocab hev
  · split at ht <;> cases ht

/-- The terminal `localExcluded` payload is `pool`-aligned. -/
theorem databaseAlignedAt_terminalResult_localExcluded
    {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs bs' : BranchState leaf} {lit : Option Literal} {reason : Option Clause}
    {learned : List Clause} {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (ht : terminalResult original props bs =
      .localExcluded bs' lit reason learned) :
    DatabaseAlignedAt pool learned := by
  rw [terminalResult] at ht
  split at ht
  · cases ht
  · cases ht
  · rename_i l c lr fl hev
    split at ht
    · cases ht
      rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
      · obtain ⟨-, hlr, -⟩ := scanDatabase_implied_facts hsrc
        rw [hlr]
        rw [if_neg (by simp)]
        exact databaseAlignedAt_nil pool
      · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ :=
          scanPropagators_implied_facts hprop
        obtain ⟨q, hq, -, -, hqpool⟩ :=
          hvocab.1 p hpm (frameState bs.frame) l r hrun
        exact databaseAlignedAt_if_singleton ⟨q, by rw [hcl, hq], hqpool⟩
    · cases ht

/-- **PARAMETRIC CLOSURE MAINTENANCE** (database half). -/
theorem databaseAlignedAt_explainedClosure {leaf : Assignment → Bool}
    (original : List Clause) (props : List Propagator) (bs : BranchState leaf)
    {pool : List Literal} (hvocab : EmissionVocabularyAt pool props)
    (h : DatabaseAlignedAt pool bs.learned) :
    DatabaseAlignedAt pool (explainedClosure original props bs).learned := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → DatabaseAlignedAt pool bs.learned →
      DatabaseAlignedAt pool (explainedClosure original props bs).learned from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) h
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle h
      rw [explainedClosure]
      split
      · exact h
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle h
      rw [explainedClosure]
      split
      · exact h
      · rename_i d hd
        have hpay := databaseAlignedAt_deduction_learned hvocab hd
        have hnew : DatabaseAlignedAt pool
            (narrowState bs d.frame d.literal d.reason d.learned).learned := by
          show DatabaseAlignedAt pool (d.learned ++ bs.learned)
          exact databaseAlignedAt_append hpay h
        refine ih (narrowState bs d.frame d.literal d.reason d.learned) ?_ hnew
        have hdec := d.decreases
        simp only [narrowState] at hdec ⊢
        omega

/-- **PARAMETRIC JUMP RESTORED-DATABASE PRODUCER**. -/
theorem databaseAlignedAt_perform {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    {pool : List Literal}
    (hvocab : EmissionVocabularyAt pool props)
    (hdb : DatabaseAlignedAt pool bs.learned)
    (hplan : DatabaseAlignedAt pool [p.learned])
    (hperf : p.perform bs original props = some restored) :
    DatabaseAlignedAt pool restored.learned := by
  unfold BackjumpPlan.perform at hperf
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at hperf
      cases hperf
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at hperf
      rw [← hperf]
      refine databaseAlignedAt_explainedClosure original props s hvocab ?_
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · cases hr
        show DatabaseAlignedAt pool (p.learned :: bs.learned)
        exact databaseAlignedAt_append hplan hdb

/-- A single-clause database is `pool`-aligned from its clause's pointwise
alignment. -/
theorem databaseAlignedAt_singleton_of_clause {pool : List Literal} {c : Clause}
    (h : ∀ q ∈ c, q.norm ∈ pool) : DatabaseAlignedAt pool [c] := by
  intro c' hc' q hq
  have hc'e : c' = c := List.mem_singleton.mp hc'
  subst hc'e
  exact h q hq

/-! ## §2b The parametric trail facts -/

/-- **PARAMETRIC CLOSURE TRAIL MAINTENANCE** (the `Frame.mass` fuel
induction of `explainedClosure_trailVocabulary` with the pool abstracted). -/
theorem explainedClosure_trailVocabulary_at {leaf : Assignment → Bool}
    (original : List Clause) (props : List Propagator) (bs : BranchState leaf)
    {pool : List Literal} (hvocab : EmissionVocabularyAt pool props)
    (hdb : DatabaseAlignedAt pool bs.learned)
    (hv : TrailVocabularyAt pool bs.trail) :
    TrailVocabularyAt pool (explainedClosure original props bs).trail := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → TrailVocabularyAt pool bs.trail →
      DatabaseAlignedAt pool bs.learned →
      TrailVocabularyAt pool (explainedClosure original props bs).trail from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) hv hdb
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hv hdb
      rw [explainedClosure]
      split
      · exact hv
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hv hdb
      rw [explainedClosure]
      split
      · exact hv
      · rename_i d hd
        have hl := deduction_literal_pooled_at hvocab hdb hd
        have hpay := databaseAlignedAt_deduction_learned hvocab hd
        have hv' : TrailVocabularyAt pool
            (narrowState bs d.frame d.literal d.reason d.learned).trail := by
          show TrailVocabularyAt pool (bs.trail ++
            [{ literal := d.literal.norm, level := bs.level,
               reason := some { clause := d.reason } }])
          exact trailVocabularyAt_append_entry hv
            (by rw [norm_norm]; exact hl)
        have hdb' : DatabaseAlignedAt pool
            (narrowState bs d.frame d.literal d.reason d.learned).learned := by
          show DatabaseAlignedAt pool (d.learned ++ bs.learned)
          exact databaseAlignedAt_append hpay hdb
        refine ih (narrowState bs d.frame d.literal d.reason d.learned)
          ?_ hv' hdb'
        have hdec := d.decreases
        simp only [narrowState] at hdec ⊢
        omega

/-- **PARAMETRIC RESTORE-LEVEL TRAIL VOCABULARY** (trail filtering). -/
theorem restoreLevel_trailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {bs : BranchState leaf} {k : Nat}
    (hv : TrailVocabularyAt pool bs.trail) :
    TrailVocabularyAt pool (bs.restoreLevel k).trail := by
  show TrailVocabularyAt pool (bs.trail.filter fun e => e.level ≤ k)
  intro e he
  exact hv e (List.mem_filter.mp he).1

/-- **PARAMETRIC JUMP RESTORED-TRAIL PRODUCER**: `restoreNarrow` restores the
CHECKPOINT's trail plus the single asserting entry, so its vocabulary needs
the checkpoint's vocabulary and the asserting literal's pooling. -/
theorem restoreNarrow_trailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (hcp : TrailVocabularyAt pool p.checkpoint.trail)
    (hass : p.asserting.norm ∈ pool)
    (h : p.restoreNarrow bs = some s) :
    TrailVocabularyAt pool s.trail := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · rename_i g _
    cases h
    show TrailVocabularyAt pool (p.execute (bs.learnGlobal p.learned)).trail
    rw [BackjumpPlan.execute_trail]
    exact trailVocabularyAt_append_entry hcp (by rw [norm_norm]; exact hass)

/-- **PARAMETRIC FULL JUMP TRAIL VOCABULARY** (`perform`). -/
theorem perform_trailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hvocab : EmissionVocabularyAt pool props)
    (hdb : DatabaseAlignedAt pool bs.learned)
    (hplan : DatabaseAlignedAt pool [p.learned])
    (hcp : TrailVocabularyAt pool p.checkpoint.trail)
    (hass : p.asserting.norm ∈ pool)
    (hperf : p.perform bs original props = some restored) :
    TrailVocabularyAt pool restored.trail := by
  unfold BackjumpPlan.perform at hperf
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at hperf
      cases hperf
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at hperf
      rw [← hperf]
      refine explainedClosure_trailVocabulary_at original props s hvocab ?_
        (restoreNarrow_trailVocabulary_at hcp hass hr)
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · cases hr
        show DatabaseAlignedAt pool (p.learned :: bs.learned)
        exact databaseAlignedAt_append hplan hdb

/-! ## §2c The parametric arm laws -/

theorem stepPropagate_branchTrailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {cfg : SchedulerConfig leaf}
    {d : ProductiveDeduction leaf cfg.branch}
    (hv : BranchTrailVocabularyAt pool cfg.branch)
    (hl : d.literal.norm ∈ pool) :
    BranchTrailVocabularyAt pool (stepPropagate cfg d).branch := by
  change TrailVocabularyAt pool (stepPropagate cfg d).branch.trail
  have hv' : TrailVocabularyAt pool cfg.branch.trail := hv
  intro e he
  simp only [stepPropagate, narrowState] at he
  rcases List.mem_append.mp he with h1 | h1
  · exact hv' e h1
  · rw [List.mem_singleton] at h1
    subst h1
    simpa [Literal.norm_idem] using hl

theorem stepDecide_branchTrailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {cfg : SchedulerConfig leaf} {v : Value}
    {vs : Domain} {doms : List Domain} {l : Literal}
    (hv : BranchTrailVocabularyAt pool cfg.branch)
    (hl : l.norm ∈ pool) :
    BranchTrailVocabularyAt pool (stepDecide cfg v vs doms l).branch := by
  change TrailVocabularyAt pool (stepDecide cfg v vs doms l).branch.trail
  have hv' : TrailVocabularyAt pool cfg.branch.trail := hv
  intro e he
  simp only [stepDecide, BranchState.decide] at he
  rcases List.mem_append.mp he with h1 | h1
  · exact hv' e h1
  · rw [List.mem_singleton] at h1
    subst h1
    simpa [Literal.norm_idem] using hl

theorem stepDecideSkip_branchTrailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {cfg : SchedulerConfig leaf} (v : Value)
    (doms : List Domain) (hv : BranchTrailVocabularyAt pool cfg.branch) :
    BranchTrailVocabularyAt pool (stepDecideSkip cfg v doms).branch := by
  show TrailVocabularyAt pool cfg.branch.trail
  exact hv

theorem stepAnalyzeConflictCounted_branchTrailVocabulary_at
    {leaf : Assignment → Bool} {pool : List Literal}
    {cfg : SchedulerConfig leaf} (c : Clause) (learned : List Clause)
    (n : Nat) (hv : BranchTrailVocabularyAt pool cfg.branch) :
    BranchTrailVocabularyAt pool
      (stepAnalyzeConflictCounted cfg c learned n).branch := by
  rwa [stepAnalyzeConflictCounted_branch]

theorem stepLocalExclude_branchTrailVocabulary_at {leaf : Assignment → Bool}
    {pool : List Literal} {cfg : SchedulerConfig leaf} (learned : List Clause)
    (r : DeadRegion) (hv : BranchTrailVocabularyAt pool cfg.branch) :
    BranchTrailVocabularyAt pool (stepLocalExclude cfg learned r).branch := by
  show TrailVocabularyAt pool cfg.branch.trail
  exact hv

theorem stepChronologicalFallback_branchTrailVocabulary_at
    {leaf : Assignment → Bool} {pool : List Literal}
    {cfg : SchedulerConfig leaf} (r : DeadRegion)
    (hv : BranchTrailVocabularyAt pool cfg.branch) :
    BranchTrailVocabularyAt pool (stepChronologicalFallback cfg r).branch := by
  show TrailVocabularyAt pool cfg.branch.trail
  exact hv

/-- The canonical resume's branch-level vocabulary at any extended pool. -/
theorem resumePending_branchTrailVocabulary_at {leaf : Assignment → Bool}
    {orig : List Domain} {extra : List Atom} {bs : BranchState leaf}
    {f : BranchFrame} (hb : PendingBacked orig f) :
    BranchTrailVocabularyAt (litPoolWith extra orig) (resumePending orig bs f) :=
  fun e he =>
    litPool_mem_litPoolWith (resumePending_branchTrailVocabulary (bs := bs) hb e he)

/-- The split literal producer at any extended pool (the landed litPool fact
transported by the pool bridge). -/
theorem stepDecide_splitLiteral_pooled_at {leaf : Assignment → Bool}
    {orig : List Domain} {extra : List Atom} {cfg : SchedulerConfig leaf}
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hreach : ReachableState leaf orig cfg.branch)
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    l.norm ∈ litPoolWith extra orig :=
  litPool_mem_litPoolWith (stepDecide_splitLiteral_pooled hreach hs)

/-! ## §2d The parametric database arm laws -/

theorem stepDecide_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (v : Value) (vs : Domain)
    (doms : List Domain) (l : Literal)
    (h : DatabaseAlignedAt pool cfg.branch.learned) :
    DatabaseAlignedAt pool (stepDecide cfg v vs doms l).branch.learned := by
  rwa [stepDecide_learned]

theorem stepDecideSkip_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (v : Value) (doms : List Domain)
    (h : DatabaseAlignedAt pool cfg.branch.learned) :
    DatabaseAlignedAt pool (stepDecideSkip cfg v doms).branch.learned := by
  show DatabaseAlignedAt pool cfg.branch.learned
  exact h

theorem stepAnalyzeConflictCounted_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (c : Clause) (learned : List Clause)
    (n : Nat) (h : DatabaseAlignedAt pool cfg.branch.learned) :
    DatabaseAlignedAt pool
      (stepAnalyzeConflictCounted cfg c learned n).branch.learned := by
  rwa [stepAnalyzeConflictCounted_branch]

theorem stepChronologicalFallback_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (r : DeadRegion)
    (h : DatabaseAlignedAt pool cfg.branch.learned) :
    DatabaseAlignedAt pool (stepChronologicalFallback cfg r).branch.learned := by
  rwa [P3.stepChronologicalFallback_learned_eq]

theorem stepConsume_halignDBAt {pool : List Literal}
    {cfg next : SchedulerConfig leaf} (hstep : stepConsume cfg = some next)
    (h : DatabaseAlignedAt pool cfg.branch.learned) :
    DatabaseAlignedAt pool next.branch.learned := by
  rwa [P3.stepConsume_learned hstep]

theorem stepPropagate_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (d : ProductiveDeduction leaf cfg.branch)
    (h : DatabaseAlignedAt pool cfg.branch.learned)
    (hpay : DatabaseAlignedAt pool d.learned) :
    DatabaseAlignedAt pool (stepPropagate cfg d).branch.learned := by
  rw [P3.stepPropagate_learned_eq]
  exact databaseAlignedAt_append hpay h

theorem stepLocalExclude_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (learned : List Clause) (r : DeadRegion)
    (h : DatabaseAlignedAt pool cfg.branch.learned)
    (hpay : DatabaseAlignedAt pool learned) :
    DatabaseAlignedAt pool (stepLocalExclude cfg learned r).branch.learned := by
  rw [P3.stepLocalExclude_learned_eq]
  exact databaseAlignedAt_append hpay h

theorem stepLearnBackjumpAssert_halignDBAt {pool : List Literal}
    {cfg : SchedulerConfig leaf} (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf)
    (hpay : DatabaseAlignedAt pool ev.learned)
    (hrest : DatabaseAlignedAt pool restored.learned) :
    DatabaseAlignedAt pool
      (stepLearnBackjumpAssert cfg p ev restored).branch.learned := by
  rw [stepLearnBackjumpAssert_learned]
  exact databaseAlignedAt_append hpay hrest

/-! ## §3 The joint forward invariant: hrec discharged

`TrailInvWith orig extra cfg` is the run-wide invariant route (i) of the C1
task: the branch's trail vocabulary, the branch database alignment, the
trail vocabulary of every SAVED checkpoint and the alignment of the
RECORDED evidence payload — all at the extended pool `litPoolWith extra
orig`, at EVERY state of the run. The conflict-RECORDING arm's successor
inherits the predecessor's branch vocabulary (the recording arm leaves the
branch unchanged), so the recording-site premise `hrec` of
`Proofs/TrailVocabularyProducers.lean` §5 is no longer needed. -/

structure TrailInvWith (orig : List Domain) (extra : List Atom)
    (cfg : SchedulerConfig leaf) : Prop where
  /-- the current branch's trail vocabulary at the extended pool -/
  branch : BranchTrailVocabularyAt (litPoolWith extra orig) cfg.branch
  /-- the current branch's learned database is extended-pool aligned -/
  db : DatabaseAlignedAt (litPoolWith extra orig) cfg.branch.learned
  /-- every saved checkpoint's trail vocabulary -/
  checkpoints : ∀ cp ∈ cfg.checkpoints,
    TrailVocabularyAt (litPoolWith extra orig) cp.trail
  /-- every RECORDED evidence payload is extended-pool aligned -/
  evidence : ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
    DatabaseAlignedAt (litPoolWith extra orig) ev.learned

/-- **THE ONE-STEP LAW OF THE JOINT INVARIANT** (the arm table of the real
dispatcher): every successor of a configuration satisfying `TrailInvWith`
satisfies it again. The jump arm PRODUCES the plan/asserting alignment from
the recorded site (the predecessor's own branch vocabulary + the R1
provenance), the checkpoint vocabulary from the invariant's checkpoint
component, and the restored database from `databaseAlignedAt_perform`; the
consume arm produces the resumed trail vocabulary from the pending head's
`PendingBacked`. No recording-site premise. -/
theorem trailInvWith_step {leaf : Assignment → Bool} {orig : List Domain}
    {extra : List Atom} {cfg cfg' : SchedulerConfig leaf}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) cfg.props)
    (horig : cfg.orig = orig)
    (hbr : ReachableState leaf orig cfg.branch)
    (hinv : TrailInvWith orig extra cfg)
    (hpend : ∀ f ∈ cfg.pending, PendingBacked orig f)
    (hreach : SchedulerReachable cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    TrailInvWith orig extra cfg' := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence resolved by `backjumpStep` (all arms clear)
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact
          { branch := stepChronologicalFallback_branchTrailVocabulary_at _ hinv.branch
            db := stepChronologicalFallback_halignDBAt _ hinv.db
            checkpoints := fun cp hcp => hinv.checkpoints cp hcp
            evidence := fun h => by
              rw [stepChronologicalFallback_conflict] at h
              cases h }
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact
              { branch := stepChronologicalFallback_branchTrailVocabulary_at _
                  hinv.branch
                db := stepChronologicalFallback_halignDBAt _ hinv.db
                checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
                evidence := fun h => by
                  rw [stepChronologicalFallback_conflict] at h
                  cases h }
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact
                  { branch := stepLocalExclude_branchTrailVocabulary_at _ _
                      hinv.branch
                    db := stepLocalExclude_halignDBAt ev.learned
                      (checkpointRegion cp) hinv.db (hinv.evidence hc)
                    checkpoints := fun cp' hcp' => hinv.checkpoints cp' hcp'
                    evidence := fun h => by
                      rw [stepLocalExclude_conflict] at h
                      cases h }
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hpm := planMatchesAnalysis_ofCheckpoint cp cfg.branch an
                have halignAn : ∀ q ∈ an.learned,
                    q.norm ∈ litPoolWith extra orig :=
                  recordedAnalysis_learned_poolAligned_at
                    (fun _ hl => litPoolWith_negate_norm_mem hl)
                    rfl hbr hreach hc ha hinv.branch
                have hplan : DatabaseAlignedAt (litPoolWith extra orig)
                    [(BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                      an.learned).learned] :=
                  databaseAlignedAt_singleton_of_clause
                    (by simpa only [hpm.1] using halignAn)
                have hass : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).asserting.norm ∈ litPoolWith extra orig := by
                  simpa only [hpm.2] using
                    recordedAnalysis_asserting_poolAligned_at hreach hc ha halignAn
                have hcpv : TrailVocabularyAt (litPoolWith extra orig)
                    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                      an.learned).checkpoint.trail :=
                  hinv.checkpoints cp (checkpointAt_mem hcp)
                have hperfDb : DatabaseAlignedAt (litPoolWith extra orig)
                    restored.learned :=
                  databaseAlignedAt_perform hvocab hinv.db hplan hp
                have hperfTr : TrailVocabularyAt (litPoolWith extra orig)
                    restored.trail :=
                  perform_trailVocabulary_at hvocab hinv.db hplan hcpv hass hp
                refine
                  { branch := ?_
                    db := ?_
                    checkpoints := ?_
                    evidence := ?_ }
                · show TrailVocabularyAt (litPoolWith extra orig) restored.trail
                  exact hperfTr
                · show DatabaseAlignedAt (litPoolWith extra orig)
                    (ev.learned ++ restored.learned)
                  exact databaseAlignedAt_append (hinv.evidence hc) hperfDb
                · intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                    (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                      an.learned) (ev := ev) (restored := restored)] at hcp'
                  exact hinv.checkpoints cp' (List.mem_filter.mp hcp').1
                · intro ev' h'
                  rw [stepLearnBackjumpAssert_conflict] at h'
                  cases h'
  · -- ROUTE 2: dead branch consumed (conflict cleared, checkpoints emptied)
    rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none =>
        simp only [consumeStep, hcons] at hsucc
        cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons
            cases hcons
        | cons f rest =>
            have hpb : PendingBacked orig f :=
              hpend f (by rw [hp]; exact List.mem_cons_self ..)
            have hbranch : BranchTrailVocabularyAt (litPoolWith extra orig)
                (resumePending orig cfg.branch f) :=
              resumePending_branchTrailVocabulary_at hpb
            have hdb' : DatabaseAlignedAt (litPoolWith extra orig)
                cfg'.branch.learned :=
              stepConsume_halignDBAt hcons hinv.db
            refine
              { branch := ?_
                db := hdb'
                checkpoints := ?_
                evidence := ?_ }
            · rw [stepConsume_branch hp hcons, horig]
              exact hbranch
            · intro cp hcp'
              have hck : cfg'.checkpoints = [] := by
                unfold LeanFzn.Solver.UIP.stepConsume at hcons
                rw [hp] at hcons
                simp only [Option.some.injEq] at hcons
                subst hcons
                rfl
              rw [hck] at hcp'
              cases hcp'
            · intro ev' h'
              rw [stepConsume_conflict hcons] at h'
              cases h'
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · -- propagation (clears the predecessor's none)
      rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      have hdl := deduction_literal_pooled_at hvocab hinv.db hd
      exact
        { branch := stepPropagate_branchTrailVocabulary_at hinv.branch hdl
          db := stepPropagate_halignDBAt d hinv.db
            (databaseAlignedAt_deduction_learned hvocab hd)
          checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
          evidence := fun h => by
            rw [stepPropagate_conflict, hconf] at h
            cases h }
    · -- guarded stable dispatch
      rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w =>
          simp only [hl, successor_sat] at hsucc
          cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame with
          | some p =>
              obtain ⟨l, v, vs, doms⟩ := p
              simp only [hl, hs] at hsucc
              split at hsucc
              · -- redundant-pin skip: branch, database and checkpoints unchanged
                rw [successor_decide] at hsucc
                cases hsucc
                exact
                  { branch := stepDecideSkip_branchTrailVocabulary_at v doms
                      hinv.branch
                    db := stepDecideSkip_halignDBAt v doms hinv.db
                    checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
                    evidence := fun h => by
                      rw [stepDecideSkip_conflict, hconf] at h
                      cases h }
              · -- fresh split: the pushed checkpoint is the PARENT snapshot
                rw [successor_decide] at hsucc
                cases hsucc
                have hsplit : splitData cfg.branch.frame = some (l, v, vs, doms) := hs
                refine
                  { branch := stepDecide_branchTrailVocabulary_at hinv.branch
                      (stepDecide_splitLiteral_pooled_at hbr hsplit)
                    db := stepDecide_halignDBAt v vs doms l hinv.db
                    checkpoints := ?_
                    evidence := fun h => by
                      rw [stepDecide_conflict, hconf] at h
                      cases h }
                intro cp hcp'
                have hck : (stepDecide cfg v vs doms l).checkpoints
                    = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
                rw [hck] at hcp'
                rcases List.mem_cons.mp hcp' with rfl | hcp'
                · show TrailVocabularyAt (litPoolWith extra orig) cfg.branch.trail
                  exact hinv.branch
                · exact hinv.checkpoints cp hcp'
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact
                { branch := stepLocalExclude_branchTrailVocabulary_at _ _
                    hinv.branch
                  db := stepLocalExclude_halignDBAt [] (branchRegion cfg) hinv.db
                    (databaseAlignedAt_nil _)
                  checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
                  evidence := fun h => by
                    rw [stepLocalExclude_conflict] at h
                    cases h }
    · -- recorded conflict dispatch
      rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact
            { branch := stepLocalExclude_branchTrailVocabulary_at _ _
                hinv.branch
              db := stepLocalExclude_halignDBAt learned (branchRegion cfg) hinv.db
                (databaseAlignedAt_terminalResult_conflict hvocab ht)
              checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
              evidence := fun h => by
                rw [stepLocalExclude_conflict] at h
                cases h }
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            -- THE RECORDING SITE: the branch vocabulary is the predecessor's
            -- (the recording arm leaves the branch unchanged)
            exact
              { branch := stepAnalyzeConflictCounted_branchTrailVocabulary_at
                  c0 learned _ hinv.branch
                db := stepAnalyzeConflictCounted_halignDBAt c0 learned _ hinv.db
                checkpoints := by
                  intro cp hcp'
                  rw [stepAnalyzeConflictCounted_checkpoints] at hcp'
                  exact hinv.checkpoints cp hcp'
                evidence := by
                  intro ev' h'
                  obtain ⟨-, hlearned, -⟩ :=
                    stepAnalyzeConflictCounted_evidence (cfg := cfg) (c := c0)
                      (learned := learned) h'
                  rw [hlearned]
                  exact databaseAlignedAt_terminalResult_conflict hvocab ht }
    · -- the local-exclusion terminal result
      rw [hsj] at hsucc
      rw [successor_localExclude] at hsucc
      cases hsucc
      exact
        { branch := stepLocalExclude_branchTrailVocabulary_at _ _ hinv.branch
          db := stepLocalExclude_halignDBAt learned (branchRegion cfg) hinv.db
            (databaseAlignedAt_terminalResult_localExcluded hvocab ht)
          checkpoints := fun cp hcp' => hinv.checkpoints cp hcp'
          evidence := fun h => by
            rw [stepLocalExclude_conflict] at h
            cases h }

/-- **THE RUN-WIDE PRODUCER (hrec DISCHARGED)**: along a supported run, the
joint extended-pool invariant holds at EVERY state — from the emission
vocabulary, the branch reachability and the box typing ONLY. The
recording-site premise `hrec` (`Proofs/TrailVocabularyProducers.lean` §5)
is discharged by the forward maintenance: the recording arm's successor
inherits the predecessor's branch vocabulary. -/
theorem trailInvWith_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {extra : List Atom}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      TrailInvWith orig extra cfg := by
  intro cfg hreach
  induction hreach with
  | init =>
      refine
        { branch := ?_
          db := databaseAlignedAt_nil _
          checkpoints := ?_
          evidence := ?_ }
      · intro e he
        simp [SchedulerConfig.init, BranchState.init] at he
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst hcp
        intro e he
        simp [rootCheckpoint] at he
      · intro ev h
        simp [SchedulerConfig.init] at h
  | step hpre hsucc ih =>
      exact trailInvWith_step
        (by rw [SupportedReach.props_eq hpre]; exact hvocab)
        (SupportedReach.orig_eq hpre) (hbr hpre) ih
        (pendingSideInv_of_premises hshape hbr hpre).pending
        (SupportedReach.reachable hpre) hsucc

/-! ## §4 The exports -/

/-- The branch-vocabulary component at an arbitrary extended pool. -/
theorem branchTrailVocabularyAt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {extra : List Atom}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabularyAt (litPoolWith extra orig) cfg.branch :=
  fun hreach => (trailInvWith_of_supportedRun hvocab hbr hshape hreach).branch

/-- The database-alignment component at an arbitrary extended pool. -/
theorem halignDBAt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {extra : List Atom}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPoolWith extra orig :=
  fun hreach => (trailInvWith_of_supportedRun hvocab hbr hshape hreach).db

/-- The checkpoint-trail-vocabulary component at an arbitrary extended
pool (the input `restoreNarrow_trailVocabulary_at`/C2's checkpoint
consumers need). -/
theorem checkpointTrailVocabularyAt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {extra : List Atom}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ cp ∈ cfg.checkpoints,
        TrailVocabularyAt (litPoolWith extra orig) cp.trail :=
  fun hreach => (trailInvWith_of_supportedRun hvocab hbr hshape hreach).checkpoints

/-- The recorded-evidence payload alignment at an arbitrary extended pool. -/
theorem evidencePayload_alignedAt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {extra : List Atom}
    (hvocab : EmissionVocabularyAt (litPoolWith extra orig) props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        DatabaseAlignedAt (litPoolWith extra orig) ev.learned :=
  fun hreach => (trailInvWith_of_supportedRun hvocab hbr hshape hreach).evidence

/-! ### §4a The unit-route instantiation (`litPoolExt`)

`extra := constraintAtomPool dcs` and `hvocab :=
emissionVocabularyAt_litPoolExt hSupp` (the landed premise-free producer). -/

/-- **THE UNIT-ROUTE RUN INVARIANT AT `litPoolExt`** (hrec discharged):
every configuration of a `hprops`/`hSupp`-supported run carries the joint
extended-pool invariant. -/
theorem trailInv_litPoolExt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      TrailInvWith orig (constraintAtomPool dcs) cfg :=
  trailInvWith_of_supportedRun
    (by rw [hprops]; exact emissionVocabularyAt_litPoolExt hSupp) hbr hshape

/-- **THE C1 SITE-FORM TRAIL VOCABULARY AT `litPoolExt`, `hrec`
DISCHARGED**: the replacement for
`branchTrailVocabulary_supportedRun_evidenceSites` with the recording-site
premise removed (the forward invariant reaches the recording arm's
successor through the predecessor). -/
theorem branchTrailVocabulary_evidenceSites_litPoolExt_of_supportedRun
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        BranchTrailVocabularyAt (litPoolExt orig dcs) cfg.branch := by
  intro cfg hreach ev hconf
  exact (trailInv_litPoolExt_of_supportedRun hprops hSupp hbr hshape hreach).branch

/-- The universal (not site-restricted) form of the same producer. -/
theorem branchTrailVocabulary_at_litPoolExt_of_supportedRun
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabularyAt (litPoolExt orig dcs) cfg.branch :=
  fun hreach => (trailInv_litPoolExt_of_supportedRun hprops hSupp hbr hshape hreach).branch

/-- **THE C1 EXTENDED-POOL `halignDB` PRODUCER**: the unit-route database
alignment at `litPoolExt orig dcs`, from `hprops`/`hSupp`, branch
reachability and box typing — NO pool-membership assumption. -/
theorem halignDB_litPoolExt_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPoolExt orig dcs :=
  fun hreach => (trailInv_litPoolExt_of_supportedRun hprops hSupp hbr hshape hreach).db

/-- The unit-route checkpoint trail vocabulary at `litPoolExt`. -/
theorem checkpointTrailVocabulary_litPoolExt_of_supportedRun
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ cp ∈ cfg.checkpoints,
        TrailVocabularyAt (litPoolExt orig dcs) cp.trail :=
  fun hreach =>
    (trailInv_litPoolExt_of_supportedRun hprops hSupp hbr hshape hreach).checkpoints

/-- The unit-route recorded-evidence payload alignment at `litPoolExt`. -/
theorem evidencePayload_aligned_litPoolExt_of_supportedRun
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        DatabaseAlignedAt (litPoolExt orig dcs) ev.learned :=
  fun hreach =>
    (trailInv_litPoolExt_of_supportedRun hprops hSupp hbr hshape hreach).evidence

/-! ### §4b The `litPool`-keyed instantiation (`extra := []`)

This is route (i) at the ORIGINAL pool: given the honest `hvocab` input
(not provable for the unit kit — the §4 kernel witness — but the exact
premise the earlier site-form producer took), the recording-site premise is
discharged here too. -/

/-- `litPoolWith [] orig` IS the landed `litPool orig` (the empty extras). -/
theorem litPoolWith_nil (orig : List Domain) : litPoolWith [] orig = litPool orig := by
  simp [litPoolWith, atomPoolWith, atomExtras, litPool]

/-- **THE `litPool`-KEYED RUN-WIDE TRAIL VOCABULARY, `hrec` DISCHARGED**:
along a supported run with the emission vocabulary at the box's own pool,
every state's branch carries the landed `TrailVocabulary` — no
recording-site premise. -/
theorem branchTrailVocabulary_supportedRun_allStates {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch := by
  intro cfg hreach
  have h := (trailInvWith_of_supportedRun (extra := [])
    (by rw [litPoolWith_nil]; exact unitEmissionVocabulary_iff_at.mp hvocab)
    hbr hshape hreach).branch
  rwa [litPoolWith_nil] at h

/-- The site-form of the same producer (the exact conclusion of
`branchTrailVocabulary_supportedRun_evidenceSites`, with `hrec` gone). -/
theorem branchTrailVocabulary_supportedRun_evidenceSites_allStates
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        BranchTrailVocabulary orig cfg.branch := by
  intro cfg hreach ev hconf
  exact branchTrailVocabulary_supportedRun_allStates hvocab hbr hshape hreach

/-- **THE `litPool`-KEYED `halignDB` PRODUCER**: the landed
`halignDB_of_supportedRun` conclusion from `hvocab`, branch reachability and
box typing — its `htrail` premise is DISCHARGED here. -/
theorem halignDB_supportedRun_allStates {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig := by
  intro cfg hreach
  have h := (trailInvWith_of_supportedRun (extra := [])
    (by rw [litPoolWith_nil]; exact unitEmissionVocabulary_iff_at.mp hvocab)
    hbr hshape hreach).db
  rwa [litPoolWith_nil] at h

/-- The checkpoint-side component at the box's own pool (also `hrec`-free). -/
theorem checkpointTrailVocabulary_supportedRun_allStates
    {leaf : Assignment → Bool} {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ cp ∈ cfg.checkpoints, TrailVocabulary orig cp.trail := by
  intro cfg hreach
  have h := (trailInvWith_of_supportedRun (extra := [])
    (by rw [litPoolWith_nil]; exact unitEmissionVocabulary_iff_at.mp hvocab)
    hbr hshape hreach).checkpoints
  intro cp hcp
  have h' := h cp hcp
  rwa [litPoolWith_nil] at h'

/-! ### §4c The canonical-resume recorded-analysis composition at any
extended pool

The consume route's evidence-site chain (`canonical resume` →
`recordedAnalysis_learned_poolAligned`): the resumed branch's vocabulary is
the canonical trail's (`resumePending_branchTrailVocabulary_at`), so the
recorded analysis's learned clause is extended-pool aligned at the resumed
site. This is the extended-pool form of
`recordedAnalysis_learned_poolAligned_of_resumePending`
(`Proofs/CanonicalTrailVocabulary.lean` §3). -/

theorem recordedAnalysis_learned_poolAligned_at_resumePending
    {leaf : Assignment → Bool} {orig : List Domain} {extra : List Atom}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf} {f : BranchFrame}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hpb : PendingBacked orig f) (hb : cfg.branch = resumePending orig bs f)
    (hreach : ReachableState leaf orig cfg.branch)
    (hcfg : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hana : ev.analysis = some an) :
    ∀ q ∈ an.learned, q.norm ∈ litPoolWith extra orig := by
  have hbr' : ReachableState leaf orig (resumePending orig bs f) := hb ▸ hreach
  have htr : BranchTrailVocabularyAt (litPoolWith extra orig)
      (resumePending orig bs f) :=
    resumePending_branchTrailVocabulary_at (bs := bs) hpb
  exact recordedAnalysis_learned_poolAligned_at
    (fun _ hl => litPoolWith_negate_norm_mem hl) hb hbr' hcfg hconf hana htr

end LeanFzn.Solver.UIP
