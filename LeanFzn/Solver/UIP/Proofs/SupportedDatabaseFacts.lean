/-
File: LeanFzn/Solver/UIP/Proofs/SupportedDatabaseFacts.lean

Purpose: C1's analysis-site pool-alignment lemmas:

  §1 `normFalsified_learned_poolAligned` — a clause whose literals all
     carry recorded NORMALIZED falsifiers on a trail-vocabulary trail has
     every normalized literal pooled (the negation/normalization algebra:
     `Literal.negate_norm_eq` + `norm_norm` + `Literal.negate_negate` +
     `litPool_negate_norm_mem`).
  §2 `recordedAnalysis_learned_poolAligned` — the recorded analysis's
     learned clause is pool-aligned at the recorded site, composing §1
     with the landed `recordedAnalysis_normFalsified`.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedDatabaseFacts` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerFalsified
import LeanFzn.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Solver.UIP.Proofs.SchedulerRank
import LeanFzn.Solver.UIP.Proofs.DomExplained
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- **C1 POOL ALIGNMENT FOR NORM-FALSIFIED CLAUSES**: if every literal of
`c` has a recorded normalized falsifier on the trail and the trail's
entries normalize into the pool, then every normalized literal of `c` is
pooled. -/
theorem normFalsified_learned_poolAligned {orig : List Domain}
    {trail : List TrailEntry} {c : Clause}
    (htrail : TrailVocabulary orig trail)
    (hfals : ∀ q ∈ c, ∃ e ∈ trail, e.literal = (q.negate).norm) :
    ∀ q ∈ c, q.norm ∈ litPool orig := by
  intro q hq
  obtain ⟨e, he, heq⟩ := hfals q hq
  have h1 : ((q.negate).norm).norm ∈ litPool orig := by
    have := htrail e he
    rwa [heq] at this
  rw [norm_norm] at h1
  have h2 := litPool_negate_norm_mem (l := q.negate) h1
  rwa [Literal.negate_negate] at h2

/-- **THE TERMINAL-CONFLICT EVENT BRIDGE**: a terminal `.conflict` result
exposes the raw pruning event, so the scan-stability lemmas apply at
recorded sites. -/
theorem nextPruningEvent_eq_of_terminalResult_conflict {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {s : BranchState leaf} {cs learned : List Clause}
    (h : terminalResult original props bs = .conflict s cs learned) :
    nextPruningEvent original props bs.frame bs.learned = .conflict cs := by
  rw [terminalResult] at h
  split at h
  · cases h
  · rename_i cs' hprune
    cases h
    exact hprune
  · -- the implied case classifies through the inner filterFrame match:
    -- neither branch is a conflict
    split at h
    · cases h
    · cases h

/-- **THE C1 ANALYSIS-CLAUSE ALIGNMENT**: at a recorded-evidence site of a
reachable run whose branch carries the trail vocabulary, the analysis's
learned clause is pool-aligned. This is the successor-DB half of
`halignDB` (the jump inserts `an.learned`). -/
theorem recordedAnalysis_learned_poolAligned {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hcfg : SchedulerReachable cfg)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (htrail : BranchTrailVocabulary orig bs) :
    ∀ q ∈ an.learned, q.norm ∈ litPool orig :=
  normFalsified_learned_poolAligned htrail
    (recordedAnalysis_normFalsified hb hreach hcfg hconf hana)

/-! ## §3 The C1 database-alignment algebra and the per-arm laws -/

/-- Database-side literal-pool alignment (the `halignDB` field shape):
every literal of every learned clause normalizes into the box's pool. -/
def DatabaseAligned (orig : List Domain) (db : List Clause) : Prop :=
  ∀ c ∈ db, ∀ q ∈ c, q.norm ∈ litPool orig

theorem databaseAligned_nil (orig : List Domain) : DatabaseAligned orig [] :=
  fun _ hc => absurd hc (List.not_mem_nil)

theorem databaseAligned_append {orig : List Domain} {db₁ db₂ : List Clause}
    (h₁ : DatabaseAligned orig db₁) (h₂ : DatabaseAligned orig db₂) :
    DatabaseAligned orig (db₁ ++ db₂) := by
  intro c hc q hq
  rcases List.mem_append.mp hc with hc | hc
  · exact h₁ c hc q hq
  · exact h₂ c hc q hq

theorem databaseAligned_of_sub {orig : List Domain} {db db' : List Clause}
    (hsub : ∀ c ∈ db, c ∈ db') (h : DatabaseAligned orig db') :
    DatabaseAligned orig db :=
  fun c hc q hq => h c (hsub c hc) q hq

/-- The alignment is a per-clause property: pointwise equality transfers. -/
theorem databaseAligned_of_eq {orig : List Domain} {db db' : List Clause}
    (heq : db = db') (h : DatabaseAligned orig db') :
    DatabaseAligned orig db :=
  heq ▸ h

/-! ## §4 The per-arm `halignDB` preservation laws

Every scheduler arm either keeps the learned database, concatenates a
fresh payload, or takes the successor's database from a restored state —
all rfl-level shape facts already proved in the step layers. The
payload producers (propagator reasons, analysis clauses, closure
payloads) live with their families; these laws are the wiring. -/

theorem stepDecide_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (v : Value) (vs : Domain)
    (doms : List Domain) (l : Literal)
    (h : DatabaseAligned orig cfg.branch.learned) :
    DatabaseAligned orig (stepDecide cfg v vs doms l).branch.learned := by
  rwa [stepDecide_learned]

theorem stepDecideSkip_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (v : Value) (doms : List Domain)
    (h : DatabaseAligned orig cfg.branch.learned) :
    DatabaseAligned orig (stepDecideSkip cfg v doms).branch.learned := by
  show DatabaseAligned orig cfg.branch.learned
  exact h

theorem stepAnalyzeConflictCounted_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (c : Clause) (learned : List Clause)
    (n : Nat) (h : DatabaseAligned orig cfg.branch.learned) :
    DatabaseAligned orig
      (stepAnalyzeConflictCounted cfg c learned n).branch.learned := by
  rwa [stepAnalyzeConflictCounted_branch]

theorem stepChronologicalFallback_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (r : DeadRegion)
    (h : DatabaseAligned orig cfg.branch.learned) :
    DatabaseAligned orig (stepChronologicalFallback cfg r).branch.learned := by
  rwa [P3.stepChronologicalFallback_learned_eq]

theorem stepConsume_halignDB {orig : List Domain}
    {cfg next : SchedulerConfig leaf} (hstep : stepConsume cfg = some next)
    (h : DatabaseAligned orig cfg.branch.learned) :
    DatabaseAligned orig next.branch.learned := by
  rwa [P3.stepConsume_learned hstep]

theorem stepPropagate_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (d : ProductiveDeduction leaf cfg.branch)
    (h : DatabaseAligned orig cfg.branch.learned)
    (hpay : DatabaseAligned orig d.learned) :
    DatabaseAligned orig (stepPropagate cfg d).branch.learned := by
  rw [P3.stepPropagate_learned_eq]
  exact databaseAligned_append hpay h

theorem stepLocalExclude_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (learned : List Clause) (r : DeadRegion)
    (h : DatabaseAligned orig cfg.branch.learned)
    (hpay : DatabaseAligned orig learned) :
    DatabaseAligned orig (stepLocalExclude cfg learned r).branch.learned := by
  rw [P3.stepLocalExclude_learned_eq]
  exact databaseAligned_append hpay h

theorem stepLearnBackjumpAssert_halignDB {orig : List Domain}
    {cfg : SchedulerConfig leaf} (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf)
    (hpay : DatabaseAligned orig ev.learned)
    (hrest : DatabaseAligned orig restored.learned) :
    DatabaseAligned orig
      (stepLearnBackjumpAssert cfg p ev restored).branch.learned := by
  rw [stepLearnBackjumpAssert_learned]
  exact databaseAligned_append hpay hrest

/-! ## §5 The unit-emission vocabulary and the payload producers (C1)

`UnitEmissionVocabulary` is the payload-side discipline of the registered
propagators relative to a FIXED box: every implied explanation is a
normalized UNIT clause `[q]` whose literal `q` is pooled, and every
conflict explanation is empty or such a unit. This is exactly the shape
`DatabaseAligned` consumes, and it is the POOL-STRENGTHENED companion of
`UnitRunProfile` (`unitEmissionVocabulary_runProfile` forgets the pool
half).

HONESTY NOTE (why the pool half is a separate input). `UnitRunProfile`
alone does NOT imply pool membership: the emitted constants are the
constraint's own (`leConstHi i c` emits `posLe i c` for an arbitrary `c`),
so a per-family producer must consume a constraint-side representative
condition, or the pool of `SchedulerVocabulary` must be extended by the
problem's constants. That producer is C2's residual (see the §7 ledger);
nothing here assumes it. -/

/-- The propagator kit's emission vocabulary relative to a box: implied
reasons are normalized units whose literal IS the pivot and is pooled;
conflicts are empty or such units. -/
def UnitEmissionVocabulary (orig : List Domain) (props : List Propagator) : Prop :=
  (∀ p ∈ props, ∀ st l r, p.run st = .implied l r →
    ∃ q : Literal, r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ litPool orig) ∧
  (∀ p ∈ props, ∀ st c, p.run st = .conflict c →
    c = [] ∨ ∃ q : Literal, c = [q] ∧ q = q.norm ∧ q.norm ∈ litPool orig)

/-- The emission vocabulary forgets the pool half: it is a `UnitRunProfile`
(so every `UnitRunProfile` consumer keeps working unchanged). -/
theorem unitEmissionVocabulary_runProfile {orig : List Domain}
    {props : List Propagator} (h : UnitEmissionVocabulary orig props) :
    UnitRunProfile props := by
  constructor
  · intro p hp st l r hr
    obtain ⟨q, hq, -, hqn, -⟩ := h.1 p hp st l r hr
    exact ⟨q, hq, hqn⟩
  · intro p hp st c hc
    rcases h.2 p hp st c hc with hnil | ⟨q, hq, hqn, -⟩
    · exact Or.inl hnil
    · exact Or.inr ⟨q, hq, hqn⟩

/-- A database holding the single normalized unit clause `[q]` is aligned. -/
theorem databaseAligned_of_unit {orig : List Domain} {c : Clause}
    (h : ∃ q : Literal, c = [q] ∧ q.norm ∈ litPool orig) :
    DatabaseAligned orig [c] := by
  obtain ⟨q, rfl, hq⟩ := h
  intro c' hc' q' hq'
  have hc1 : c' = [q] := List.mem_singleton.mp hc'
  have hq1 : q' ∈ ([q] : Clause) := by rwa [hc1] at hq'
  have hq2 : q' = q := List.mem_singleton.mp hq1
  subst hq2
  exact hq

/-- A freshness-filtered unit payload (`if b then [c] else []`, the shape of
both the deduction and the conflict payloads) is aligned from the unit
evidence of `c` — the condition is irrelevant. -/
theorem databaseAligned_if_singleton {orig : List Domain} {c : Clause} {b : Bool}
    (hunit : ∃ q : Literal, c = [q] ∧ q.norm ∈ litPool orig) :
    DatabaseAligned orig (if b then [c] else []) := by
  cases b with
  | false => simpa using databaseAligned_nil (orig := orig)
  | true => simpa using databaseAligned_of_unit hunit

/-- **PROPAGATE-ARM PAYLOAD PRODUCER**: the learned payload of a selected
deduction is aligned. Database-sourced events carry `leanReason = false`
(`scanDatabase_implied_facts`), so the payload is either empty or the
propagator kit's unit reason — the emission vocabulary covers it. -/
theorem databaseAligned_deduction_learned {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    (hvocab : UnitEmissionVocabulary orig props)
    (hd : explainedDeduction original props bs = some d) :
    DatabaseAligned orig d.learned := by
  obtain ⟨c, lr, fl, hev, -, hlearned⟩ := explainedDeduction_learned_shape hd
  rw [hlearned]
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨-, hlr, -⟩ := scanDatabase_implied_facts hsrc
    rw [hlr]
    rw [if_neg (by simp)]
    exact databaseAligned_nil orig
  · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ := scanPropagators_implied_facts hprop
    obtain ⟨q, hq, -, -, hqpool⟩ :=
      hvocab.1 p hpm (frameState bs.frame) d.literal r hrun
    exact databaseAligned_if_singleton ⟨q, by rw [hcl, hq], hqpool⟩

/-- **LOCALEXCLUDE / EVIDENCE PAYLOAD PRODUCER**: the freshness-filtered
conflict payload (`cs.filter …`, the `learned` field of the recorded
evidence and of the local-exclusion arm) is aligned. A database conflict
carries `[]`; a propagator conflict carries its unit or nothing. -/
theorem databaseAligned_conflict_learned {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {cs : List Clause}
    (hvocab : UnitEmissionVocabulary orig props)
    (hev : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    DatabaseAligned orig (cs.filter fun c => !(bs.learned.contains c)) := by
  rcases nextPruningEvent_conflict_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨-, -, -, hcs⟩ := scanDatabase_conflict_facts hsrc
    rw [hcs, List.filter_nil]
    exact databaseAligned_nil orig
  · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
    rw [hcs]
    rcases hvocab.2 p hpm (frameState bs.frame) c hrun with hnil | ⟨q, hcq, -, hqpool⟩
    · rw [hnil]
      show DatabaseAligned orig
        (List.filter (fun c => !(bs.learned.contains c)) [])
      rw [List.filter_nil]
      exact databaseAligned_nil orig
    · by_cases hempty : c.isEmpty = true
      · rw [hempty]
        show DatabaseAligned orig
          (List.filter (fun c => !(bs.learned.contains c)) [])
        rw [List.filter_nil]
        exact databaseAligned_nil orig
      · rw [if_neg hempty]
        exact databaseAligned_of_sub (fun c' hc' => (List.mem_filter.mp hc').1)
          (databaseAligned_of_unit ⟨q, hcq, hqpool⟩)

/-- The terminal-conflict payload of `terminalResult` is aligned (the
recorded-evidence `learned` field at the recording arm). -/
theorem databaseAligned_terminalResult_conflict {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs bs' : BranchState leaf} {cs learned : List Clause}
    (hvocab : UnitEmissionVocabulary orig props)
    (ht : terminalResult original props bs = .conflict bs' cs learned) :
    DatabaseAligned orig learned := by
  rw [terminalResult] at ht
  split at ht
  · cases ht
  · rename_i cs' hev
    cases ht
    exact databaseAligned_conflict_learned hvocab hev
  · split at ht <;> cases ht

/-- The terminal `localExcluded` payload (the failed-filter arm's learned
list) is aligned: it is the freshness-filtered unit reason of the implied
event that the failing `filterFrame` classified. -/
theorem databaseAligned_terminalResult_localExcluded {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs bs' : BranchState leaf} {lit : Option Literal} {reason : Option Clause}
    {learned : List Clause}
    (hvocab : UnitEmissionVocabulary orig props)
    (ht : terminalResult original props bs =
      .localExcluded bs' lit reason learned) :
    DatabaseAligned orig learned := by
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
        exact databaseAligned_nil orig
      · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ := scanPropagators_implied_facts hprop
        obtain ⟨q, hq, -, -, hqpool⟩ := hvocab.1 p hpm (frameState bs.frame) l r hrun
        exact databaseAligned_if_singleton ⟨q, by rw [hcl, hq], hqpool⟩
    · cases ht

/-- **CLOSURE MAINTENANCE**: the explained closure keeps the database
aligned (the same `Frame.mass` fuel induction as
`unitLearned_explainedClosure`); the closure learns only selected
deductions' payloads, never on a conflict. -/
theorem databaseAligned_explainedClosure {leaf : Assignment → Bool}
    (original : List Clause) (props : List Propagator) (bs : BranchState leaf)
    {orig : List Domain} (hvocab : UnitEmissionVocabulary orig props)
    (h : DatabaseAligned orig bs.learned) :
    DatabaseAligned orig (explainedClosure original props bs).learned := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → DatabaseAligned orig bs.learned →
      DatabaseAligned orig (explainedClosure original props bs).learned from
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
        have hpay := databaseAligned_deduction_learned hvocab hd
        have hnew : DatabaseAligned orig
            (narrowState bs d.frame d.literal d.reason d.learned).learned := by
          show DatabaseAligned orig (d.learned ++ bs.learned)
          exact databaseAligned_append hpay h
        refine ih (narrowState bs d.frame d.literal d.reason d.learned) ?_ hnew
        have hdec := d.decreases
        simp only [narrowState] at hdec ⊢
        omega

/-- **JUMP RESTORED-DATABASE PRODUCER**: the `perform` result's database is
aligned from the pre-jump alignment, the plan clause's alignment
(`recordedAnalysis_learned_poolAligned` at the site) and the emission
vocabulary (the closure's own learning during restoration). -/
theorem databaseAligned_perform {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hvocab : UnitEmissionVocabulary orig props)
    (hdb : DatabaseAligned orig bs.learned)
    (hplan : DatabaseAligned orig [p.learned])
    (hperf : p.perform bs original props = some restored) :
    DatabaseAligned orig restored.learned := by
  unfold BackjumpPlan.perform at hperf
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at hperf
      cases hperf
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at hperf
      rw [← hperf]
      refine databaseAligned_explainedClosure original props s hvocab ?_
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · cases hr
        show DatabaseAligned orig (p.learned :: bs.learned)
        exact databaseAligned_append hplan hdb

/-- A single-clause database is aligned from its clause's pointwise
alignment (the plan's learned clause is a `Clause`, i.e. ONE clause). -/
theorem databaseAligned_singleton_of_clause {orig : List Domain} {c : Clause}
    (h : ∀ q ∈ c, q.norm ∈ litPool orig) : DatabaseAligned orig [c] := by
  intro c' hc' q hq
  have hc'e : c' = c := List.mem_singleton.mp hc'
  subst hc'e
  exact h q hq

/-! ## §6 The run-level `halignDB`

The one-step law over the REAL dispatch (the `C2d` arm table), then the
two run inductions: `SupportedReach` (self-indexed, C2/P5's chain) and raw
`SchedulerReachable` (self-`orig`, the D1/F1 `CompiledPhasePremises`
shape). Both produce the JOINT invariant (aligned branch database ∧ aligned
recorded-evidence payload); the local-exclusion/fallback arm reads the
evidence payload produced at its own recording site — no universal
conflict-state claim of any kind. -/

/-- **THE ONE-STEP LAW**: every real dispatcher successor of a configuration
carrying the four site facts (alignment, evidence alignment, branch
reachability, trail vocabulary) satisfies the joint database invariant.
All payloads are PRODUCED (deduction/conflict/localExcluded/vocabulary);
`hbr`/`htrail` are the analysis-clause site inputs (see §7). -/
theorem databaseAlignedStep {leaf : Assignment → Bool}
    {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (hvocab : UnitEmissionVocabulary orig cfg.props)
    (hdb : DatabaseAligned orig cfg.branch.learned)
    (hevdb : ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
      DatabaseAligned orig ev.learned)
    (hbr : ReachableState leaf orig cfg.branch)
    (htrail : ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
      BranchTrailVocabulary orig cfg.branch)
    (hreach : SchedulerReachable cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    DatabaseAligned orig cfg'.branch.learned ∧
      (∀ {ev : ConflictEvidence}, cfg'.conflict = some ev →
        DatabaseAligned orig ev.learned) := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence resolved by `backjumpStep`
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact ⟨by rw [P3.stepChronologicalFallback_learned_eq]; exact hdb,
          fun h => by rw [stepChronologicalFallback_conflict] at h; cases h⟩
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact ⟨by rw [P3.stepChronologicalFallback_learned_eq]; exact hdb,
              fun h => by rw [stepChronologicalFallback_conflict] at h; cases h⟩
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact ⟨stepLocalExclude_halignDB ev.learned (checkpointRegion cp)
                    hdb (hevdb hc),
                  fun h => by rw [stepLocalExclude_conflict] at h; cases h⟩
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hpm := planMatchesAnalysis_ofCheckpoint cp cfg.branch an
                have hplan : DatabaseAligned orig
                    [(BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                      an.learned).learned] :=
                  databaseAligned_singleton_of_clause (by
                    simpa only [hpm.1] using
                      (recordedAnalysis_learned_poolAligned (bs := cfg.branch) rfl
                        hbr hreach hc ha (htrail hc) :
                          ∀ q ∈ an.learned, q.norm ∈ litPool orig))
                have hrestored : DatabaseAligned orig restored.learned :=
                  databaseAligned_perform hvocab hdb hplan hp
                exact ⟨stepLearnBackjumpAssert_halignDB _ ev restored
                    (hevdb hc) hrestored,
                  fun h => by rw [stepLearnBackjumpAssert_conflict] at h; cases h⟩
  · -- ROUTE 2: dead branch consumed
    rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none =>
        simp only [consumeStep, hcons] at hsucc
        cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact ⟨stepConsume_halignDB hcons hdb,
          fun h => by rw [stepConsume_conflict hcons] at h; cases h⟩
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      exact ⟨stepPropagate_halignDB d hdb
          (databaseAligned_deduction_learned hvocab hd),
        fun h => by rw [stepPropagate_conflict, hconf] at h; cases h⟩
    · rw [hsj] at hsucc
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
              · rw [successor_decide] at hsucc
                cases hsucc
                exact ⟨stepDecideSkip_halignDB v doms hdb,
                  fun h => by rw [stepDecideSkip_conflict, hconf] at h; cases h⟩
              · rw [successor_decide] at hsucc
                cases hsucc
                exact ⟨stepDecide_halignDB v vs doms l hdb,
                  fun h => by rw [stepDecide_conflict, hconf] at h; cases h⟩
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact ⟨stepLocalExclude_halignDB [] (branchRegion cfg) hdb
                  (databaseAligned_nil orig),
                fun h => by rw [stepLocalExclude_conflict] at h; cases h⟩
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact ⟨stepLocalExclude_halignDB learned (branchRegion cfg) hdb
              (databaseAligned_terminalResult_conflict hvocab ht),
            fun h => by rw [stepLocalExclude_conflict] at h; cases h⟩
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            exact ⟨stepAnalyzeConflictCounted_halignDB c0 learned _ hdb,
              fun h => by
                obtain ⟨-, hlearned, -⟩ :=
                  stepAnalyzeConflictCounted_evidence (cfg := cfg) (c := c0)
                    (learned := learned) h
                rw [hlearned]
                exact databaseAligned_terminalResult_conflict hvocab ht⟩
    · rw [hsj] at hsucc
      rw [successor_localExclude] at hsucc
      cases hsucc
      exact ⟨stepLocalExclude_halignDB learned (branchRegion cfg) hdb
          (databaseAligned_terminalResult_localExcluded hvocab ht),
        fun h => by rw [stepLocalExclude_conflict] at h; cases h⟩

/-- **SUPPORTED-RUN JOINT INDUCTION** (self-indexed, the C2/P5 chain):
along exact `SupportedReach` execution, the branch database and every
recorded-evidence payload stay aligned — from the emission vocabulary and
the two per-state site inputs. -/
theorem databaseAlignedAndEvidence_of_supportedRun {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      DatabaseAligned orig cfg.branch.learned ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          DatabaseAligned orig ev.learned) := by
  intro cfg hreach
  induction hreach with
  | init =>
      refine ⟨databaseAligned_nil orig, ?_⟩
      intro ev h
      simp [SchedulerConfig.init] at h
  | step hpre hsucc ih =>
      exact databaseAlignedStep
        (by rw [(SupportedReach.triple_eq hpre).2.2]; exact hvocab)
        ih.1 ih.2 (hbr hpre) (htrail hpre) (SupportedReach.reachable hpre) hsucc

/-- **THE C1 RUN-LEVEL `halignDB`** (the field shape of
`SupportedPhasePremises.halignDB` / `supportedPhaseProgressSorted_of_premises`). -/
theorem halignDB_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig :=
  fun hreach =>
    (databaseAlignedAndEvidence_of_supportedRun hvocab hbr htrail hreach).1

/-- **RAW-REACHABILITY JOINT INDUCTION** (self-`orig`, the D1/F1
`CompiledPhasePremises` shape): same invariant along arbitrary reachable
execution, with the pool read at each configuration's own box. -/
theorem databaseAlignedAndEvidence_of_reachable {leaf : Assignment → Bool}
    (hvocab : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      UnitEmissionVocabulary cfg.orig cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableState leaf cfg.orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        BranchTrailVocabulary cfg.orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      DatabaseAligned cfg.orig cfg.branch.learned ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          DatabaseAligned cfg.orig ev.learned) := by
  intro cfg hreach
  induction hreach with
  | init orig original props =>
      refine ⟨?_, ?_⟩
      · show DatabaseAligned orig []
        exact databaseAligned_nil orig
      · intro ev h
        simp [SchedulerConfig.init] at h
  | step hnext hsucc hpre ih =>
      rw [W1.schedulerNext_succ_orig (hnext ▸ hsucc)]
      exact databaseAlignedStep (hvocab hpre) ih.1 ih.2 (hbr hpre)
        (htrail hpre) hpre (hnext ▸ hsucc)

/-- **THE RAW `halignDB`** (the field shape of `CompiledPhasePremises.halignDB`). -/
theorem halignDB_of_reachable {leaf : Assignment → Bool}
    (hvocab : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      UnitEmissionVocabulary cfg.orig cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableState leaf cfg.orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        BranchTrailVocabulary cfg.orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool cfg.orig :=
  fun hreach =>
    (databaseAlignedAndEvidence_of_reachable hvocab hbr htrail hreach).1

/-! ## §7 The C2 input ledger (exact residual producers)

`halignDB_of_supportedRun` / `halignDB_of_reachable` consume exactly four
inputs; C2 must discharge them (or take them from their owners):

1. `UnitEmissionVocabulary orig props` — the pooled-emission vocabulary of
   the registered kit. RESIDUAL (owner: C2 / pool): `unitRunProfile_proved`
   supplies the unit shape; the POOL half needs a per-family producer from a
   constraint-side representative condition (each emitted threshold/value
   atom must be a pool atom), or an extension of `SchedulerVocabulary`'s
   `threshPool`/`litPool` by the problem's constants (foreign file,
   `SchedulerVocabulary.lean`). `supported_conflict_clause_unit`
   (`Proofs/DomExplained.lean`, N1) supplies the CONFLICT half's shape
   unconditionally; only its pool conjunct is residual.
2. `hbr` — `ReachableState leaf orig cfg.branch` along the run; producer
   `supportedHbr_of_gates` (J1, `Proofs/SupportedArms.lean` §2) on the
   supported run / B4's `hbr_of_reachPreserve` on the raw run.
3. `htrail` — `BranchTrailVocabulary` at CONFLICT-EVIDENCE SITES only (no
   universal per-state claim): root `branchTrailVocabulary_init`, the
   landed `stepPropagate/stepDecide_branchTrailVocabulary` arm laws, the
   new `resumePending_branchTrailVocabulary` (canonical resume route,
   `Proofs/CanonicalTrailVocabulary.lean`) and `restoreLevel`-filtering for
   the sibling route; the JUMP arm's forward maintenance (the closure's own
   narrow entries, `relaxed by implied_literal_pooled`-style producers) is
   the remaining arm-law residual (C1/J1).
4. `hdb`-site inputs — unchanged and already produced in `ScanStability.lean`
   §4: `databaseUnfalsified_of_reachable_recorded` consumes `hbr` (2) and
   `hinhab : ∃ a, FrameCovers cfg.branch.frame a` (C2). NO universal
   conflict-state unfalsifiedness is required or claimed anywhere in this
   file.

## §7 addendum (C1 round 2, session 11)

The residual item 1 has been SPLIT and produced as far as honesty allows:

* `Proofs/EmissionVocabulary.lean` §2 defines the constraint-side
  condition `ThresholdsPooled` (the exact threshold representatives the
  registered `run` equations emit) and §3 proves
  `unitEmissionVocabulary_proved_of_thresholds` from it — so item 1 is
  now exactly `ThresholdsPooled` (plus nothing else). §4 kernel-refutes
  the condition at the sparse box `[[1, 5]]` with `.leConstHi 0 3`
  (`emitted_threshold_not_pooled`, `thresholdsPooled_false_sparse`), so
  the pool residual is REAL and cannot be discharged by `unitFamilyB`
  alone; the Boolean `constEq` row is unconditional
  (`pooledEmission_constEqBool`, only the slot range is consumed).
* Item 3's arm laws are landed in `Proofs/TrailVocabularyProducers.lean`
  §1–§4 (split literal pooled, deduction literal pooled — the
  DATABASE-sourced case takes `DatabaseAligned` as a named premise —
  closure/restoreLevel/restoreNarrow/perform trail producers). The
  run-level site-form producer §5 additionally needs the RECORDING-SITE
  premise `hrec` (the analyze arm records evidence on a `conflict = none`
  configuration, so the site-form induction cannot reach its branch);
  this is documented in that file's §6 together with the C2 residual
  (`hinhab_site` per evidence site vs the empty-frame route
  `not_reachableFrameInhabited_emptyDomain`). -/

/-! ## §8 The pool-parametric emission vocabulary (C1 round 3)

`UnitEmissionVocabulary` hard-codes `litPool orig` as the pool. The
finite-pool-extension route (C1 round 3) needs the SAME discipline at the
extended pool `litPoolWith` (`SchedulerVocabulary` §"finite pool
extension"; `litPoolExt orig dcs` in `Proofs/EmissionVocabulary.lean` §5),
because the retained kernel witness shows emitted thresholds can fall
outside `litPool orig`. `EmissionVocabularyAt` is that generalization:
definitionally the same conjunction with an arbitrary pool, so
`UnitEmissionVocabulary orig props` IS `EmissionVocabularyAt (litPool orig)
props` (the `Iff.rfl` bridge below) and every existing consumer keeps its
statement. The extended-pool producer is
`emissionVocabularyAt_litPoolExt` (`Proofs/EmissionVocabulary.lean` §5),
needing NO threshold premise (`hSupp` alone). -/

/-- The propagator kit's emission vocabulary relative to an ARBITRARY
literal pool: implied reasons are normalized units whose literal IS the
pivot and is pooled; conflicts are empty or such units. At
`pool := litPool orig` this is `UnitEmissionVocabulary` definitionally. -/
def EmissionVocabularyAt (pool : List Literal) (props : List Propagator) : Prop :=
  (∀ p ∈ props, ∀ st l r, p.run st = .implied l r →
    ∃ q : Literal, r.clause = [q] ∧ l = q ∧ q = q.norm ∧ q.norm ∈ pool) ∧
  (∀ p ∈ props, ∀ st c, p.run st = .conflict c →
    c = [] ∨ ∃ q : Literal, c = [q] ∧ q = q.norm ∧ q.norm ∈ pool)

/-- The bridge: the landed `UnitEmissionVocabulary` is exactly the
pool-parametric form at the box's own `litPool`. -/
theorem unitEmissionVocabulary_iff_at {orig : List Domain}
    {props : List Propagator} :
    UnitEmissionVocabulary orig props ↔
      EmissionVocabularyAt (litPool orig) props :=
  Iff.rfl

/-- Pool monotonicity: a larger pool keeps the vocabulary. -/
theorem emissionVocabularyAt_mono {pool pool' : List Literal}
    {props : List Propagator}
    (hsub : ∀ l ∈ pool, l ∈ pool')
    (h : EmissionVocabularyAt pool props) :
    EmissionVocabularyAt pool' props := by
  constructor
  · intro p hp st l r hr
    obtain ⟨q, hq, hl, hqn, hpool⟩ := h.1 p hp st l r hr
    exact ⟨q, hq, hl, hqn, hsub q.norm hpool⟩
  · intro p hp st c hc
    rcases h.2 p hp st c hc with hnil | ⟨q, hq, hqn, hpool⟩
    · exact Or.inl hnil
    · exact Or.inr ⟨q, hq, hqn, hsub q.norm hpool⟩

/-- The emission vocabulary at an arbitrary pool still forgets to a
`UnitRunProfile` (the pool is not consulted by that consumer). -/
theorem emissionVocabularyAt_runProfile {pool : List Literal}
    {props : List Propagator} (h : EmissionVocabularyAt pool props) :
    UnitRunProfile props := by
  constructor
  · intro p hp st l r hr
    obtain ⟨q, hq, -, hqn, -⟩ := h.1 p hp st l r hr
    exact ⟨q, hq, hqn⟩
  · intro p hp st c hc
    rcases h.2 p hp st c hc with hnil | ⟨q, hq, hqn, -⟩
    · exact Or.inl hnil
    · exact Or.inr ⟨q, hq, hqn⟩

end LeanFzn.Solver.UIP
