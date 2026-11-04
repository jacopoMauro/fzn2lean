/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerRank.lean

Prereqs: P1 (`Proofs/SchedulerVocabulary.lean`), S5 (`Proofs/SchedulerStep.lean`)
and P2's `canonicalDB` (`Proofs/LearningNovelty.lean`).

PURPOSE.  The PLAN's candidate rank `(remainingCanonicalClauses,
chronologicalWork, localMass, phase)` instantiated over a FIXED compiled
input `orig`, with the non-jump arm decreases bound to the REAL runtime
transitions. The new measure is named `PhaseRank` (the old C3a measure is
`SchedulerRank` and is NOT reused as a tuple: its type is a 3-tuple).

THE MEASURE (`PhaseRank orig cfg : Nat × Nat × Nat × Nat`, lexicographic):

  1. `absentCount cfg.branch.learned (clausePool orig)` — the
     bounded-database component: the number of FIXED-POOL clauses (P1's
     `clausePool orig`) whose canonical form is NOT yet in the learned
     database.  It is a COUNT, never a subtraction, so it cannot
     saturate: it is bounded by `(clausePool orig).length` for every
     database (`absentCount_le_length`), and the honest `Nat.sub` reading
     is licensed by the partition theorem
     `presentCount + absentCount = pool.length` (`absentCount_eq_sub`), so
     `length - present` is provably non-saturating.  A raw
     `pool.length - db.length` would saturate and hide progress; that is
     exactly what the partition excludes.
  2. `frontierCost cfg.frontier` — chronologicalWork (the current frame
     IS the head of the work list).
  3. `Frame.mass cfg.branch.frame` — localMass.
  4. `statusWeight cfg.status` — the phase countdown: `1` while the
     branch is `.active`, `0` once it is `.dead`.  The evidence-recorded
     sub-phase (`conflict = some ev`) is deliberately NOT a component:
     recording evidence is a rank STUTTER whose successor route cannot
     repeat (`analyzeConflictCounted_not_repeated`), which is the C3a
     phase argument, re-run here for the O1 COUNTED site.

GATE COVERAGE (PLAN P3 acceptance gate):

  * rank def over the FIXED input with `clausePool` bounds: §1, §2;
  * database component non-increase:
    `absent_propagate_le`, `absent_localExclude_le` (the two DB-growing
    transitions) — restriction of `absentCount_mono`;
  * `WellFounded` lex relation: §3 (`Subrelation.wf` + `InvImage.wf` over
    the core product instance; the old `C3a.rankLt_wf` does not apply
    because the component count differs);
  * non-jump decreases: propagate (mass, §4), decide (frontierCost, §4),
    consume (frontierCost, §4), localExclude/fallback single steps plus
    the forced-consume composites (§5), the analyze recorder stutter and
    its non-repetition, INCLUDING the counted evidence recording (§6);
  * DB-changing propagation: the primary component never increases (§4).

P4 TARGET (NOT claimed here).  The jump arm
`stepLearnBackjumpAssert` is P4's separate obligation
(`Proofs/SchedulerJumpProgress.lean`): its new database is
`ev.learned ++ restored.learned`, and a genuinely new canonical pool
clause (P2's `jumpNovelty_progress`) is the only proved source of a
STRICT decrease of component 1.  This file proves the bracketing facts
(component 1 cannot increase on any non-jump step) but leaves the strict
component-1 decrease to P4; a restored ancestor's `frontierCost` can
exceed the conflict frame's, so no other component pays for the jump.

REUSE NOTES (old lemmas reused vs re-proved):
  * REUSED verbatim (rank-agnostic): `frontierCost_cons`,
    `frontierCost_expand`, `branchCost_pos`, `filterFrame_cost_le`,
    `C3a.frontierCost_frame_lt`, `C3a.frontierCost_frame_congr`,
    `C3a.splitData_frame_eq`, `C3a.stepConsume_frame_of_pending_cons`,
    `C3a.backjumpStep_not_analyzeConflict`, `C2d.schedulerNext_eq_backjump`,
    the runtime shape lemmas `stepDecide_learned/pending/frame`.
  * RE-PROVED for the new tuple (the old statements do not apply): every
    `PhaseLt` decrease, the lex order and its well-foundedness, all
    `absentCount` algebra, and `stepConsume_learned` (C3a never needed the
    database of the consumed successor; component 1 does).
  * NOT reused: `C3a.SchedulerRank`/`RankLt`/`rankLt_wf` and the old arm
    decreases — different tuple.

No `sorry`, no custom axioms.  Namespace-local `P3` helpers only.

DAG:
  Proofs.SchedulerProgress (C3a) + Proofs.LearningNovelty (P2)
    -> Proofs.SchedulerRank (this module; consumed by P4/P5)
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerProgress
import LeanFzn.Legacy.Solver.UIP.Proofs.LearningNovelty
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.P3
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP

/-! ## §1 The bounded-database component: counts, not saturating subtraction -/

/-- Number of FIXED-POOL clauses canonically present in the database. -/
def presentCount (db pool : List Clause) : Nat :=
  match pool with
  | [] => 0
  | c :: cs => (if c ∈ canonicalDB db then 1 else 0) + presentCount db cs

/-- The rank's database component: FIXED-POOL clauses whose canonical
form is NOT yet in the database. A count over the pool, so it is
unconditionally bounded by the pool size (no `-` anywhere). -/
def absentCount (db pool : List Clause) : Nat :=
  match pool with
  | [] => 0
  | c :: cs => (if c ∈ canonicalDB db then 0 else 1) + absentCount db cs

/-- Partition theorem: the pool splits into present and absent clauses.
This is the honesty licence for the `Nat.sub` reading of the remaining
count: the subtrahend is counted inside the minuend, so subtraction
cannot saturate incorrectly. -/
theorem presentCount_add_absentCount (db pool : List Clause) :
    presentCount db pool + absentCount db pool = pool.length := by
  induction pool with
  | nil => simp [presentCount, absentCount]
  | cons c cs ih =>
      simp only [presentCount, absentCount, List.length_cons]
      by_cases hc : c ∈ canonicalDB db
      · rw [if_pos hc, if_pos hc]; omega
      · rw [if_neg hc, if_neg hc]; omega

/-- The remaining count is bounded by the FIXED pool size — for EVERY
database, including databases larger than the pool. This is the bound the
rank's well-foundedness reads. -/
theorem absentCount_le_length (db pool : List Clause) :
    absentCount db pool ≤ pool.length := by
  have h := presentCount_add_absentCount db pool
  omega

/-- `Nat.sub` reading, licensed by the proved partition (P3 gate: "cannot
saturate natural subtraction incorrectly"). -/
theorem absentCount_eq_sub (db pool : List Clause) :
    absentCount db pool = pool.length - presentCount db pool := by
  have h := presentCount_add_absentCount db pool
  omega

/-- Monotonicity of the canonical image of the database. -/
theorem canonicalDB_mono {db db' : List Clause} (h : ∀ c ∈ db, c ∈ db') :
    ∀ c, c ∈ canonicalDB db → c ∈ canonicalDB db' := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
  exact List.mem_map.mpr ⟨d, h d hd, rfl⟩

/-- THE DATABASE COMPONENT NEVER INCREASES when the database grows: every
present pool clause stays present, so the absent set only shrinks. -/
theorem absentCount_mono {db db' : List Clause} (h : ∀ c ∈ db, c ∈ db')
    (pool : List Clause) : absentCount db' pool ≤ absentCount db pool := by
  have hcanon := canonicalDB_mono h
  induction pool with
  | nil => simp [absentCount]
  | cons c cs ih =>
      have hstep : (if c ∈ canonicalDB db' then 0 else 1) ≤
          (if c ∈ canonicalDB db then 0 else 1) := by
        by_cases hc : c ∈ canonicalDB db
        · have hc' : c ∈ canonicalDB db' := hcanon c hc
          simp [hc, hc']
        · by_cases hc' : c ∈ canonicalDB db' <;> simp [hc, hc']
      simp only [absentCount]
      omega

/-! ## §2 The rank over a FIXED input -/

/-- The phase countdown: `.active` counts one, `.dead` counts zero. The
evidence-recorded sub-phase stays `.active` and is handled by the
non-repetition argument (§6). -/
def statusWeight : BranchStatus → Nat
  | .active => 1
  | .dead => 0

/-- **THE P3 RANK** (`PhaseRank`, distinct from C3a's `SchedulerRank`):
`(remainingCanonicalClauses, chronologicalWork, localMass, phase)` over
the FIXED compiled input `orig`, lexicographically (component 1 most
significant). All four components are `Nat`; the pool bounds come from
P1's `clausePool orig`. -/
def PhaseRank (orig : List Domain) (cfg : SchedulerConfig leaf) :
    Nat × Nat × Nat × Nat :=
  (absentCount cfg.branch.learned (clausePool orig),
   frontierWeight cfg.frontier,
   Frame.mass cfg.branch.frame,
   statusWeight cfg.status)

/-- The lexicographic order on the rank's 4-tuple (right-associated
product, so the core instance nests three `Prod.Lex` layers). -/
def PhaseLt (a b : Nat × Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨
    (a.1 = b.1 ∧
      (a.2.1 < b.2.1 ∨
        (a.2.1 = b.2.1 ∧
          (a.2.2.1 < b.2.2.1 ∨ (a.2.2.1 = b.2.2.1 ∧ a.2.2.2 < b.2.2.2)))))

/-- The rank's own components do not read `events`: the O1 counted
evidence recording cannot reset progress through the counter. -/
theorem phaseRank_events_congr (orig : List Domain) (cfg : SchedulerConfig leaf)
    (e : RuntimeEvents) :
    PhaseRank orig { cfg with events := e } = PhaseRank orig cfg := rfl

/-! ## §3 Well-foundedness of the lex order -/

/-- The lex order is the core product well-founded relation on the
4-tuple (definitional identification: `sizeOf` is the identity on `Nat`,
so all three `Prod.Lex` layers are the instance's layers). -/
theorem phaseLt_of_inst {a b : Nat × Nat × Nat × Nat} (h : PhaseLt a b) :
    (inferInstance : WellFoundedRelation (Nat × Nat × Nat × Nat)).rel a b := by
  have hrel : (inferInstance : WellFoundedRelation (Nat × Nat × Nat × Nat)).rel =
      Prod.Lex (sizeOfWFRel.rel (α := Nat))
        (Prod.Lex (sizeOfWFRel.rel (α := Nat))
          (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))) := rfl
  rw [hrel]
  show Prod.Lex (sizeOfWFRel.rel (α := Nat))
    (Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat))))
    (a.1, a.2) (b.1, b.2)
  rcases h with h | ⟨h1, h | ⟨h2, h | ⟨h3, h4⟩⟩⟩
  · exact Prod.Lex.left (b₁ := a.2) (b₂ := b.2) h
  · rw [← h1]
    exact Prod.Lex.right (a := a.1)
      (Prod.Lex.left (b₁ := a.2.2) (b₂ := b.2.2) h)
  · rw [← h1]
    refine Prod.Lex.right (a := a.1) ?_
    show Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
      (a.2.1, a.2.2) (b.2.1, b.2.2)
    rw [← h2]
    exact Prod.Lex.right (a := a.2.1)
      (Prod.Lex.left (b₁ := a.2.2.2) (b₂ := b.2.2.2) h)
  · rw [← h1]
    refine Prod.Lex.right (a := a.1) ?_
    show Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
      (a.2.1, a.2.2) (b.2.1, b.2.2)
    rw [← h2]
    refine Prod.Lex.right (a := a.2.1) ?_
    show Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat))
      (a.2.2.1, a.2.2.2) (b.2.2.1, b.2.2.2)
    rw [← h3]
    exact Prod.Lex.right (a := a.2.2.1) h4

/-- The lex order is well-founded (subrelation of the core instance). -/
theorem phaseLt_wf : WellFounded PhaseLt :=
  Subrelation.wf (fun {_ _} h => phaseLt_of_inst h)
    (inferInstance : WellFoundedRelation (Nat × Nat × Nat × Nat)).wf

/-- The scheduler's step relation is well-founded when oriented by the
new rank: an infinite computation must produce an infinite strictly
decreasing `PhaseRank` chain, which cannot exist. -/
theorem phaseRank_wf {leaf : Assignment → Bool} (orig : List Domain) :
    WellFounded (fun a b : SchedulerConfig leaf =>
      PhaseLt (PhaseRank orig a) (PhaseRank orig b)) :=
  InvImage.wf (PhaseRank orig) phaseLt_wf

/-! ## §4 Transition shape lemmas for the database component -/

theorem stepPropagate_learned_eq (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).branch.learned = d.learned ++ cfg.branch.learned :=
  stepPropagate_branch_learned cfg d

theorem stepLocalExclude_learned_eq (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).branch.learned
      = learned ++ cfg.branch.learned := rfl

theorem stepLocalExclude_status (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).status = .dead := rfl

theorem stepChronologicalFallback_learned_eq (cfg : SchedulerConfig leaf)
    (r : DeadRegion) :
    (stepChronologicalFallback cfg r).branch.learned = cfg.branch.learned := rfl

theorem stepChronologicalFallback_status (cfg : SchedulerConfig leaf)
    (r : DeadRegion) :
    (stepChronologicalFallback cfg r).status = .dead := rfl

/-- The phase weights: dead strictly below active. -/
theorem statusWeight_dead_lt_active :
    statusWeight .dead < statusWeight .active := by decide

/-- The consumed successor carries the SAME learned database (the single
canonical resume rebuilds only trail/level/frame; `resumePending` keeps
`learned`). C3a never needed this, the new component 1 does. -/
theorem stepConsume_learned {cfg next : SchedulerConfig leaf}
    (h : stepConsume cfg = some next) :
    next.branch.learned = cfg.branch.learned := by
  unfold LeanFzn.Solver.UIP.stepConsume at h
  cases hp : cfg.pending with
  | nil => rw [hp] at h; cases h
  | cons f rest =>
      rw [hp] at h
      dsimp only at h
      simp only [Option.some.injEq] at h
      subst h
      exact LeanFzn.Solver.Propagation.resumePending_learned cfg.orig cfg.branch f

/-! ## §4b DB-changing propagation: the primary component never increases

`stepPropagate` inserts `d.learned` (freshness-filtered) into the
database, so component 1 may drop but can never rise. -/

theorem absent_propagate_le (orig : List Domain) (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    absentCount (stepPropagate cfg d).branch.learned (clausePool orig) ≤
      absentCount cfg.branch.learned (clausePool orig) := by
  apply absentCount_mono
  intro c hc
  rw [stepPropagate_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

/-- Local exclusion also inserts `learned`; component 1 never increases. -/
theorem absent_localExclude_le (orig : List Domain) (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    absentCount (stepLocalExclude cfg learned r).branch.learned (clausePool orig) ≤
      absentCount cfg.branch.learned (clausePool orig) := by
  apply absentCount_mono
  intro c hc
  rw [stepLocalExclude_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

/-! ## §5 The non-jump decreases -/

/-- PROPAGATE (mass arm): the DB-changing propagation may drop component 1
(strictly, then done) or keep it; in the latter case the old C3a split
applies to the NEW tuple — a strictly cheaper narrowed frame decreases
component 2, otherwise the deduction's own strict `Frame.mass` decrease
pays for component 3. REUSED: `filterFrame_cost_le`, the C3a frontier
algebra; RE-PROVED: the lex case analysis at the new arity. -/
theorem phaseRank_lt_propagate (orig : List Domain) (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    PhaseLt (PhaseRank orig (stepPropagate cfg d)) (PhaseRank orig cfg) := by
  have hrem := absent_propagate_le orig cfg d
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hcost : branchCost d.frame.doms ≤ branchCost cfg.branch.frame.doms :=
      filterFrame_cost_le d.filtered
    have e1 : (PhaseRank orig (stepPropagate cfg d)).snd =
        (frontierWeight (d.frame :: cfg.pending), Frame.mass d.frame,
          statusWeight (stepPropagate cfg d).status) := by
      simp [PhaseRank, SchedulerConfig.frontier, narrowState]
    rw [e1]
    rcases Nat.lt_or_eq_of_le hcost with hclt | hceq
    · exact Or.inl (C3a.frontierWeight_frame_lt hclt cfg.pending)
    · exact Or.inr ⟨C3a.frontierWeight_frame_congr hceq cfg.pending, Or.inl d.decreases⟩

/-- DECIDE (frontier arm): the database is unchanged (component 1 equal);
the split replaces the parent frame by its two children and
`frontierCost_expand` gives a strict decrease of component 2. REUSED:
`C3a.splitData_frame_eq`, `frontierCost_expand`; RE-PROVED: the component
equality at the new arity. -/
theorem phaseRank_lt_decide (orig : List Domain) (cfg : SchedulerConfig leaf)
    (k : Nat) (v : Value) (vs : Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, e.enum ≠ []) :
    PhaseLt (PhaseRank orig (stepDecide cfg k v vs l)) (PhaseRank orig cfg) := by
  have hspec := C3a.splitData_frame_eq hsplit
  have hne : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsplit
  have hnew : (stepDecide cfg k v vs l).frontier
      = cfg.branch.frame.pin k v :: cfg.branch.frame.retire k vs :: cfg.pending := by
    simp only [SchedulerConfig.frontier, stepDecide_pending, stepDecide_frame]
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCount (stepDecide cfg k v vs l).branch.learned (clausePool orig) =
      absentCount cfg.branch.learned (clausePool orig)
    rw [stepDecide_learned]
  · show frontierWeight (stepDecide cfg k v vs l).frontier <
      frontierWeight cfg.frontier
    rw [hnew]
    exact DecisionProto.frontierWeight_split_lt
      (DecisionProto.cost_pin_lt hspec hne hall)
      (DecisionProto.cost_retire_lt hspec hall)

/-- THE SKIP'S FRONTIER COST DROP (rank-agnostic, B1): at a split site the
pinned child `(doms, chosen ++ [v])` is strictly cheaper than the parent
frame `((v :: vs) :: doms, chosen)` (the frame loses its nonempty head
domain), and the pending stack is common. Shared by the P3 and P4 skip
decreases. -/
theorem frontierWeight_stepDecideSkip_lt {cfg : SchedulerConfig leaf}
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, e.enum ≠ []) :
    frontierWeight (stepDecideSkip cfg k v).frontier
      < frontierWeight cfg.frontier := by
  have hspec := C3a.splitData_frame_eq hsplit
  have hne : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsplit
  have hnew : (stepDecideSkip cfg k v).frontier
      = cfg.branch.frame.pin k v :: cfg.pending := by
    simp only [SchedulerConfig.frontier, stepDecideSkip]
  rw [hnew]
  exact C3a.frontierWeight_frame_lt
    (DecisionProto.cost_pin_lt hspec hne hall) cfg.pending

/-- DECIDE-SKIP (B1, frontier arm): the redundant-pin skip replaces the head
frame `((v :: vs) :: doms, chosen)` by the pinned child
`(doms, chosen ++ [v])` without pushing a sibling. The database is untouched
(component 1 equal) and the frontier cost strictly decreases (component 2,
`frontierCost_stepDecideSkip_lt`). REUSED: `C3a.splitData_frame_eq`. -/
theorem phaseRank_lt_decideSkip (orig : List Domain) (cfg : SchedulerConfig leaf)
    (k : Nat) (v : Value) (vs : Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, e.enum ≠ []) :
    PhaseLt (PhaseRank orig (stepDecideSkip cfg k v)) (PhaseRank orig cfg) :=
  Or.inr ⟨rfl, Or.inl (frontierWeight_stepDecideSkip_lt hsplit hall)⟩

/-- CONSUME (frontier arm): the dead current frame leaves the frontier and
the consumed pending alternative becomes it; the database is carried over
(`stepConsume_learned`), so component 1 is equal and component 2 strictly
decreases by `frontierCost_cons`. REUSED:
`C3a.stepConsume_frame_of_pending_cons`, `frontierCost_cons`. -/
theorem phaseRank_lt_consume (orig : List Domain) {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    PhaseLt (PhaseRank orig next) (PhaseRank orig cfg) := by
  have hlearn := stepConsume_learned h
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCount next.branch.learned (clausePool orig) =
      absentCount cfg.branch.learned (clausePool orig)
    rw [hlearn]
  · obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight (cfg.branch.frame :: cfg.pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons cfg.branch.frame (f :: rest)

/-- LOCAL EXCLUDE: the database may grow (component 1 non-increase); with
component 1 equal, components 2 and 3 are untouched and the phase
countdown `.active → .dead` strictly decreases component 4. The guard
`cfg.status = .active` is the dispatcher's. -/
theorem phaseRank_lt_localExclude (orig : List Domain) (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) (hstatus : cfg.status = .active) :
    PhaseLt (PhaseRank orig (stepLocalExclude cfg learned r)) (PhaseRank orig cfg) := by
  have hrem := absent_localExclude_le orig cfg learned r
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩⟩
    show statusWeight (stepLocalExclude cfg learned r).status < statusWeight cfg.status
    rw [stepLocalExclude_status, hstatus]
    exact statusWeight_dead_lt_active

/-- CHRONOLOGICAL FALLBACK: precisely the same shape with an unchanged
database; the phase countdown pays. Guard: dispatcher's `status =
.active`. -/
theorem phaseRank_lt_fallback (orig : List Domain) (cfg : SchedulerConfig leaf)
    (r : DeadRegion) (hstatus : cfg.status = .active) :
    PhaseLt (PhaseRank orig (stepChronologicalFallback cfg r)) (PhaseRank orig cfg) := by
  refine Or.inr ⟨?_, Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩⟩
  · show absentCount (stepChronologicalFallback cfg r).branch.learned
        (clausePool orig) = absentCount cfg.branch.learned (clausePool orig)
    rw [stepChronologicalFallback_learned_eq]
  · show statusWeight (stepChronologicalFallback cfg r).status
        < statusWeight cfg.status
    rw [stepChronologicalFallback_status, hstatus]
    exact statusWeight_dead_lt_active

/-! ## §5b The stutter composites (fallback/consume, localExclude/consume)

In the NEW rank the two dead-marking steps already strictly decrease on
their own (the countdown component); the composites are stated anyway for
interface compatibility with the deliverable's wording, and they compose
with the consume step that the dispatcher FORCES afterwards (both steps
leave `conflict = none ∧ status = .dead`, exactly the consume guard). -/

theorem phaseRank_lt_fallback_then_consume (orig : List Domain)
    {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (_hstatus : cfg.status = .active)
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRank orig next) (PhaseRank orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepChronologicalFallback cfg r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepChronologicalFallback cfg r).branch.frame
          :: (stepChronologicalFallback cfg r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCount next.branch.learned (clausePool orig) =
      absentCount cfg.branch.learned (clausePool orig)
    rw [hlearn, stepChronologicalFallback_learned_eq]
  · show frontierWeight next.frontier < frontierWeight cfg.frontier
    rwa [show frontierWeight (stepChronologicalFallback cfg r).frontier
        = frontierWeight cfg.frontier from rfl] at hwork

theorem phaseRank_lt_localExclude_then_consume (orig : List Domain)
    {cfg next : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (_hstatus : cfg.status = .active)
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRank orig next) (PhaseRank orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hrem1 := absent_localExclude_le orig cfg learned r
  have hwork : frontierWeight next.frontier
      < frontierWeight (stepLocalExclude cfg learned r).frontier := by
    show frontierWeight (next.branch.frame :: next.pending)
      < frontierWeight ((stepLocalExclude cfg learned r).branch.frame
          :: (stepLocalExclude cfg learned r).pending)
    rw [hframe, hpend, hp]
    exact frontierWeight_cons _ _
  rcases Nat.lt_or_eq_of_le hrem1 with hlt | heq
  · refine Or.inl ?_
    show absentCount next.branch.learned (clausePool orig)
      < absentCount cfg.branch.learned (clausePool orig)
    rw [hlearn]
    exact hlt
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · show absentCount next.branch.learned (clausePool orig) =
        absentCount cfg.branch.learned (clausePool orig)
      rw [hlearn]
      exact heq
    · show frontierWeight next.frontier < frontierWeight cfg.frontier
      rwa [show frontierWeight (stepLocalExclude cfg learned r).frontier
          = frontierWeight cfg.frontier from rfl] at hwork

/-! ## §6 The analyze recorder: stutter, counted evidence, non-repetition

The O1 counted analyze site (`stepAnalyzeConflictCounted`, which records
the real `analyzeEvents` expansion count into `cfg.events`) changes only
`conflict`, `events` and `stats`; all four rank components are literally
unchanged. A single-step strict decrease is IMPOSSIBLE for a
`BranchState`-projection measure (the same finding as C3a arm 4), so the
termination content is the PHASE argument: the successor carries recorded
evidence, whose dispatcher route is `backjumpStep`, which can never
return `.analyzeConflict` — the stutter is one-shot and P4's jump
obligation takes over. -/

/-- The counted evidence recording is a rank STUTTER (the `events`
increment is invisible to the rank by `phaseRank_events_congr`). -/
theorem phaseRank_analyzeConflictCounted_stutter (orig : List Domain)
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) (n : Nat) :
    PhaseRank orig (stepAnalyzeConflictCounted cfg c learned n)
      = PhaseRank orig cfg := rfl

/-- The counted recorder's successor carries evidence. -/
theorem analyzeConflictCounted_conflict_isSome (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).conflict.isSome = true := rfl

/-- NON-REPETITION at the real dispatcher: after the counted recorder the
dispatcher's arm is `backjumpStep`, which by the REUSED
`C3a.backjumpStep_not_analyzeConflict` never returns `.analyzeConflict`
again. -/
theorem analyzeConflictCounted_not_repeated (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    ¬ (∃ next c', schedulerNext (stepAnalyzeConflictCounted cfg c learned n)
      = .analyzeConflict next c') := by
  intro hc
  have hsome : (stepAnalyzeConflictCounted cfg c learned n).conflict.isSome = true := rfl
  cases hcc : (stepAnalyzeConflictCounted cfg c learned n).conflict with
  | none => rw [hcc] at hsome; cases hsome
  | some ev =>
      obtain ⟨next, c', h⟩ := hc
      rw [C2d.schedulerNext_eq_backjump hcc] at h
      exact C3a.backjumpStep_not_analyzeConflict _ _ ⟨next, c', h⟩

/-! ## §8 Generic projected-database counts (order-insensitive interface)

The pool countdown is parameterized by the canonical projection. The
`Clause.canonicalClause` instance recovers the P3 definitions
(`canonicalDBMap Clause.canonicalClause = canonicalDB`); the P4
sorted-shape rank instantiates `f := canonicalSorted orig`, whose pool
membership is a THEOREM (`canonicalSorted_mem_sortedClausePool`), so
the previously-open `hpool` premise disappears. -/

/-- Generic canonical projection of a database. -/
def canonicalDBMap (f : Clause → Clause) (db : List Clause) : List Clause := db.map f

theorem canonicalDBMap_mono {f : Clause → Clause} {db db' : List Clause}
    (h : ∀ d ∈ db, d ∈ db') :
    ∀ d ∈ canonicalDBMap f db, d ∈ canonicalDBMap f db' := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
  exact List.mem_map_of_mem (f := f) (h e he)

/-- Generic absent count over a projected database. -/
def absentCountMap (f : Clause → Clause) (db pool : List Clause) : Nat :=
  match pool with
  | [] => 0
  | c :: cs => (if c ∈ canonicalDBMap f db then 0 else 1) + absentCountMap f db cs

theorem absentCountMap_mono {f : Clause → Clause} {db db' : List Clause}
    (h : ∀ d ∈ db, d ∈ db') (pool : List Clause) :
    absentCountMap f db' pool ≤ absentCountMap f db pool := by
  have hcanon := canonicalDBMap_mono (f := f) h
  induction pool with
  | nil => simp [absentCountMap]
  | cons c cs ih =>
      simp only [absentCountMap]
      have hhead : (if c ∈ canonicalDBMap f db' then 0 else 1) ≤
          (if c ∈ canonicalDBMap f db then 0 else 1) := by
        by_cases hc : c ∈ canonicalDBMap f db
        · simp [hc, hcanon c hc]
        · by_cases hc' : c ∈ canonicalDBMap f db' <;> simp [hc, hc']
      omega

/-- Generic strict countdown decrease: no subtraction, no slack. -/
theorem absentCountMap_lt_of_mono_mem {f : Clause → Clause}
    {db db' pool : List Clause} {c : Clause} (hmono : ∀ d ∈ db, d ∈ db')
    (hpool : c ∈ pool) (hnew : c ∈ canonicalDBMap f db')
    (hold : c ∉ canonicalDBMap f db) :
    absentCountMap f db' pool < absentCountMap f db pool := by
  have hcanon := canonicalDBMap_mono (f := f) hmono
  induction pool with
  | nil => simp at hpool
  | cons d ds ih =>
      rcases List.mem_cons.mp hpool with rfl | htl
      · have h1 : (if c ∈ canonicalDBMap f db' then 0 else 1) = 0 := if_pos hnew
        have h0 : (if c ∈ canonicalDBMap f db then 0 else 1) = 1 := if_neg hold
        have htle := absentCountMap_mono (f := f) hmono ds
        simp only [absentCountMap]
        rw [h1, h0]
        omega
      · have hhead : (if d ∈ canonicalDBMap f db' then 0 else 1) ≤
            (if d ∈ canonicalDBMap f db then 0 else 1) := by
          by_cases hd : d ∈ canonicalDBMap f db
          · simp [hd, hcanon d hd]
          · by_cases hd' : d ∈ canonicalDBMap f db' <;> simp [hd, hd']
        have hih := ih htl
        simp only [absentCountMap]
        omega



end LeanFzn.Solver.UIP.P3
