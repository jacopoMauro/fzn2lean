/-
File: LeanFzn/Solver/Propagation/Proofs/Run.lean

Purpose:
  The run-level reachability induction for the LCG engine loop
  (PLAN.md P3b): the states `lcgSearch.go` recurses into carry
  the `RunInv` bundle, and at the positive-level conflict arm the
  analyzed state is `AnalysisReady`, so `analyzeConflict_correct`
  applies and every learned clause the engine inserts is entailed.

  What is carried (all preserved by every transition the loop
  performs):

  * `conflictNone` — the loop's recursive entries are conflict-free
    (every repair clears the conflict slot);
  * `coherent` — the domains are the trail's `domOfLit` fold
    (`DomainCoherent`; propagation preserves it, repair rebuilds it
    this exact way);
  * `clausesFixed` — the original clause database is never modified;
  * `learnedEntailed` — every learned clause is entailed by the
    internal problem (seeded empty; each insertion is the analysis of
    an `AnalysisReady` state via `analyzeConflict_correct`);
  * `rooted` — every trail entry's level is at most the decision
    level (enqueue stamps the current level; repair truncates);
  * `trailNorm` — every trail literal is normalized (enqueueNorm
    enqueues `l0.norm`; repair filters a normalized trail);
  * `reasonNorm` — every reason clause of every entry contains only
    normalized literals (decisions carry `none`; scan-unit reasons
    are sub-clauses of normalized databases; propagator reasons are
    built by the per-family code from normalized trail literals —
    carried as an entry premise where a family supplies it);
  * `reasonValid` — every reason is a valid explanation of its pivot
    (scan-unit reasons: the clause is entailed and the pivot is a
    member — both structural; propagator reasons: the per-family
    entitlement premise);
  * `rootFacts` — every level-0 entry's literal is true at every
    internal solution (level-0 entries arise only from root-fact
    initialization and justified propagation at level 0).

  What is NOT carried (deliberately): `SolvedBy` — a decision splits
  the solution space, so per-state solution-representation does not
  survive the decision arm. Its run-level replacement (decision
  descent, `UnsatRun`'s general discharge) is PLAN §3 item 3; here the
  induction threads the ANALYSIS-side invariants only.

Dependencies:
  - LeanFzn.Solver.Chronological.Search: the engine loop.
  - LeanFzn.Solver.Propagation.Proofs.Theory: the propagation-layer preservation
    lemmas (`enqueueNorm_domFold`, `repair_domFold`, the level-0
    soundness chain).
  - LeanFzn.Solver.Propagation.Proofs.Transitions: `analyzeConflict_correct`.
  - LeanFzn.Solver.Propagation.Proofs.Engine: `DomainCoherent` and the trail lemmas.

DAG:
  LeanFzn.Solver.UIP.Search + LeanFzn.Solver.UIP.Proofs.{Theory,Transitions,Engine}
    -> LeanFzn.Solver.UIP.Proofs.Run -> LeanFzn.Solver.UIP.Proofs.Search (front-door assembly)
-/

import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Proofs.Theory
import LeanFzn.Solver.Propagation.Proofs.Transitions


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Reference
open LeanFzn LeanFzn.Solver.Core

/-! ## The run invariant -/

/-- The invariant carried between `lcgSearch.go` iterations. The
    `_entitled` parameters carry the external entitlement premises:
    the original clause database's entitlement and the per-family
    propagator entitlement (the same shape the front doors already
    demand). -/
structure RunInv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  /-- the domains are the trail's domOfLit fold -/
  coherent : DomainCoherent problem st
  /-- the original clause database is unchanged -/
  clausesFixed : st.clauses = problem.clauses
  /-- every learned clause is entailed -/
  learnedEntailed : ∀ c ∈ st.learned,
    c.EntailedBy problem constraintHolds
  /-- trail entry levels are at most the decision level -/
  rooted : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel
  /-- every trail literal is normalized -/
  trailNorm : ∀ e ∈ st.trail, e.literal = e.literal.norm
  /-- every reason clause is normalized -/
  reasonNorm : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
    ∀ l ∈ r.clause, l = l.norm
  /-- every reason is a valid explanation of its pivot. Propagator
      reasons consume the family entitlement premise. -/
  reasonValid : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
    Reason.Valid problem constraintHolds r e.literal
  /-- level-0 entries are true at every internal solution -/
  rootFacts : RootFacts problem constraintHolds st.trail
  /-- the original database's clauses are normalized -/
  clausesNorm : ∀ c ∈ st.clauses, ∀ l ∈ c, l = l.norm
  /-- the learned database's clauses are normalized -/
  learnedNorm : ∀ c ∈ st.learned, ∀ l ∈ c, l = l.norm

/-! ## Field lemmas for the arm transitions -/

/-- `enqueueNorm` preserves the trail-normalization invariant: the
    fresh arm appends the normalized `l0.norm`; the other arms leave
    the trail unchanged. -/
theorem enqueueNorm_trailNorm {st : State} {l0 : Literal}
    {reason : Option Reason}
    (h : ∀ e ∈ st.trail, e.literal = e.literal.norm) :
    ∀ e ∈ (enqueueNorm st l0 reason).trail,
      e.literal = e.literal.norm := by
  intro e he
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · rw [htr] at he; exact h e he
  · rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold
    · have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast]
      exact (norm_norm l0).symm

/-- `enqueueNorm` preserves rootedness: the fresh entry is stamped
    with the CURRENT decision level, which the bound allows. -/
theorem enqueueNorm_rooted {st : State} {l0 : Literal}
    {reason : Option Reason}
    (h : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel) :
    ∀ e ∈ (enqueueNorm st l0 reason).trail,
      e.level ≤ (enqueueNorm st l0 reason).decisionLevel := by
  have hdl : (enqueueNorm st l0 reason).decisionLevel
      = st.decisionLevel := by
    simp only [enqueueNorm]
    split
    · rfl
    · split
      · rfl
      · rfl
  intro e he
  rw [hdl]
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · rw [htr] at he
    exact h e he
  · rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold
    · have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast]
      exact Nat.le_refl _

/-- `enqueueNorm` preserves reason normalization when the enqueued
    reason's clause is normalized (the scan-unit and propagator
    callers establish this from their clause sources). -/
theorem enqueueNorm_reasonNorm {st : State} {l0 : Literal}
    {reason : Option Reason}
    (h : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
      ∀ l ∈ r.clause, l = l.norm)
    (hfresh : ∀ r ∈ reason, ∀ l ∈ r.clause, l = l.norm) :
    ∀ e ∈ (enqueueNorm st l0 reason).trail, ∀ r ∈ e.reason,
      ∀ l ∈ r.clause, l = l.norm := by
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · intro e he r hr l hl
    rw [htr] at he; exact h e he r hr l hl
  · intro e he r hr l hl
    rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold r hr l hl
    · have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast] at hr
      exact hfresh r hr l hl

/-- `enqueueNorm` preserves reason validity when the enqueued reason
    is valid for the enqueued (normalized) literal. -/
theorem enqueueNorm_reasonValid
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (h : ∀ e ∈ st.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hfresh : ∀ r ∈ reason,
      Reason.Valid problem constraintHolds r l0.norm) :
    ∀ e ∈ (enqueueNorm st l0 reason).trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal := by
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · intro e he r hr
    rw [htr] at he; exact h e he r hr
  · intro e he r hr
    rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold r hr
    · have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast] at hr
      rw [hlast]
      exact hfresh r hr

/-- `enqueueNorm` preserves the fixed original database. -/
theorem enqueueNorm_clausesFixed {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (h : st.clauses = problem.clauses) :
    (enqueueNorm st l0 reason).clauses = problem.clauses := by
  have hcl : (enqueueNorm st l0 reason).clauses = st.clauses := by
    simp only [enqueueNorm]
    split
    · rfl
    · split
      · rfl
      · rfl
  rw [hcl, h]

/-- `enqueueNorm` preserves learned-clause membership (hence
    entitlement). -/
theorem enqueueNorm_learnedEntailed
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (h : ∀ c ∈ st.learned, c.EntailedBy problem constraintHolds) :
    ∀ c ∈ (enqueueNorm st l0 reason).learned,
      c.EntailedBy problem constraintHolds := by
  have hln : (enqueueNorm st l0 reason).learned = st.learned := by
    simp only [enqueueNorm]
    split
    · rfl
    · split
      · rfl
      · rfl
  rw [hln]
  exact h

/-- The scan-unit reason's validity: the clause is one of the active
    (entitled) clauses and the unit literal is its member, exactly as
    `scanClause`'s filter built it. -/
theorem scanUnit_reasonValid
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause} {l : Literal}
    (hc : c ∈ st.clauses ∨ c ∈ st.learned)
    (hclauses : ∀ c2 ∈ st.clauses, c2.EntailedBy problem constraintHolds)
    (hlearned : ∀ c2 ∈ st.learned,
      c2.EntailedBy problem constraintHolds)
    (hscan : scanClause st c = some (.inr (l, { clause := c }))) :
    Reason.Valid problem constraintHolds { clause := c } l := by
  refine ⟨?_, ?_⟩
  · rcases hc with hc | hc
    · exact hclauses c hc
    · exact hlearned c hc
  · -- the unit literal is a member of the scanned clause: the scan's
    -- filter keeps exactly the clause's non-false literals
    unfold scanClause at hscan
    split at hscan
    · exact absurd hscan (by simp)
    · have hmem : l ∈ c := by
        match hh : c.filter (fun l2 => !st.negOnTrail l2) with
        | [] => rw [hh] at hscan; exact absurd hscan (by simp)
        | [l2] =>
            rw [hh] at hscan
            have hll : l = l2 := by
              injection hscan with h1
              injection h1 with h2
              cases h2
              rfl
            rw [hll]
            have hmem2 : l2 ∈ List.filter (fun l2 => !st.negOnTrail l2) c :=
              by rw [hh]; exact List.mem_cons_self
            exact (List.mem_filter.mp hmem2).1
        | l1 :: l2 :: rest =>
            rw [hh] at hscan
            exact absurd hscan (by simp)
      simpa using hmem

/-! ## The empty-conflict non-analyzability lemmas

An EMPTY conflict clause never analyzes: `analyzeStep` skips the
empty worklist clause, the worklist empties, and `nextPivot` on the
empty mark set is `none`. This is what makes the analysis arm's own
success (`analyzeConflict … = some an`) force the conflict clause to
be nonempty — the soundness hinge of the `cc ≠ []`-restricted
`hconfent` premise (the `neSlot` family reports the empty clause at
decision-narrowed states, where it is not entitled; the engine then
takes the chronological-fallback arm instead). -/

/-- `nextPivot` on the empty mark set is `none`. -/
theorem nextPivot_none (trail : List TrailEntry) :
    nextPivot trail [] = none := by
  unfold nextPivot
  simp

/-- Every worklist clause being empty (no skip, no marks, no learnt)
    makes the analyzer return `none`. -/
theorem analyzeStep_all_empty (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (cs : List Clause), (∀ c ∈ cs, c = []) →
      analyzeStep trail lvl fuel cs none [] [] = none := by
  intro fuel
  induction fuel with
  | zero => intro cs _; cases cs <;> rfl
  | succ k ih =>
      intro cs hall
      cases cs with
      | nil =>
          show analyzeStep trail lvl (k+1) [] none [] [] = none
          unfold analyzeStep
          rw [nextPivot_none trail]
      | cons c rest =>
          have hce : c = [] := hall c (List.mem_cons_self)
          subst hce
          have hrest : ∀ c2 ∈ rest, c2 = [] := fun c2 hc2 =>
            hall c2 (List.mem_cons_of_mem _ hc2)
          show analyzeStep trail lvl (k+1) ([] :: rest) none [] [] = none
          unfold analyzeStep
          exact ih rest hrest

/-- The empty conflict clause never resolves to a UIP. -/
theorem analyzeTrail_empty (trail : List TrailEntry) (lvl : Nat) :
    analyzeTrail trail lvl ([] : Clause) = none := by
  unfold analyzeTrail
  refine analyzeStep_all_empty trail lvl _ [[]] ?_
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · exact h
  · exact absurd h (by simp)

/-- A state whose conflict slot is the empty clause never enters the
    analysis arm: `analyzeConflict` returns `none`. -/
theorem analyzeConflict_empty_none {state : State}
    (h : state.conflict = some []) :
    analyzeConflict state = none := by
  unfold analyzeConflict
  rw [h]
  simp only []
  rw [analyzeTrail_empty]

/-! ## The analysis call's readiness -/

/-- The per-family reason-validity premise: every propagator's
    implied literal carries a VALID, normalized explanation — the
    clause is entailed by the internal problem and the pivot is a
    member. This is the analysis-side strengthening of the
    propagator contract (`PropSafe` covers exclusion only); the
    per-family discharge (each family's nogood lemma) is future
    work, so the premise is explicit here. -/
def ReasonSafeUniv (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) : Prop :=
  ∀ st, DomainCoherent problem st →
    ∀ p ∈ props, ∀ l r,
      p.run st = .implied l r →
      Reason.Valid problem constraintHolds r l ∧
        (∀ q ∈ r.clause, q = q.norm)

/-- The scan verdict's origin: every `scanAll` result comes from a
    clause of the active database. -/
theorem scanAll_mem
    {st : State} {res : Sum Clause (Literal × Reason)}
    (hscan : scanAll st = some res) :
    ∃ c, (c ∈ st.clauses ∨ c ∈ st.learned) ∧
      scanClause st c = some res := by
  -- scanAll.go closes over the fixed state and walks the active
  -- database (clauses ++ learned)
  have hgo0 : scanAll.go st (st.clauses ++ st.learned)
      = some res := by
    rw [← State.allClauses]
    exact hscan
  have main : ∀ (ds : List Clause),
      (∀ c2, c2 ∈ ds → c2 ∈ st.clauses ∨ c2 ∈ st.learned) →
      (scanAll.go st ds = some res) →
      ∃ c, c ∈ ds ∧ scanClause st c = some res := by
    intro ds
    induction ds with
    | nil =>
        intro _ hgo
        exact absurd hgo (by intro hcon; injection hcon)
    | cons c rest ih =>
      intro hmem hgo
      have hstep : (scanAll.go st (c :: rest)) =
          (match scanClause st c with
           | none => scanAll.go st rest
           | some r => some r) := rfl
      rw [hstep] at hgo
      cases hsc : scanClause st c with
      | none =>
          rw [hsc] at hgo
          obtain ⟨c2, hc2mem, hc2scan⟩ :=
            ih (fun c3 h3 => hmem c3 (List.mem_cons_of_mem _ h3)) hgo
          exact ⟨c2, List.mem_cons_of_mem _ hc2mem, hc2scan⟩
      | some verdict =>
          rw [hsc] at hgo
          injection hgo with hgo2
          cases hgo2
          exact ⟨c, List.mem_cons_self, hsc⟩
  obtain ⟨c, hcmem, hcscan⟩ :=
    main (st.clauses ++ st.learned)
      (fun c2 h2 => List.mem_append.mp h2) hgo0
  exact ⟨c, List.mem_append.mp hcmem, hcscan⟩

/-- The scan-unit reason inversion: when the scan reports a unit
    `(l, r)`, the reason is exactly `{ clause := c }` for the
    scanned clause and `l` is `c`'s only non-false literal. -/
theorem scanAll_unit_reason
    {st : State} {l : Literal} {r : Reason}
    (hscan : scanAll st = some (.inr (l, r))) :
    ∃ c, (c ∈ st.clauses ∨ c ∈ st.learned) ∧
      r = { clause := c } ∧ scanClause st c = some (.inr (l, r)) := by
  obtain ⟨c, hcmem, hcscan⟩ := scanAll_mem hscan
  refine ⟨c, hcmem, ?_, hcscan⟩
  unfold scanClause at hcscan
  split at hcscan
  · exact absurd hcscan (by simp)
  · match hh : c.filter (fun l2 => !st.negOnTrail l2) with
    | [] => rw [hh] at hcscan; exact absurd hcscan (by simp)
    | [l2] =>
        rw [hh] at hcscan
        injection hcscan with heq
        injection heq with heq2
        cases heq2
        rfl
    | l1 :: l2 :: rest =>
        rw [hh] at hcscan
        exact absurd hcscan (by simp)


/-- `enqueueNorm` preserves root facts when the fresh entry is above
    level 0: the level-0 entries are a sub-list of the old trail. -/
theorem enqueueNorm_rootFacts_pos
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hpos : st.decisionLevel ≠ 0)
    (h : RootFacts problem constraintHolds st.trail) :
    RootFacts problem constraintHolds
      (enqueueNorm st l0 reason).trail := by
  intro e he hzero a ha
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · rw [htr] at he; exact h e he hzero a ha
  · rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold hzero a ha
    · exfalso
      -- the fresh entry is stamped with the CURRENT (positive) level,
      -- so a level-0 requirement on it is impossible
      have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast] at hzero
      simp at hzero
      omega

/-- `enqueueNorm` preserves root facts at level 0 when the enqueued
    literal is true at every internal solution. -/
theorem enqueueNorm_rootFacts_level0
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (h : RootFacts problem constraintHolds st.trail)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    RootFacts problem constraintHolds
      (enqueueNorm st l0 reason).trail := by
  intro e he hzero a ha
  rcases enqueueNorm_trail_cases (st := st) (l := l0)
    (reason := reason) with htr | htr
  · rw [htr] at he; exact h e he hzero a ha
  · rw [htr] at he
    rcases List.mem_append.mp he with hold | hnew
    · exact h e hold hzero a ha
    · have hlast : e = TrailEntry.mk l0.norm st.decisionLevel reason :=
        by simpa using hnew
      rw [hlast]
      exact hlit a ha

/-! ## Propagation preserves the run invariant -/

/-- The propagator sweep's run-invariant preservation. Only implied
    literals are enqueued, with reasons validated by `ReasonSafeUniv`;
    conflicts stop the sweep (the caller consumes them); the shape
    fields all transfer through `enqueueNorm`'s field lemmas. The
    justification premise `hjust` supplies the implied literals' truth
    at every internal solution at LEVEL-0 coherent accumulators (the
    only place it is consumed: the fresh entry's RootFacts obligation
    in `enqueueNorm_rootFacts_level0`). Restricting to level 0 is
    what makes the premise dischargeable: at a positive decision
    level an implied literal is only true at every REPRESENTED
    solution (the decision's consequences), not at every internal
    problem solution, so the un-restricted premise would be false.
    Its per-family discharge is the same nogood argument as
    `PropSafe`'s impliedTrueAt, with the level-0 trail's
    falsification turning representation into problem-level truth. -/
theorem runPropagators_runInv
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hreason : ReasonSafeUniv problem constraintHolds props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem constraintHolds acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem constraintHolds a →
          l.norm.eval a = some true)
    (st : State)
    (hinv : RunInv problem constraintHolds props st) :
    RunInv problem constraintHolds props (runPropagators props st) := by
  -- the sweep threads the shape over the propagator list
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      DomainCoherent problem acc →
      acc.clauses = problem.clauses →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      (∀ e ∈ acc.trail, e.literal = e.literal.norm) →
      (∀ e ∈ acc.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm) →
      (∀ e ∈ acc.trail, ∀ r ∈ e.reason,
        Reason.Valid problem constraintHolds r e.literal) →
      (∀ c ∈ acc.learned, c.EntailedBy problem constraintHolds) →
      RootFacts problem constraintHolds acc.trail →
      (∀ c ∈ acc.clauses, ∀ l ∈ c, l = l.norm) →
      (∀ c ∈ acc.learned, ∀ l ∈ c, l = l.norm) →
      RunInv problem constraintHolds props (runPropagators.go ps acc) := by
    intro ps
    induction ps with
    | nil =>
        intro acc _ hcoh hcl hroot hnorm hreasonN hreasonV hlearned
          hrootF hclN hlnN
        have hgo : runPropagators.go [] acc = acc := rfl
        rw [hgo]
        exact ⟨hcoh, hcl, hlearned, hroot, hnorm, hreasonN, hreasonV,
          hrootF, hclN, hlnN⟩
    | cons p rest ih =>
        intro acc hmem hcoh hcl hroot hnorm hreasonN hreasonV hlearned
          hrootF hclN hlnN
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        simp only [runPropagators.go]
        split
        · -- already conflicting: the accumulator is returned
          exact ⟨hcoh, hcl, hlearned, hroot, hnorm, hreasonN, hreasonV,
            hrootF, hclN, hlnN⟩
        · rename_i hclear
          match hrun : p.run acc with
          | PropagationResult.stable =>
              show RunInv problem constraintHolds props
                (runPropagators.go rest acc)
              exact ih acc hrest hcoh hcl hroot hnorm hreasonN hreasonV
                hlearned hrootF hclN hlnN
          | PropagationResult.conflict c =>
              -- the sweep reports the conflict and stops: only the
              -- conflict slot changes
              exact ⟨hcoh, hcl, hlearned, hroot, hnorm, hreasonN,
                hreasonV, hrootF, hclN, hlnN⟩
          | PropagationResult.implied l r =>
              -- the reason side: ReasonSafeUniv at the coherent acc
              obtain ⟨hvalid, hnormr⟩ :=
                hreason acc hcoh p hp l r hrun
              have hfreshN : ∀ r2 ∈ (some r : Option Reason),
                  ∀ q ∈ r2.clause, q = q.norm := by
                intro r2 hr2 q hq
                cases hr2
                exact hnormr q hq
              -- the pivot is a member of the normalized clause, so
              -- the pivot itself is normalized: the validity for l
              -- transfers to the enqueued l.norm
              have hpivmem : l ∈ r.clause := by
                simpa using hvalid.2
              have hpivnorm : l = l.norm :=
                hnormr l hpivmem
              have hfreshV : ∀ r2 ∈ (some r : Option Reason),
                  Reason.Valid problem constraintHolds r2 l.norm := by
                intro r2 hr2
                cases hr2
                rw [← hpivnorm]
                exact hvalid
              have hcoh2 : DomainCoherent problem
                  (enqueueNorm acc l (some r)) :=
                enqueueNorm_domFold hcoh
              -- rootFacts: above level 0 the fresh entry is outside
              -- its scope; at level 0 the justification premise gives
              -- the literal's truth at every internal solution
              have hrootF2 : RootFacts problem constraintHolds
                  (enqueueNorm acc l (some r)).trail := by
                cases hlv : acc.decisionLevel with
                | zero =>
                    exact enqueueNorm_rootFacts_level0 hrootF
                      (hjust acc hcoh hlv hrootF hroot p hp l r hrun)
                | succ n =>
                    exact enqueueNorm_rootFacts_pos (by omega) hrootF
              have hclN2 : ∀ c2 ∈ (enqueueNorm acc l (some r)).clauses,
                  ∀ q ∈ c2, q = q.norm := by
                intro c2 hc2 q hq
                rw [enqueueNorm_clausesFixed hcl] at hc2
                exact hclN c2 (by rw [hcl]; exact hc2) q hq
              have hlnN2 : ∀ c2 ∈ (enqueueNorm acc l (some r)).learned,
                  ∀ q ∈ c2, q = q.norm := by
                intro c2 hc2 q hq
                have hln : (enqueueNorm acc l (some r)).learned
                    = acc.learned := by
                  simp only [enqueueNorm]
                  split
                  · rfl
                  · split
                    · rfl
                    · rfl
                rw [hln] at hc2
                exact hlnN c2 hc2 q hq
              exact ih (enqueueNorm acc l (some r)) hrest hcoh2
                (enqueueNorm_clausesFixed hcl)
                (enqueueNorm_rooted hroot)
                (enqueueNorm_trailNorm hnorm)
                (enqueueNorm_reasonNorm hreasonN hfreshN)
                (enqueueNorm_reasonValid hreasonV hfreshV)
                (enqueueNorm_learnedEntailed hlearned)
                hrootF2 hclN2 hlnN2
  exact main props st (fun q hq => hq) hinv.coherent hinv.clausesFixed
    hinv.rooted hinv.trailNorm hinv.reasonNorm hinv.reasonValid
    hinv.learnedEntailed hinv.rootFacts hinv.clausesNorm
    hinv.learnedNorm

/-! ## The propagation loop and the repair -/

/-- `RunInv` does not mention the conflict slot: setting it leaves
    every component intact. -/
theorem runInv_conflictUpdate
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {st : State} {cc : Option Clause}
    (h : RunInv problem constraintHolds props st) :
    RunInv problem constraintHolds props { st with conflict := cc } := by
  -- every field projects the same components; the record update is
  -- definitionally the same projections
  cases h
  rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The propagation loop preserves the run invariant (the
    conflict-carrying outcome keeps the state's shape with the
    conflict set; the caller distinguishes the two by the conflict
    slot). The scan-unit arm's reason is the scanned active clause
    (entitled by the databases), and its fresh-entry obligations
    follow from the scan's unit shape; the propagator arm is
    `runPropagators_runInv`. -/
theorem propagateLoop_runInv
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hreason : ReasonSafeUniv problem constraintHolds props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem constraintHolds acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem constraintHolds a →
          l.norm.eval a = some true)
    (hdb : ∀ c ∈ problem.clauses,
      c.EntailedBy problem constraintHolds)
    : ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      RunInv problem constraintHolds props st →
      RunInv problem constraintHolds props
        (propagateLoop fuel props st) := by
  intro fuel
  induction fuel with
  | zero => intro st _ hinv; exact hinv
  | succ fuel ih =>
      intro st hnone hinv
      simp only [propagateLoop]
      split
      · -- conflict-carrying entry: impossible (hnone)
        rename_i hconf
        rw [Option.isSome_iff_exists] at hconf
        obtain ⟨c, hc⟩ := hconf
        rw [hc] at hnone
        exact absurd hnone (by simp)
      · rename_i hclear
        cases hscan : scanAll st with
        | none =>
            -- the goal is already the if-shape (the simp only
            -- [propagateLoop] + hscan case substituted it)
            by_cases hlen : ((runPropagators props st).trail.length ==
                st.trail.length) = true
            · -- quiesced: the swept state is the loop's answer
              rw [if_pos hlen]
              exact runPropagators_runInv hreason hjust st hinv
            · -- extended: recurse at the swept state. A
              -- conflict-carrying swept state is returned UNCHANGED
              -- by the loop head (the `if conflict.isSome then st`
              -- guard fires first), so the invariant is the swept
              -- state's own; a conflict-free swept state goes to the
              -- induction hypothesis
              rw [if_neg hlen]
              by_cases hconf2 : (runPropagators props st).conflict = none
              · exact ih (runPropagators props st) hconf2
                  (runPropagators_runInv hreason hjust st hinv)
              · -- the swept state carries the conflict: the loop
                -- head returns it as-is
                have hret : propagateLoop fuel props
                    (runPropagators props st)
                    = runPropagators props st := by
                  cases hfuel : fuel with
                  | zero => rfl
                  | succ k =>
                      show (propagateLoop (k + 1) props
                        (runPropagators props st))
                        = runPropagators props st
                      unfold propagateLoop
                      have hissome : (runPropagators props
                          st).conflict.isSome = true := by
                        cases hc3 : (runPropagators props st).conflict with
                        | none => exact absurd hc3 hconf2
                        | some c =>
                            rw [Option.isSome_iff_exists]
                            exact ⟨c, rfl⟩
                      rw [if_pos hissome]
                rw [hret]
                exact runPropagators_runInv hreason hjust st hinv
        | some verdict =>
            match verdict with
            | Sum.inl c =>
                -- scan conflict: the returned state is st with the
                -- conflict set; every shape field is unchanged
                exact runInv_conflictUpdate hinv
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                -- scan unit: enqueue l with reason r
                obtain ⟨cc, hcmem, hreq, hcscan⟩ :=
                  scanAll_unit_reason (st := st) hscan
                -- the reason is the active clause cc (entitled):
                -- an original clause by the fixed-database premise
                -- (the problem's clause entitlement), a learned one
                -- by the invariant
                have hent : cc.EntailedBy problem constraintHolds := by
                  rcases hcmem with hc | hc
                  · exact hdb cc (by rw [← hinv.clausesFixed]; exact hc)
                  · exact hinv.learnedEntailed cc hc
                -- the reason's validity: the clause is entitled and
                -- the reason's clause is the active clause cc: its
                -- normalization and entitlement follow from the
                -- database it belongs to
                -- the reason's validity: the clause is entitled and
                -- the unit literal is a member of the scanned clause
                -- l is the scan's filter output: a member of cc,
                -- and cc's only non-trail-false literal
                have hfil : l ∈ cc ∧ ∀ q ∈ cc, q ≠ l →
                    st.negOnTrail q = true := by
                  have hrw : scanClause st cc
                      = some (.inr (l, { clause := cc })) := by
                    rw [← hreq]
                    exact hcscan
                  unfold scanClause at hrw
                  split at hrw
                  · exact absurd hrw (by simp)
                  · match hh : cc.filter (fun l2 => !st.negOnTrail l2) with
                    | [] => rw [hh] at hrw; exact absurd hrw (by simp)
                    | [l2] =>
                        rw [hh] at hrw
                        have hll : l = l2 := by
                          injection hrw with h1
                          injection h1 with h2
                          cases h2
                          rfl
                        have hl2mem : l2 ∈ cc.filter
                            (fun l2 => !st.negOnTrail l2) :=
                          by rw [hh]; exact List.mem_cons_self
                        refine ⟨by rw [hll]; exact (List.mem_filter.mp hl2mem).1,
                          ?_⟩
                        intro q hq hne
                        by_cases hneg : st.negOnTrail q = true
                        · exact hneg
                        · exfalso
                          have hqmem : q ∈ cc.filter
                              (fun l2 => !st.negOnTrail l2) :=
                            List.mem_filter.mpr ⟨hq, by
                              simp only [Bool.not_eq_true']
                              exact Bool.not_eq_true (st.negOnTrail q) |>.mp hneg⟩
                          rw [hh] at hqmem
                          have hq2 : q = l2 := by
                            rcases List.mem_cons.mp hqmem with hq3 | hq3
                            · exact hq3
                            · cases hq3
                          rw [hq2, hll] at hne
                          exact hne rfl
                    | l1 :: l2 :: rest =>
                        rw [hh] at hrw
                        exact absurd hrw (by simp)
                have hrv : Reason.Valid problem constraintHolds r l := by
                  rw [hreq]
                  exact ⟨hent, by simpa using hfil.1⟩
                have hrn : ∀ q ∈ r.clause, q = q.norm := by
                  intro q hq
                  rw [hreq] at hq
                  rcases hcmem with hcc | hcc
                  · exact hinv.clausesNorm cc hcc q hq
                  · exact hinv.learnedNorm cc hcc q hq
                -- the fresh-entry obligations for enqueueNorm
                have hfreshN : ∀ r2 ∈ (some r : Option Reason),
                    ∀ q ∈ r2.clause, q = q.norm := by
                  intro r2 hr2 q hq
                  cases hr2
                  exact hrn q hq
                have hfreshV : ∀ r2 ∈ (some r : Option Reason),
                    Reason.Valid problem constraintHolds r2 l.norm := by
                  intro r2 hr2
                  cases hr2
                  -- the pivot is a member of the normalized reason
                  -- clause, hence normalized; validity transfers
                  have hpiv : l = l.norm := hrn l (by
                    simpa using hrv.2)
                  rw [← hpiv]
                  exact hrv
                -- root facts: above level 0 the fresh entry is out of
                -- scope; at level 0 the unit literal is true at every
                -- solution — the clause is entitled and its OTHER
                -- literals are trail-false (the scan's filter); the
                -- trail-facts-at-solutions half is exactly the
                -- RootFacts the invariant already carries over the
                -- level-0 subtrail plus the represented-solutions
                -- argument. The unit case: every other literal of cc
                -- is negOnTrail — falsified at every solution
                -- satisfying the trail — so l must be the witness.
                have hrootF2 : RootFacts problem constraintHolds
                    (enqueueNorm st l (some r)).trail := by
                  cases hlv : st.decisionLevel with
                  | zero =>
                      refine enqueueNorm_rootFacts_level0 hinv.rootFacts
                        (fun a ha => ?_)
                      -- the clause cc is entitled: some witness is
                      -- true at a; every OTHER literal is
                      -- trail-false, and at level 0 the trail is
                      -- true at every solution (htrail0), making
                      -- those witnesses false — so l is the witness
                      obtain ⟨w, hw, hev⟩ := hent a ha
                      -- l is a member of the normalized active clause
                      have hlnorm : l = l.norm := by
                        rcases hcmem with hcc | hcc
                        · exact hinv.clausesNorm cc hcc l hfil.1
                        · exact hinv.learnedNorm cc hcc l hfil.1
                      by_cases hwl : w = l
                      · rw [← hwl, Literal.norm_eval w a]
                        exact hev
                      · exfalso
                        have hneg := hfil.2 w hw hwl
                        -- at level 0, RootFacts (hinv.rootFacts)
                        -- gives trail truth at every solution
                        have htr : st.TrailSatisfied a := by
                          intro e he2
                          have hle : e.level ≤ st.decisionLevel :=
                            hinv.rooted e he2
                          rw [hlv] at hle
                          have hzero : e.level = 0 := Nat.le_zero.mp hle
                          exact hinv.rootFacts e he2 hzero a ha
                        have hfals : w.eval a = some false :=
                          negOnTrail_falsifies_entry hneg htr
                        rw [hev] at hfals
                        exact absurd hfals (by simp)
                  | succ n =>
                      exact enqueueNorm_rootFacts_pos (by omega)
                        hinv.rootFacts
                -- assemble the post-enqueue invariant and recurse
                have hinv2 : RunInv problem constraintHolds props
                    (enqueueNorm st l (some r)) :=
                  ⟨enqueueNorm_domFold hinv.coherent,
                    enqueueNorm_clausesFixed hinv.clausesFixed,
                    enqueueNorm_learnedEntailed hinv.learnedEntailed,
                    enqueueNorm_rooted hinv.rooted,
                    enqueueNorm_trailNorm hinv.trailNorm,
                    enqueueNorm_reasonNorm hinv.reasonNorm hfreshN,
                    enqueueNorm_reasonValid hinv.reasonValid hfreshV,
                    hrootF2,
                    fun c2 hc2 q hq => by
                      rw [enqueueNorm_clausesFixed hinv.clausesFixed] at hc2
                      exact hinv.clausesNorm c2 (by
                        rw [hinv.clausesFixed]; exact hc2) q hq,
                    fun c2 hc2 q hq => by
                      have hln : (enqueueNorm st l (some r)).learned
                          = st.learned := by
                        simp only [enqueueNorm]
                        split
                        · rfl
                        · split
                          · rfl
                          · rfl
                      rw [hln] at hc2
                      exact hinv.learnedNorm c2 hc2 q hq⟩
                have hnone2 : (enqueueNorm st l (some r)).conflict = none := by
                  -- the filter test: the scan kept l among the
                  -- not-trail-false literals of cc, so the negation
                  -- of l is not on the trail; l is normalized (a
                  -- member of the normalized active clause), so the
                  -- test transfers to the enqueued l.norm
                  have hlnotfalse : (!st.negOnTrail l) = true := by
                    have hrw2 : scanClause st cc
                        = some (.inr (l, { clause := cc })) := by
                      rw [← hreq]
                      exact hcscan
                    unfold scanClause at hrw2
                    split at hrw2
                    · exact absurd hrw2 (by simp)
                    · match hh2 : cc.filter
                          (fun l2 => !st.negOnTrail l2) with
                      | [] =>
                          rw [hh2] at hrw2
                          exact absurd hrw2 (by simp)
                      | [l2] =>
                          have hl2 : l = l2 := by
                            rw [hh2] at hrw2
                            injection hrw2 with h1
                            injection h1 with h2
                            cases h2
                            rfl
                          have hl2mem : l2 ∈ cc.filter
                              (fun l2 => !st.negOnTrail l2) := by
                            rw [hh2]; exact List.mem_cons_self
                          rw [hl2]
                          exact (List.mem_filter.mp hl2mem).2
                      | l1 :: l2 :: rest =>
                          rw [hh2] at hrw2
                          exact absurd hrw2 (by simp)
                  have hnegr : st.negOnTrail l = false := by
                    have htmp := hlnotfalse
                    simp only [Bool.not_eq_true'] at htmp
                    exact htmp
                  have hln2 : l = l.norm := by
                    rcases hcmem with hcc | hcc
                    · exact hinv.clausesNorm cc hcc l hfil.1
                    · exact hinv.learnedNorm cc hcc l hfil.1
                  -- the three enqueueNorm arms: skip returns the
                  -- conflict-free entry state; opposing needs
                  -- negOnTrail l.norm — impossible; fresh keeps the
                  -- clear conflict slot
                  simp only [enqueueNorm]
                  split
                  · -- skip: the entry state itself
                    show st.conflict = none
                    exact hnone
                  · split
                    · -- opposing: the negation is not on the trail
                      exfalso
                      rename_i hneg
                      rw [← hln2] at hneg
                      rw [hnegr] at hneg
                      exact absurd hneg (by simp)
                    · -- fresh: neither enqueue nor the domain
                      -- replacement touches the conflict slot
                      show st.conflict = none
                      exact hnone
                exact ih (enqueueNorm st l (some r)) hnone2 hinv2

/-! ## The repair transition -/

/-- `repairAfterBackjump` preserves the run invariant: the kept
    subtrail's entries keep their levels (≤ the repair level ≤ the
    old decision level), the domains are rebuilt as the kept-trail
    fold, and both databases are untouched. -/
theorem repair_runInv
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    {level : Nat} {st : State}
    (hinv : RunInv problem constraintHolds props st)
    (hle : level ≤ st.decisionLevel) :
    RunInv problem constraintHolds props
      (repairAfterBackjump problem level st) := by
  -- the kept trail is a filter of the old: memberships transfer
  have hkept : ∀ e ∈ (repairAfterBackjump problem level st).trail,
      e ∈ st.trail := by
    intro e he
    unfold repairAfterBackjump at he
    exact (List.mem_filter.mp he).1
  -- the kept entries' levels are ≤ level ≤ st.decisionLevel, and
  -- the repaired decision level IS level
  have hroot : ∀ e ∈ (repairAfterBackjump problem level st).trail,
      e.level ≤ (repairAfterBackjump problem level st).decisionLevel := by
    intro e he
    have hmem := hkept e he
    have hle2 : e.level ≤ level := by
      unfold repairAfterBackjump at he
      exact of_decide_eq_true (List.mem_filter.mp he).2
    have hdl : (repairAfterBackjump problem level st).decisionLevel
        = level := rfl
    rw [hdl]
    exact hle2
  refine ⟨?_, ?_, ?_, hroot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- coherent: the repaired domains are the kept-trail fold
    exact repair_domFold
  · -- clauses fixed: repair does not touch the database
    have hcl : (repairAfterBackjump problem level st).clauses
        = st.clauses := rfl
    rw [hcl, hinv.clausesFixed]
  · -- learned entailed: membership transfers through the unchanged
    -- learned field
    intro c hc
    have hcl : (repairAfterBackjump problem level st).learned
        = st.learned := rfl
    rw [hcl] at hc
    exact hinv.learnedEntailed c hc
  · -- trail norm: memberships transfer
    intro e he
    exact hinv.trailNorm e (hkept e he)
  · -- reason norm
    intro e he r hr l hl
    exact hinv.reasonNorm e (hkept e he) r hr l hl
  · -- reason valid
    intro e he r hr
    exact hinv.reasonValid e (hkept e he) r hr
  · -- root facts: the kept subtrail's level-0 entries are old ones
    intro e he hzero a ha
    exact hinv.rootFacts e (hkept e he) hzero a ha
  · -- clauses norm
    intro c hc l hl
    exact hinv.clausesNorm c hc l hl
  · -- learned norm
    intro c hc l hl
    exact hinv.learnedNorm c hc l hl

/-! ## The master run induction -/


/-- **THE ANALYSIS-CALL READINESS (§3 item 2, the plan's central
    obligation)**: at the engine's positive-level conflict arm, the
    analyzed state — the propagated state of a run-invariant,
    conflict-free loop entry — is `AnalysisReady`: its conflict clause
    is entitled (the caller's front-door premise, discharged by
    `propagateLoop_conflict_entitled`), every reason is valid and
    normalized, and the root facts hold. `analyzeConflict_correct`
    then applies, so the learned clause is entailed and the backjump
    level is sound. -/
theorem analysis_ready_at_conflict
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator}
    (hreason : ReasonSafeUniv problem constraintHolds props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem constraintHolds acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem constraintHolds a →
          l.norm.eval a = some true)
    (hdb : ∀ c ∈ problem.clauses,
      c.EntailedBy problem constraintHolds)
    (st : State)
    (hnone : st.conflict = none)
    (hinv : RunInv problem constraintHolds props st)
    (hconf : (propagateLoop (engineFuel st) props st).conflict.isSome
      = true)
    (hconfent : ∀ c, (propagateLoop (engineFuel st) props st).conflict
        = some c → c ≠ [] →
        c.EntailedBy problem constraintHolds)
    (hanalyze : analyzeConflict (propagateLoop (engineFuel st) props st)
      ≠ none)
:
    (propagateLoop (engineFuel st) props st).AnalysisReady problem
        constraintHolds ∧
      (∀ e ∈ (propagateLoop (engineFuel st) props st).trail,
        e.level ≤ (propagateLoop (engineFuel st) props
          st).decisionLevel) := by
  -- the propagated state's run invariant
  have hinv1 := propagateLoop_runInv hreason hjust hdb
    (engineFuel st) st hnone hinv
  refine ⟨⟨?_, hinv1.reasonValid, hinv1.rootFacts,
    hinv1.reasonNorm⟩, hinv1.rooted⟩
  · -- the conflict clause's entitlement
    intro cc hcc
    cases hc2 : (propagateLoop (engineFuel st) props st).conflict with
    | none =>
        rw [hc2] at hconf
        exact absurd hconf (by simp)
    | some c =>
        rw [hc2] at hcc
        have hccc : cc = c := by
          cases hcc
          rfl
        rw [hccc]
        -- nonemptiness from analyzability: an empty conflict clause
        -- never analyzes (analyzeStep skips it; nextPivot on the
        -- empty marks is none)
        have hcne : c ≠ [] := by
          intro hempty
          rw [hempty] at hc2
          rw [analyzeConflict_empty_none hc2] at hanalyze
          exact absurd hanalyze (by simp)
        exact hconfent c hc2 hcne



/-! ## Decision descent (§3 item 3): the level-0 invariant -/

/-- The level-0 solution-representation invariant: every internal
    solution is represented by the state's LEVEL-0 PROJECTION — the
    sub-trail of level-0 entries, domains rebuilt from it. This is the
    per-state statement that survives DECISIONS (a decision stamps a
    positive level, so the level-0 projection is untouched) and
    BACKJUMPS (the repair filter keeps the level-0 subtrail). -/
def Level0Solved (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
    SolvedBy problem constraintHolds
      (repairAfterBackjump problem 0 st)

/-- The repair's domains fit any assignment fitting the fold's start
    (the rebuilt domains are the kept-trail fold from the problem's
    own domains — a sub-fold of the full one; membership in the
    ORIGINAL problem domains bounds every kept step). -/
theorem repair0_fits
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {a : Assignment} (ha : a.Fits problem.domains)
    {st : State} (htrue : ∀ e ∈ st.trail, e.level ≤ 0 →
      e.literal.eval a = some true) :
    a.Fits (repairAfterBackjump problem 0 st).domains := by
  exact fold_fits (st.trail.filter (fun e => decide (e.level ≤ 0))) a
    problem.domains ha
    (fun e he => htrue e ((List.mem_filter.mp he).1) (by
      have hle := (List.mem_filter.mp he).2
      exact of_decide_eq_true hle))

/-- At a level-0 state with only level-0 entries, `Level0Solved`
    transfers to the state itself: the kept trail is the whole trail,
    the rebuilt domains fit (fold from the problem's domains), the
    databases are the state's own fields. -/
theorem level0Solved_solvedBy
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State}
    (hlevel : st.decisionLevel = 0)
    (hrooted : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel)
    (hcoh : DomainCoherent problem st)
    (h : Level0Solved problem constraintHolds st) :
    SolvedBy problem constraintHolds st := by
  -- at level 0 the repair keeps the whole trail, so the level-0
  -- projection's trail IS the state's trail
  have hfil : st.trail.filter (fun e => decide (e.level ≤ 0))
      = st.trail := by
    rw [List.filter_eq_self]
    intro e he
    have hle : e.level ≤ 0 := by rw [← hlevel]; exact hrooted e he
    simpa using hle
  intro a ha
  obtain ⟨hfit0, htrail0, hcl0, hln0⟩ := h a ha
  have htrail : st.TrailSatisfied a := by
    intro e he
    exact htrail0 e (by
      unfold repairAfterBackjump
      rw [hfil]
      exact he)
  refine ⟨?_, htrail, hcl0, hln0⟩
  · -- at level 0 the whole trail is kept, so the repair's fold IS
    -- the state's fold (coherence): the domains coincide
    have hdom : (repairAfterBackjump problem 0 st).domains
        = st.domains := by
      show (let kept := st.trail.filter (fun e => decide (e.level ≤ 0))
            let doms := kept.foldl (fun acc e => domOfLit acc e.literal)
              problem.domains
            doms) = st.domains
      simp only [hfil]
      exact hcoh.symm
    rw [← hdom]
    exact repair0_fits (problem := problem) ha.1
      (fun e he _ => htrail e he)

/-- Filter commutation for the repair filters: keeping level-0
    entries commutes with any other level filter (level-0 is the
    smallest). -/
theorem repair_filter_comm (l : List TrailEntry) (level : Nat) :
    (l.filter (fun e => decide (e.level ≤ level))).filter
      (fun e => decide (e.level ≤ 0))
    = l.filter (fun e => decide (e.level ≤ 0)) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      by_cases hle : e.level ≤ 0
      · have hd0 : (decide (e.level ≤ 0)) = true :=
          of_decide_eq_true (by simpa using hle)
        have hdL : (decide (e.level ≤ level)) = true :=
          of_decide_eq_true (by
            have hh : e.level ≤ level := Nat.le_trans hle (Nat.zero_le level)
            simpa using hh)
        simp only [List.filter_cons, hdL, hd0, if_true]
        exact congrArg (e :: ·) ih
      · have hd0 : ¬((decide (e.level ≤ 0)) = true) := by
          simpa using hle
        simp only [List.filter_cons]
        by_cases hdL : (decide (e.level ≤ level)) = true
        · simp only [hdL, if_true]
          simp only [List.filter_cons, hd0, Bool.not_eq_true', if_false]
          exact ih
        · simp only [hdL, if_false]
          simp only [List.filter_cons, hd0, Bool.not_eq_true', if_false]
          exact ih

/-- Repair-to-zero is idempotent under further repairs: the level-0
    projection of a repaired state is the level-0 projection of the
    original. -/
theorem repair0_repair (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (level : Nat) (st : State) :
    repairAfterBackjump problem 0 (repairAfterBackjump problem level st)
      = repairAfterBackjump problem 0 st := by
  unfold repairAfterBackjump
  simp only
  rw [repair_filter_comm]

/-- The decision enqueue's fresh entry is stamped above level 0, so
    the level-0 projection ignores it; the skip and opposing arms
    leave the trail unchanged. -/
theorem repair0_decision (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (st : State) (l : Literal) :
    repairAfterBackjump problem 0
        (enqueueNorm (newDecisionLevel st) l none)
      = repairAfterBackjump problem 0 st := by
  unfold repairAfterBackjump
  simp only [enqueueNorm]
  split
  · -- skip arm: the state is unchanged
    rfl
  · split
    · -- opposing arm: the conflict slot is set; the repair clears it
      rfl
    · -- fresh arm: the enqueue's trail equation and the 0-filter drop
      have htr : (enqueue (newDecisionLevel st) l.norm none).trail
          = st.trail ++ [TrailEntry.mk l.norm (st.decisionLevel + 1) none] := rfl
      rw [htr]
      have hfil : (st.trail ++ [TrailEntry.mk l.norm (st.decisionLevel + 1)
          none]).filter (fun e => decide (e.level ≤ 0))
          = st.trail.filter (fun e => decide (e.level ≤ 0)) := by
        rw [List.filter_append]
        have hnil : List.filter (fun e => decide (e.level ≤ 0))
            [TrailEntry.mk l.norm (st.decisionLevel + 1) none] = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [if_neg]
          intro hcon
          have hh : (TrailEntry.mk l.norm (st.decisionLevel + 1) none).level
              ≤ 0 := of_decide_eq_true hcon
          simp at hh
        rw [hnil, List.append_nil]
      rw [hfil]
      -- the remaining fields coincide (enqueue only extends the trail)
      rfl

/-- Decisions preserve the level-0 projection: the fresh entry is
    stamped at the (positive) new level, so the repair-0 filter drops
    it and the level-0 subtrail is unchanged. -/
theorem level0Solved_decision
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l : Literal}
    (h : Level0Solved problem constraintHolds st) :
    Level0Solved problem constraintHolds
      (enqueueNorm (newDecisionLevel st) l none) := by
  rw [Level0Solved, repair0_decision, ← Level0Solved]
  exact h

/-- Backjump repairs preserve the level-0 projection. -/
theorem level0Solved_repair
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {level : Nat}
    (h : Level0Solved problem constraintHolds st) :
    Level0Solved problem constraintHolds
      (repairAfterBackjump problem level st) := by
  rw [Level0Solved, repair0_repair, ← Level0Solved]
  exact h


/-- The propagator sweep preserves rootedness. -/
theorem runPropagators_rooted (props : List Propagator) (st : State)
    (h : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel) :
    ∀ e ∈ (runPropagators props st).trail,
      e.level ≤ (runPropagators props st).decisionLevel := by
  -- the sweep's internal fold over the propagator list
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ e ∈ (runPropagators.go ps acc).trail,
        e.level ≤ (runPropagators.go ps acc).decisionLevel := by
    intro ps
    induction ps with
    | nil => intro acc _ h; exact h
    | cons p rest ih =>
        intro acc hmem h
        simp only [runPropagators.go]
        split
        · exact h
        · rename_i hclear
          match hrun : p.run acc with
          | PropagationResult.stable =>
              exact ih acc (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) h
          | PropagationResult.conflict c => exact h
          | PropagationResult.implied l r =>
              show ∀ e ∈ (runPropagators.go rest
                (enqueueNorm acc l (some r))).trail,
                e.level ≤ (runPropagators.go rest
                  (enqueueNorm acc l (some r))).decisionLevel
              exact ih (enqueueNorm acc l (some r))
                (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
                (enqueueNorm_rooted h)
  exact main props st (fun q hq => hq) h



/-- The propagation loop preserves rootedness: it only enqueues at
    the current decision level (which it never changes). -/
theorem propagateLoop_rooted
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      (∀ e ∈ st.trail, e.level ≤ st.decisionLevel) →
      ∀ e ∈ (propagateLoop fuel props st).trail,
        e.level ≤ (propagateLoop fuel props st).decisionLevel := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
      intro st h
      simp only [propagateLoop]
      split
      · -- conflict-carrying entry: impossible (contradicts none? no —
        -- the entry may carry a conflict from an OUTER caller; the
        -- loop returns it unchanged)
        exact h
      · rename_i hclear
        cases hscan : scanAll st with
        | none =>
            -- the goal is already the if-shape (the case
            -- substitution rewrote the loop head)
            by_cases hlen : ((runPropagators props st).trail.length ==
                st.trail.length) = true
            · -- quiesced: the sweep's rootedness
              rw [if_pos hlen]
              exact runPropagators_rooted props st h
            · -- extended: recurse at the swept state
              rw [if_neg hlen]
              exact ih (runPropagators props st)
                (runPropagators_rooted props st h)
        | some verdict =>
            match verdict with
            | Sum.inl c => exact h
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                -- scan-unit enqueue at the current level
                have hroot2 : ∀ e ∈ (enqueueNorm st l (some r)).trail,
                    e.level ≤ (enqueueNorm st l (some r)).decisionLevel :=
                  enqueueNorm_rooted h
                exact ih (enqueueNorm st l (some r)) hroot2

/-- Level-0 propagation preserves the level-0 solution
    representation whenever the loop's answer is CONFLICT-FREE (the
    only case the engine continues from); a conflict-carrying answer
    is consumed terminally at level 0. The proof: the entry is
    level-0 with all entries at level 0 (so `Level0Solved` = `SolvedBy`
    via `level0Solved_solvedBy`), the existing `propagateLoop_solvedBy`
    threads `SolvedBy` to the conflict-free answer, and the answer
    stays at level 0 with all entries at level 0 (propagation never
    changes the level), so its own `Level0Solved` holds. -/
theorem level0Solved_propagate_clear
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (fuel : Nat) (st : State)
    (hlevel : st.decisionLevel = 0)
    (hrooted : ∀ e ∈ st.trail, e.level ≤ st.decisionLevel)
    (hnone : st.conflict = none)
    (hcoh : DomainCoherent problem st)
    (hL0 : Level0Solved problem constraintHolds st)
    (hclear : (propagateLoop fuel props st).conflict = none) :
    Level0Solved problem constraintHolds
      (propagateLoop fuel props st) := by
  -- the entry is solved-by
  have hsolved : SolvedBy problem constraintHolds st :=
    level0Solved_solvedBy hlevel hrooted hcoh hL0
  -- the existing theorem threads it (with the entry's databases:
  -- both database fields of the level-0 projection are st's own
  -- fields, and hL0's representation gives their entitlement)
  have hclent : ∀ c ∈ st.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true := by
    intro c hc a ha
    have hrep := hL0 a ha
    -- the projection's clauses field is st.clauses
    have hcf : (repairAfterBackjump problem 0 st).clauses
        = st.clauses := rfl
    rw [← hcf] at hc
    exact hrep.2.2.1 c hc
  have hlnent : ∀ c ∈ st.learned, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true := by
    intro c hc a ha
    have hrep := hL0 a ha
    have hlf : (repairAfterBackjump problem 0 st).learned
        = st.learned := rfl
    rw [← hlf] at hc
    obtain ⟨wl, hwl, hev⟩ := hrep.2.2.2 c hc
    exact ⟨wl, hwl, hev⟩
  have hsolved2 : SolvedBy problem constraintHolds
      (propagateLoop fuel props st) :=
    propagateLoop_solvedBy hsafe hsolvable st.clauses st.learned
      hclent hlnent
      fuel st hnone hsolved hcoh
      rfl rfl hclear
  -- the answer is at level 0 (the loop never changes the level:
  -- propagateLoop_decisionLevel) with all entries at level 0
  -- (rootedness is preserved by runInv-free transfer: propagation
  -- enqueues at the current level), so its level-0 projection is
  -- itself up to the cleared conflict; the level-0 solved-ness is
  -- exactly hsolved2 read through the projection
  have hlevel2 : (propagateLoop fuel props st).decisionLevel = 0 := by
    rw [propagateLoop_decisionLevel props fuel st]
    exact hlevel
  -- every entry of the answer is at level 0: propagation only
  -- enqueues at the current (0) level, and repairs never occur
  -- inside the loop
  have hrooted2 : ∀ e ∈ (propagateLoop fuel props st).trail,
      e.level ≤ (propagateLoop fuel props st).decisionLevel := by
    exact propagateLoop_rooted fuel st hrooted
  -- SolvedBy of the answer + level-0 shape gives Level0Solved: the
  -- answer's level-0 projection keeps the whole trail (all entries
  -- at level 0) and both databases; the domains are rebuilt by the
  -- same fold; and the fits half comes from the entry state's own
  -- problem-domains fits (every solution fits the problem's
  -- domains — ProblemSolution's first conjunct)
  intro a ha
  have hrep := hsolved2 a ha
  obtain ⟨hfit, htrail, hcl, hln⟩ := hrep
  refine ⟨?_, ?_, hcl, hln⟩
  · -- Fits of the rebuilt domains: the fold fires from
    -- problem.domains, which fits a (ProblemSolution's own conjunct)
    exact repair0_fits (problem := problem) ha.1
      (fun e he _ => htrail e he)
  · -- trail satisfaction: the kept trail is the whole trail (all
    -- entries at level 0), so the repair's membership is the
    -- state's own
    intro e he
    have hfil : List.filter (fun e => decide (e.level ≤ 0))
        (propagateLoop fuel props st).trail
        = (propagateLoop fuel props st).trail := by
      rw [List.filter_eq_self]
      intro e2 he2
      have hle : e2.level ≤ (propagateLoop fuel props st).decisionLevel :=
        hrooted2 e2 he2
      rw [hlevel2] at hle
      simpa using hle
    have hmem : e ∈ (propagateLoop fuel props st).trail :=
      hfil ▸ he
    exact htrail e hmem


/-- The analysis arm's level-0 descent step: when the conflict is
    analyzed at decision level 0 with backjump level 0, the asserting
    literal is TRUE at every internal solution — the learned clause is
    entailed (`analyzeConflict_correct` at the AnalysisReady state),
    and its below literals are level-0 trail facts (true at every
    solution by `Level0Solved`), so each is not a satisfying witness
    and the asserting literal must be. -/
theorem asserting_true_at_solutions
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st1 : State} {an : ConflictAnalysis}
    (hready : st1.AnalysisReady problem constraintHolds)
    (hstate : st1.WellFormed problem constraintHolds)
    (hanalyze : analyzeConflict st1 = some an)
    (hlevel1 : st1.decisionLevel = 0)
    (hrooted1 : ∀ e ∈ st1.trail, e.level ≤ st1.decisionLevel)
    (hL0 : Level0Solved problem constraintHolds st1)
    -- the below-literals falsification: every NON-asserting literal
    -- of the learned clause is the negation of a level-0 trail entry
    -- (the analyzer's markLit records exactly the falsified events
    -- with their falsifiers on the trail; at level 0 those falsifier
    -- entries are level-0 facts, true at every solution, so the
    -- below literals are false at every solution). Its discharge is
    -- the analyzer's falsifier-chain lemma (the registered gap of
    -- the Analyze layer).
    (hbelow : ∀ q ∈ an.learned, q ≠ an.asserting →
      ∃ e ∈ st1.trail, e.level = 0 ∧
        e.literal = q.negate.norm)
    (a : Assignment)
    (ha : ProblemSolution problem constraintHolds a) :
    an.asserting.norm.eval a = some true := by
  -- the learned clause is entailed
  obtain ⟨hent, _, _⟩ :=
    analyzeConflict_correct (problem := problem)
      (constraintHolds := constraintHolds) hstate hready hanalyze
  -- the learned clause's shape: uip.negate :: below.map (·.1); the
  -- asserting literal IS uip.negate
  -- at a level-0 state the below literals are level-0 trail facts:
  -- each is FALSE at a (they are the negations of true facts)
  -- so the asserting literal is the only possible witness
  obtain ⟨w, hw, hev⟩ := hent a ha
  by_cases hwa : w = an.asserting
  · -- w IS the asserting literal; normalize
    rw [← hwa]
    rw [Literal.norm_eval w a]
    exact hev
  · -- w is a below literal: falsified at a by the level-0 facts
    obtain ⟨e, hemem, _, hfals⟩ := hbelow w hw hwa
    -- the level-0 subtrail of st1 IS st1's whole trail (all entries
    -- at level 0), so the falsifier entry is a represented fact
    have hfil : List.filter (fun e2 => decide (e2.level ≤ 0)) st1.trail
        = st1.trail := by
      rw [List.filter_eq_self]
      intro e2 he2
      have hle : e2.level ≤ st1.decisionLevel := hrooted1 e2 he2
      rw [hlevel1] at hle
      simpa using hle
    have hrep := hL0 a ha
    have hetrue : e.literal.eval a = some true := by
      have hmem : e ∈ (repairAfterBackjump problem 0 st1).trail := by
        show e ∈ List.filter (fun e2 => decide (e2.level ≤ 0)) st1.trail
        rw [hfil]
        exact hemem
      exact hrep.2.1 e hmem
    -- derive w false at a: the entry's literal is w.negate.norm and
    -- is TRUE at a, so w is false
    rw [hfals] at hetrue
    rw [Literal.norm_eval w.negate a] at hetrue
    rw [Literal.eval_negate w a] at hetrue
    cases hw2 : w.eval a with
    | none => rw [hw2] at hetrue; exact absurd hetrue (by simp)
    | some b =>
        rw [hw2] at hetrue
        cases b
        · rw [hw2] at hev; exact absurd hev (by simp)
        · simp at hetrue


/-- The `UnsatRun` entry obligation's conclusion shape: a level-0,
    conflict-clear, solved-by, run-invariant entry whose
    propagation reports either an entitled conflict or the failed
    level-0 leaf. -/
def UnsatEntryShape (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : Prop :=
  ∃ st' : State,
    st'.decisionLevel = 0 ∧
    st'.conflict = none ∧
    SolvedBy problem constraintHolds st' ∧
    DomainCoherent problem st' ∧
    st'.clauses = problem.clauses ∧
    (∀ c ∈ st'.learned, c.EntailedBy problem constraintHolds) ∧
    ((propagateLoop (engineFuel st') props st').conflict.isSome = true ∧
      SolvedBy problem constraintHolds
        (propagateLoop (engineFuel st') props st') ∨
    (propagateLoop (engineFuel st') props st').conflict = none ∧
      allSingleton (propagateLoop (engineFuel st') props st') = true ∧
      ∃ a, singletonAssignment
          (propagateLoop (engineFuel st') props st') = some a ∧
        ¬ (fitsB problem a &&
            problem.constraints.all (fun c => constraintHoldsB c a)))
/-- The sweep's unconditional SolvedBy: whether or not it reports a
    conflict, the swept state still represents every internal
    solution (the enqueues are justified; the conflict verdict does
    not change the trail). -/
theorem sweep_solvedBy_any
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (st : State)
    (hsol : SolvedBy problem constraintHolds st)
    (hcoh : DomainCoherent problem st)
    (c : Clause) :
    SolvedBy problem constraintHolds
      { st with conflict := some c } := by
  intro a ha
  have hrep := hsol a ha
  exact hrep

/-- The sweep's unconditional `SolvedBy`: whether or not a conflict
    is reported, the swept state represents every internal solution —
    the sweep's enqueues are justified (`PropSafe`'s impliedTrueAt at
    represented solutions), and the conflict verdict does not change
    the trail. -/
theorem runPropagators_solvedBy_all
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (st : State)
    (hnone : st.conflict = none)
    (hsol : SolvedBy problem constraintHolds st)
    (hcoh : DomainCoherent problem st) :
    SolvedBy problem constraintHolds (runPropagators props st) := by
  -- the internal sweep induction: each enqueue's literal is true at
  -- every represented solution (PropSafe), so SolvedBy threads
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      acc.conflict = none →
      SolvedBy problem constraintHolds acc →
      DomainCoherent problem acc →
      SolvedBy problem constraintHolds (runPropagators.go ps acc) := by
    intro ps
    induction ps with
    | nil =>
        intro acc _ _ hsol2 _
        have hgo : runPropagators.go [] acc = acc := rfl
        rw [hgo]
        exact hsol2
    | cons p rest ih =>
        intro acc hmem hnone2 hsol2 hcoh2
        have hp : p ∈ props := hmem p (List.mem_cons_self)
        have hrest : ∀ q ∈ rest, q ∈ props := fun q hq =>
          hmem q (List.mem_cons_of_mem _ hq)
        have hpsafe := hsafe acc hcoh2
        simp only [runPropagators.go]
        split
        · -- already conflicting: the accumulator is returned
          show SolvedBy problem constraintHolds acc
          exact hsol2
        · rename_i hclear2
          match hrun : p.run acc with
          | PropagationResult.stable =>
              show SolvedBy problem constraintHolds
                (runPropagators.go rest acc)
              exact ih acc hrest hnone2 hsol2 hcoh2
          | PropagationResult.conflict c =>
              -- the verdict does not change the accumulator
              show SolvedBy problem constraintHolds acc
              exact hsol2
          | PropagationResult.implied l r =>
              -- the implied literal is true at every represented
              -- solution; enqueueNorm_solvedBy threads
              have hjustify : ∀ a, ProblemSolution problem
                  constraintHolds a → l.norm.eval a = some true := by
                intro a ha
                have hrep := hsol2 a ha
                rw [Literal.norm_eval l a]
                exact hpsafe.impliedTrueAt p hp l r hrun a
                  (And.intro ha hrep)
              obtain ⟨hconf3, hsol3⟩ := enqueueNorm_solvedBy
                (problem := problem) (constraintHolds := constraintHolds)
                (st := acc) (l0 := l) (reason := some r) hnone2 hsol2
                hjustify
              rcases hconf3 with hconf3 | hnosol
              · exact ih (enqueueNorm acc l (some r)) hrest hconf3 hsol3
                  (enqueueNorm_coherent hcoh2)
              · -- no internal solution exists: SolvedBy is vacuous
                intro a ha
                exact absurd ⟨a, ha⟩ hnosol
  exact main props st (fun q hq => hq) hnone hsol hcoh
/-- `propagateLoop_solvedBy` without the conflict-clear premise on
    the RESULT: a conflict-carrying answer still represents every
    solution — the loop's enqueues are all justified (scan units by
    entitlement + trail falsification, propagator implications by
    the safety premise), and the conflict verdict itself does not
    change the trail. -/
theorem propagateLoop_solvedBy_any
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (orig lnd : List Clause)
    (hdb : ∀ c ∈ orig,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hlearned : ∀ c ∈ lnd,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      SolvedBy problem constraintHolds st →
      DomainCoherent problem st →
      st.clauses = orig →
      st.learned = lnd →
      SolvedBy problem constraintHolds (propagateLoop fuel props st) := by
  intro fuel
  induction fuel with
  | zero => intro st _ hsol _ _ _; exact hsol
  | succ fuel ih =>
      intro st hc hsol hcoh hclfix hlnfix
      -- SolvedBy ignores the conflict slot: a helper transferring
      -- through the record update
      have solvedBy_conflictUpdate :
          ∀ (s : State) (cc : Option Clause),
            SolvedBy problem constraintHolds s →
            SolvedBy problem constraintHolds
              { s with conflict := cc } := by
        intro s cc hsol2 a ha
        exact hsol2 a ha
      cases hscan : scanAll st with
      | none =>
          have hUnf : propagateLoop (fuel + 1) props st =
              (if ((runPropagators props st).trail.length == st.trail.length)
                = true then runPropagators props st
              else propagateLoop fuel props (runPropagators props st)) := by
            simp [propagateLoop, hc, hscan, Option.isSome_none]
          rw [hUnf]
          by_cases hlen : ((runPropagators props st).trail.length ==
              st.trail.length) = true
          · -- quiesced: the swept state is the loop's answer; the
            -- sweep's SolvedBy (clear or conflict-carrying — both
            -- arms represent every solution)
            rw [if_pos hlen]
            rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
              ⟨_, hsol2⟩ | ⟨c, _, _⟩
            · exact hsol2
            · -- the conflict-carrying swept state: SolvedBy still
              -- holds — the sweep's enqueues are all justified, so
              -- every solution stays represented
              exact runPropagators_solvedBy_all hsafe hsolvable st
                hc hsol hcoh
          · -- extended: the recursion from the swept state
            rw [if_neg hlen]
            by_cases hconf2 : (runPropagators props st).conflict = none
            · rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
                ⟨_, hsol2⟩ | ⟨c, hcc, _⟩
              · exact ih (runPropagators props st) hconf2 hsol2
                  (runPropagators_coherent props st hcoh)
                  (by
                    have hcl2 : (runPropagators props st).clauses
                        = st.clauses := by
                      unfold runPropagators
                      exact runPropagators_go_clauses props st
                    rw [hcl2]; exact hclfix)
                  (by
                    have hln2 : (runPropagators props st).learned
                        = st.learned := by
                      unfold runPropagators
                      exact runPropagators_go_learned props st
                    rw [hln2]; exact hlnfix)
              · rw [hcc] at hconf2; exact absurd hconf2 (by simp)
            · -- the conflict-carrying swept state is the loop's
              -- answer: SolvedBy is the swept state's own
              have hret : propagateLoop fuel props
                  (runPropagators props st)
                  = runPropagators props st := by
                cases hfuel : fuel with
                | zero => rfl
                | succ k =>
                    simp only [propagateLoop]
                    have hissome : (runPropagators props
                        st).conflict.isSome = true := by
                      cases hc3 : (runPropagators props st).conflict with
                      | none => exact absurd hc3 hconf2
                      | some c =>
                          rw [Option.isSome_iff_exists]
                          exact ⟨c, rfl⟩
                    rw [if_pos hissome]
              rw [hret]
              rcases sweep_solvedBy hsafe hsolvable st hsol hcoh hc with
                ⟨_, hsol2⟩ | ⟨c, _, _⟩
              · exact hsol2
              · exact runPropagators_solvedBy_all hsafe hsolvable st
                  hc hsol hcoh
      | some verdict =>
          cases verdict with
          | inl c =>
              -- scan conflict: the returned state is st with the
              -- conflict slot set — SolvedBy transfers (unmodified
              -- trail/domains/databases)
              have hUnf2 : propagateLoop (fuel + 1) props st
                  = { st with conflict := some c } := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf2]
              exact solvedBy_conflictUpdate st (some c) hsol
          | inr w =>
              obtain ⟨l, r⟩ := w
              have hUnf : propagateLoop (fuel + 1) props st
                  = propagateLoop fuel props (enqueueNorm st l (some r)) := by
                simp [propagateLoop, hc, hscan, Option.isSome_none]
              rw [hUnf]
              obtain ⟨c2, hcm, hcs⟩ := scanAll_inr_inv hscan
              have hent : (∀ a, ProblemSolution problem constraintHolds a →
                  ∃ l2 ∈ c2, l2.eval a = some true) := by
                rcases List.mem_append.mp hcm with hcl | hln
                · exact hdb c2 (hclfix ▸ hcl)
                · exact hlearned c2 (hlnfix ▸ hln)
              have hjustify : ∀ a, ProblemSolution problem constraintHolds a →
                  l.norm.eval a = some true :=
                scanUnit_justified_all hcs hent hsol
              obtain ⟨hconf2, hsol2⟩ := enqueueNorm_justified_solvable
                (problem := problem) (constraintHolds := constraintHolds)
                (st := st) (l0 := l) (reason := some r) hc hsolvable hsol
                hjustify
              have hcl2 : (enqueueNorm st l (some r)).clauses = st.clauses :=
                enqueueNorm_clauses
              have hln2 : (enqueueNorm st l (some r)).learned = st.learned :=
                enqueueNorm_learned
              exact ih (enqueueNorm st l (some r)) hconf2 hsol2
                (enqueueNorm_coherent hcoh)
                (by rw [hcl2]; exact hclfix)
                (by rw [hln2]; exact hlnfix)

/-- The sweep's level-0 filter identity at POSITIVE levels: fresh
    enqueues are stamped at the current (positive) decision level, so
    the 0-filter drops them and the level-0 subtrail is the entry's
    own. -/
theorem runPropagators_filter0_pos {props : List Propagator} (s : State)
    (hpos : 0 < s.decisionLevel)
    (hrooted : ∀ e ∈ s.trail, e.level ≤ s.decisionLevel) :
    (runPropagators props s).trail.filter
        (fun e => decide (e.level ≤ 0))
      = s.trail.filter (fun e => decide (e.level ≤ 0)) := by
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      0 < acc.decisionLevel →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      (runPropagators.go ps acc).trail.filter
          (fun e => decide (e.level ≤ 0))
        = acc.trail.filter (fun e => decide (e.level ≤ 0)) := by
    intro ps
    induction ps with
    | nil => intro acc _ _ _; rfl
    | cons p rest ih =>
        intro acc hmem hpos2 hroot2
        simp only [runPropagators.go]
        split
        · rfl
        · rename_i hclear
          match hrun : p.run acc with
          | PropagationResult.stable =>
              exact ih acc (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
                hpos2 hroot2
          | PropagationResult.conflict c => rfl
          | PropagationResult.implied l r =>
              have hfil : (enqueueNorm acc l (some r)).trail.filter
                  (fun e => decide (e.level ≤ 0))
                  = acc.trail.filter
                      (fun e => decide (e.level ≤ 0)) := by
                rcases enqueueNorm_trail_cases (st := acc) (l := l)
                  (reason := some r) with htr | htr
                · rw [htr]
                · rw [htr, List.filter_append, List.filter_cons,
                    List.filter_nil]
                  rw [if_neg (by
                    intro hcon
                    have hh : acc.decisionLevel ≤ 0 :=
                      of_decide_eq_true hcon
                    omega)]
                  rw [List.append_nil]
              have hdl3 : (enqueueNorm acc l (some r)).decisionLevel
                  = acc.decisionLevel := by
                simp only [enqueueNorm]
                split
                · rfl
                · split
                  · rfl
                  · rfl
              exact (ih (enqueueNorm acc l (some r))
                (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
                (by rw [hdl3]; exact hpos2)
                (enqueueNorm_rooted hroot2)).trans hfil
  exact main props s (fun q hq => hq) hpos hrooted

/-- The propagation loop's level-0 filter identity at POSITIVE
    levels: every fresh enqueue (scan unit or propagator implication)
    is at the current (positive) level, so the level-0 subtrail is the
    entry's own. -/
theorem propagateLoop_filter0_pos {props : List Propagator} :
    ∀ (fuel : Nat) (s : State),
      0 < s.decisionLevel →
      (∀ e ∈ s.trail, e.level ≤ s.decisionLevel) →
      (propagateLoop fuel props s).trail.filter
          (fun e => decide (e.level ≤ 0))
        = s.trail.filter (fun e => decide (e.level ≤ 0)) := by
  intro fuel
  induction fuel with
  | zero => intro s _ _; rfl
  | succ fuel ih =>
      intro s hpos hrooted
      simp only [propagateLoop]
      split
      · rfl
      · rename_i hclear
        cases hscan : scanAll s with
        | none =>
            show List.filter (fun e => decide (e.level ≤ 0))
              (if ((runPropagators props s).trail.length ==
                  s.trail.length) = true then runPropagators props s
              else propagateLoop fuel props (runPropagators props
                s)).trail = _
            by_cases hlen : ((runPropagators props s).trail.length ==
                s.trail.length) = true
            · rw [if_pos hlen]
              exact runPropagators_filter0_pos s hpos hrooted
            · rw [if_neg hlen]
              rw [← runPropagators_filter0_pos s hpos hrooted]
              have hdl : (runPropagators props s).decisionLevel
                  = s.decisionLevel :=
                runPropagators_decisionLevel props s
              exact ih (runPropagators props s) (by rw [hdl]; exact hpos)
                (runPropagators_rooted props s hrooted)
        | some verdict =>
            match verdict with
            | Sum.inl c => rfl
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                show List.filter (fun e => decide (e.level ≤ 0))
                  (propagateLoop fuel props (enqueueNorm s l
                    (some r))).trail = _
                have hfil : (enqueueNorm s l (some r)).trail.filter
                    (fun e => decide (e.level ≤ 0))
                    = s.trail.filter (fun e => decide (e.level ≤ 0)) := by
                  rcases enqueueNorm_trail_cases (st := s) (l := l)
                    (reason := some r) with htr | htr
                  · rw [htr]
                  · rw [htr, List.filter_append, List.filter_cons,
                      List.filter_nil]
                    rw [if_neg (by
                      intro hcon
                      have hh : s.decisionLevel ≤ 0 :=
                        of_decide_eq_true hcon
                      omega)]
                    rw [List.append_nil]
                have hdl2 : (enqueueNorm s l (some r)).decisionLevel
                    = s.decisionLevel := by
                  simp only [enqueueNorm]
                  split
                  · rfl
                  · split
                    · rfl
                    · rfl
                exact (ih (enqueueNorm s l (some r))
                  (by rw [hdl2]; exact hpos)
                  (enqueueNorm_rooted hrooted)).trans hfil

/-- The propagation loop never modifies the original clause
    database. -/
theorem propagateLoop_clauses {props : List Propagator} :
    ∀ (fuel : Nat) (s : State),
      (propagateLoop fuel props s).clauses = s.clauses := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
      intro s
      simp only [propagateLoop]
      split
      · rfl
      · rename_i hclear
        cases hscan : scanAll s with
        | none =>
            by_cases hlen : ((runPropagators props s).trail.length ==
                s.trail.length) = true
            · rw [if_pos hlen]
              show (runPropagators.go props s).clauses = s.clauses
              exact runPropagators_go_clauses props s
            · rw [if_neg hlen]
              show (propagateLoop fuel props (runPropagators props
                s)).clauses = s.clauses
              rw [ih (runPropagators props s)]
              show (runPropagators.go props s).clauses = s.clauses
              exact runPropagators_go_clauses props s
        | some verdict =>
            match verdict with
            | Sum.inl c => rfl
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                show (propagateLoop fuel props (enqueueNorm s l
                  (some r))).clauses = s.clauses
                rw [ih (enqueueNorm s l (some r))]
                show (enqueueNorm s l (some r)).clauses = s.clauses
                simp only [enqueueNorm]
                split
                · rfl
                · split
                  · rfl
                  · rfl

/-- The propagation loop never modifies the learned database. -/
theorem propagateLoop_learned {props : List Propagator} :
    ∀ (fuel : Nat) (s : State),
      (propagateLoop fuel props s).learned = s.learned := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
      intro s
      simp only [propagateLoop]
      split
      · rfl
      · rename_i hclear
        cases hscan : scanAll s with
        | none =>
            by_cases hlen : ((runPropagators props s).trail.length ==
                s.trail.length) = true
            · rw [if_pos hlen]
              show (runPropagators.go props s).learned = s.learned
              exact runPropagators_go_learned props s
            · rw [if_neg hlen]
              show (propagateLoop fuel props (runPropagators props
                s)).learned = s.learned
              rw [ih (runPropagators props s)]
              show (runPropagators.go props s).learned = s.learned
              exact runPropagators_go_learned props s
        | some verdict =>
            match verdict with
            | Sum.inl c => rfl
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                show (propagateLoop fuel props (enqueueNorm s l
                  (some r))).learned = s.learned
                rw [ih (enqueueNorm s l (some r))]
                show (enqueueNorm s l (some r)).learned = s.learned
                simp only [enqueueNorm]
                split
                · rfl
                · split
                  · rfl
                  · rfl

/-- The wake-up queue is never modified (reserved for the two-watched
    literal schedule). -/
theorem sweep_queue {props : List Propagator} (s : State) :
    (runPropagators props s).queue = s.queue := by
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      (runPropagators.go ps acc).queue = acc.queue := by
    intro ps
    induction ps with
    | nil => intro acc _; rfl
    | cons p rest ih =>
        intro acc hmem
        simp only [runPropagators.go]
        split
        · rfl
        · rename_i hclear
          match hrun : p.run acc with
          | PropagationResult.stable =>
              exact ih acc (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
          | PropagationResult.conflict c => rfl
          | PropagationResult.implied l r =>
              show (runPropagators.go rest
                (enqueueNorm acc l (some r))).queue = acc.queue
              rw [ih (enqueueNorm acc l (some r))
                (fun q hq => hmem q (List.mem_cons_of_mem _ hq))]
              show (enqueueNorm acc l (some r)).queue = acc.queue
              simp only [enqueueNorm]
              split
              · rfl
              · split
                · rfl
                · rfl
  exact main props s (fun q hq => hq)

/-- The propagation loop never modifies the wake-up queue. -/
theorem propagateLoop_queue {props : List Propagator} :
    ∀ (fuel : Nat) (s : State),
      (propagateLoop fuel props s).queue = s.queue := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
      intro s
      simp only [propagateLoop]
      split
      · rfl
      · rename_i hclear
        cases hscan : scanAll s with
        | none =>
            by_cases hlen : ((runPropagators props s).trail.length ==
                s.trail.length) = true
            · rw [if_pos hlen]
              exact sweep_queue s
            · rw [if_neg hlen]
              show (propagateLoop fuel props (runPropagators props
                s)).queue = s.queue
              rw [ih (runPropagators props s)]
              exact sweep_queue s
        | some verdict =>
            match verdict with
            | Sum.inl c =>
                show ({ s with conflict := some c }).queue = s.queue
                rfl
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                show (propagateLoop fuel props (enqueueNorm s l
                  (some r))).queue = s.queue
                rw [ih (enqueueNorm s l (some r))]
                show (enqueueNorm s l (some r)).queue = s.queue
                simp only [enqueueNorm]
                split
                · rfl
                · split
                  · rfl
                  · rfl

/-- The analysis output's head inversion: the learned clause's
    head IS the asserting literal (up to normalization), from
    `analyzeConflict`'s construction. -/
theorem analyzeHead_mem {state : State} {an : ConflictAnalysis}
    (heq : analyzeConflict state = some an) :
    an.asserting.norm ∈ an.learned.map (fun l => l.norm) := by
  unfold analyzeConflict at heq
  cases hconf : state.conflict with
  | none => rw [hconf] at heq; exact absurd heq (by simp)
  | some conflictClause =>
      rw [hconf] at heq
      cases hres : analyzeTrail state.trail
          state.decisionLevel conflictClause with
      | none => simp only [hres] at heq; exact absurd heq (by simp)
      | some res =>
          obtain ⟨below, uip⟩ := res
          simp only [hres] at heq
          have hhead : an.asserting = uip.negate ∧
              an.learned = uip.negate ::
                below.map (fun p => p.1) := by
            injection heq with h1
            cases h1
            constructor <;> rfl
          rw [hhead.1, hhead.2]
          exact List.mem_cons_self

/-! ## Decision-arm support: the bisection's opposing exclusion and
    the decided state's transfers (agent A2, integrated 2026-09-30;
    re-verified in this module's own declarations) -/

/-! ## Helper 1: the extrema folds attain their values -/

/-- The `domMaxI` fold's result is a member of the scanned list (the
    fold of `maxI` over a list starting from `none` is one of the
    elements). -/
theorem a2_foldmax_mem : ∀ (ls : List Int) (acc : Option Int) (m : Int),
    (ls.foldl (fun a x => match a with
      | none => some x
      | some c => some (maxI c x)) acc) = some m →
    m ∈ ls ∨ acc = some m := by
  intro ls
  induction ls with
  | nil =>
      intro acc m h
      cases acc with
      | none => rw [List.foldl_nil] at h; exact absurd h (by simp)
      | some c =>
          rw [List.foldl_nil] at h
          exact Or.inr (by rw [h])
  | cons x rest ih =>
      intro acc m h
      rw [List.foldl_cons] at h
      cases acc with
      | none =>
          obtain hm | hacc := ih (some x) m h
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inl (by
              rw [Option.some.injEq] at hacc
              rw [← hacc]; exact List.mem_cons_self)
      | some c =>
          obtain hm | hacc := ih (some (maxI c x)) m h
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · rw [Option.some.injEq] at hacc
            have hmax : maxI c x = c ∨ maxI c x = x := by
              unfold maxI
              by_cases hc : c ≤ x <;> simp [hc]
            rcases hmax with hm2 | hm2
            · rw [hm2] at hacc
              exact Or.inr (by rw [hacc])
            · rw [hm2] at hacc
              exact Or.inl (by rw [hacc]; exact List.mem_cons_self)

/-- `domMaxI d = some mx` is attained: some value of `d` has integer
    view `mx`. -/
theorem a2_domMaxI_attained {d : List Value} {mx : Int}
    (h : domMaxI d = some mx) :
    ∃ v ∈ d, Value.intView v = some mx := by
  unfold domMaxI at h
  obtain hm | hnone := a2_foldmax_mem (domInts d) none mx h
  · have hmem : mx ∈ d.filterMap Value.intView := hm
    obtain ⟨v, hvm, hvv⟩ := List.mem_filterMap.mp hmem
    exact ⟨v, hvm, hvv⟩
  · exact absurd hnone (by simp)

/-- The `domMinI` fold's result is a member of the scanned list. -/
theorem a2_foldmin_mem : ∀ (ls : List Int) (acc : Option Int) (m : Int),
    (ls.foldl (fun a x => match a with
      | none => some x
      | some c => some (minI c x)) acc) = some m →
    m ∈ ls ∨ acc = some m := by
  intro ls
  induction ls with
  | nil =>
      intro acc m h
      cases acc with
      | none => rw [List.foldl_nil] at h; exact absurd h (by simp)
      | some c =>
          rw [List.foldl_nil] at h
          exact Or.inr (by rw [h])
  | cons x rest ih =>
      intro acc m h
      rw [List.foldl_cons] at h
      cases acc with
      | none =>
          obtain hm | hacc := ih (some x) m h
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inl (by
              rw [Option.some.injEq] at hacc
              rw [← hacc]; exact List.mem_cons_self)
      | some c =>
          obtain hm | hacc := ih (some (minI c x)) m h
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · rw [Option.some.injEq] at hacc
            have hmin : minI c x = c ∨ minI c x = x := by
              unfold minI
              by_cases hc : c ≤ x <;> simp [hc]
            rcases hmin with hm2 | hm2
            · rw [hm2] at hacc
              exact Or.inr (by rw [hacc])
            · rw [hm2] at hacc
              exact Or.inl (by rw [hacc]; exact List.mem_cons_self)

/-- `domMinI d = some mn` is attained dually. -/
theorem a2_domMinI_attained {d : List Value} {mn : Int}
    (h : domMinI d = some mn) :
    ∃ v ∈ d, Value.intView v = some mn := by
  unfold domMinI at h
  obtain hm | hnone := a2_foldmin_mem (domInts d) none mn h
  · have hmem : mn ∈ d.filterMap Value.intView := hm
    obtain ⟨v, hvm, hvv⟩ := List.mem_filterMap.mp hmem
    exact ⟨v, hvm, hvv⟩
  · exact absurd hnone (by simp)

/-! ## Helper 2: the posLe fold bound (the Q invariant) -/

/-- The Q invariant: a slot domain is at most singleton (Boolean pin)
    or all its integer views are bounded by `k`. -/
def A2Q (k : Int) (d : List Value) : Prop :=
  d.length ≤ 1 ∨ (∀ v ∈ d, ∀ i, Value.intView v = some i → i ≤ k)

/-- Past-the-end update: reading the updated slot at an index past the
    domain list's length gives the default (empty). -/
theorem a2_updateSlot_getD_nil (doms : List (List Value)) (s : Nat)
    (f : List Value → List Value) (hge : doms.length ≤ s) :
    (updateSlot doms s f).getD s [] = [] := by
  have hlen : (updateSlot doms s f).length = doms.length :=
    updateSlot_length doms s f
  exact getD_nil_of_ge (updateSlot doms s f) s (by rw [hlen]; exact hge)

/-- Each `domOfLit` step preserves Q on any slot: the intLe arms
    filter (a subset of the old slot, and length-bounded), the boolEq
    arm pins to a singleton, and other slots are untouched. -/
theorem a2_Q_step : ∀ (doms : List (List Value)) (l : Literal)
    (s : Nat) (k : Int),
    A2Q k (doms.getD s []) →
    A2Q k ((domOfLit doms l).getD s []) := by
  intro doms l s k h
  match hl : l with
  | ⟨.intLe s' k', positive⟩ =>
      cases hpos : positive with
      | true =>
          have hd : domOfLit doms ⟨.intLe s' k', true⟩ =
              updateSlot doms s' (fun d =>
                domFilterInt (fun p => decide (p ≤ k')) d) := rfl
          rw [hd]
          by_cases hslot : s' = s
          · subst hslot
            by_cases hin : s' < doms.length
            · rw [updateSlot_getD_eq doms s' _ hin]
              rcases h with h1 | h2
              · refine Or.inl ?_
                rw [domFilterInt]
                calc (List.filter (fun v =>
                    match v with
                    | Value.int i => decide (i ≤ k')
                    | Value.bool b => decide ((if b = true then 1 else 0) ≤ k')
                    | x => true) (doms.getD s' [])).length
                    ≤ (doms.getD s' []).length :=
                      List.length_filter_le _ _
                  _ ≤ 1 := h1
              · refine Or.inr ?_
                intro v hv i hvi
                have hmem : v ∈ domFilterInt (fun p => decide (p ≤ k'))
                    (doms.getD s' []) := hv
                rw [domFilterInt, List.mem_filter] at hmem
                exact h2 v hmem.1 i hvi
            · rw [a2_updateSlot_getD_nil doms s' _
                (Nat.le_of_not_gt (fun hlt => hin hlt))]
              exact Or.inl (by simp)
          · rw [updateSlot_getD_ne doms s' _ s (fun hcon => hslot hcon.symm)]
            exact h
      | false =>
          have hd : domOfLit doms ⟨.intLe s' k', false⟩ =
              updateSlot doms s' (fun d =>
                domFilterInt (fun p => decide (p > k')) d) := rfl
          rw [hd]
          by_cases hslot : s' = s
          · subst hslot
            by_cases hin : s' < doms.length
            · rw [updateSlot_getD_eq doms s' _ hin]
              rcases h with h1 | h2
              · refine Or.inl ?_
                rw [domFilterInt]
                calc (List.filter (fun v =>
                    match v with
                    | Value.int i => decide (i > k')
                    | Value.bool b => decide ((if b = true then 1 else 0) > k')
                    | x => true) (doms.getD s' [])).length
                    ≤ (doms.getD s' []).length :=
                      List.length_filter_le _ _
                  _ ≤ 1 := h1
              · refine Or.inr ?_
                intro v hv i hvi
                have hmem : v ∈ domFilterInt (fun p => decide (p > k'))
                    (doms.getD s' []) := hv
                rw [domFilterInt, List.mem_filter] at hmem
                exact h2 v hmem.1 i hvi
            · rw [a2_updateSlot_getD_nil doms s' _
                (Nat.le_of_not_gt (fun hlt => hin hlt))]
              exact Or.inl (by simp)
          · rw [updateSlot_getD_ne doms s' _ s (fun hcon => hslot hcon.symm)]
            exact h
  | ⟨.boolEq s' b, positive⟩ =>
      have hd : domOfLit doms ⟨.boolEq s' b, positive⟩ =
          updateSlot doms s' (fun d => d.filter
            (fun v => v.eqB (.bool (if positive then b else !b)))) := rfl
      by_cases hslot : s' = s
      · subst hslot
        rw [hd]
        by_cases hin : s' < doms.length
        · rw [updateSlot_getD_eq doms s' _ hin]
          rcases h with h1 | h2
          · exact Or.inl (Nat.le_trans (List.length_filter_le _ _) h1)
          · refine Or.inr ?_
            intro v hv i hvi
            exact h2 v (List.mem_filter.mp hv).1 i hvi
        · rw [a2_updateSlot_getD_nil doms s' _
            (Nat.le_of_not_gt (fun hlt => hin hlt))]
          exact Or.inl (by simp)
      · rw [hd, updateSlot_getD_ne doms s' _ s (fun hcon => hslot hcon.symm)]
        exact h
  | ⟨.intNe s' k', positive⟩ =>
      cases hpos : positive with
      | true =>
          have hd : domOfLit doms ⟨.intNe s' k', true⟩ =
              updateSlot doms s' (fun d =>
                domFilterInt (fun p => decide (p ≠ k')) d) := rfl
          rw [hd]
          by_cases hslot : s' = s
          · subst hslot
            by_cases hin : s' < doms.length
            · rw [updateSlot_getD_eq doms s' _ hin]
              rcases h with h1 | h2
              · refine Or.inl ?_
                rw [domFilterInt]
                calc (List.filter (fun v =>
                    match v with
                    | Value.int i => decide (i ≠ k')
                    | Value.bool b => decide ((if b = true then 1 else 0) ≠ k')
                    | x => true) (doms.getD s' [])).length
                    ≤ (doms.getD s' []).length :=
                      List.length_filter_le _ _
                  _ ≤ 1 := h1
              · refine Or.inr ?_
                intro v hv i hvi
                have hmem : v ∈ domFilterInt (fun p => decide (p ≠ k'))
                    (doms.getD s' []) := hv
                rw [domFilterInt, List.mem_filter] at hmem
                exact h2 v hmem.1 i hvi
            · rw [a2_updateSlot_getD_nil doms s' _
                (Nat.le_of_not_gt (fun hlt => hin hlt))]
              exact Or.inl (by simp)
          · rw [updateSlot_getD_ne doms s' _ s (fun hcon => hslot hcon.symm)]
            exact h
      | false =>
          have hd : domOfLit doms ⟨.intNe s' k', false⟩ =
              updateSlot doms s' (fun d =>
                domFilterInt (fun p => decide (p = k')) d) := rfl
          rw [hd]
          by_cases hslot : s' = s
          · subst hslot
            by_cases hin : s' < doms.length
            · rw [updateSlot_getD_eq doms s' _ hin]
              rcases h with h1 | h2
              · refine Or.inl ?_
                rw [domFilterInt]
                calc (List.filter (fun v =>
                    match v with
                    | Value.int i => decide (i = k')
                    | Value.bool b => decide ((if b = true then 1 else 0) = k')
                    | x => true) (doms.getD s' [])).length
                    ≤ (doms.getD s' []).length :=
                      List.length_filter_le _ _
                  _ ≤ 1 := h1
              · refine Or.inr ?_
                intro v hv i hvi
                have hmem : v ∈ domFilterInt (fun p => decide (p = k'))
                    (doms.getD s' []) := hv
                rw [domFilterInt, List.mem_filter] at hmem
                exact h2 v hmem.1 i hvi
            · rw [a2_updateSlot_getD_nil doms s' _
                (Nat.le_of_not_gt (fun hlt => hin hlt))]
              exact Or.inl (by simp)
          · rw [updateSlot_getD_ne doms s' _ s (fun hcon => hslot hcon.symm)]
            exact h

/-- Q is preserved across a whole fold (iterated `a2_Q_step`). -/
theorem a2_Q_fold : ∀ (tr : List TrailEntry) (doms : List (List Value))
    (s : Nat) (k : Int),
    A2Q k (doms.getD s []) →
    A2Q k ((tr.foldl (fun acc e => domOfLit acc e.literal) doms).getD s []) := by
  intro tr
  induction tr with
  | nil => intro doms s k h; exact h
  | cons e rest ih =>
      intro doms s k h
      rw [List.foldl_cons]
      exact ih (domOfLit doms e.literal) s k (a2_Q_step doms e.literal s k h)

/-- The Q-establishing step: filtering the slot at `posLe s k` makes
    every integer view of the slot bounded by `k`. -/
theorem a2_Q_posLe (doms : List (List Value)) (s : Nat) (k : Int) :
    A2Q k ((domOfLit doms (posLe s k)).getD s []) := by
  have hd : domOfLit doms (posLe s k) =
      updateSlot doms s (fun d =>
        domFilterInt (fun p => decide (p ≤ k)) d) := rfl
  rw [hd]
  by_cases hin : s < doms.length
  · rw [updateSlot_getD_eq doms s _ hin]
    refine Or.inr ?_
    intro v hv i hvi
    have hmem : v ∈ domFilterInt (fun p => decide (p ≤ k))
        (doms.getD s []) := hv
    rw [domFilterInt, List.mem_filter] at hmem
    cases v with
    | int p =>
        rw [show Value.intView (Value.int p) = some p from rfl] at hvi
        rw [Option.some.injEq] at hvi
        subst hvi
        exact of_decide_eq_true hmem.2
    | bool b =>
        rw [show Value.intView (Value.bool b) =
          some (if b then 1 else 0) from rfl] at hvi
        rw [Option.some.injEq] at hvi
        subst hvi
        exact of_decide_eq_true hmem.2
    | setOfInt x => exact absurd hvi (by simp [Value.intView])
    | array x => exact absurd hvi (by simp [Value.intView])
  · rw [a2_updateSlot_getD_nil doms s _
      (Nat.le_of_not_gt (fun hlt => hin hlt))]
    exact Or.inl (by simp)

/-- LEMMA A: if some trail entry is exactly `posLe s k`, then the
    folded slot is Q at `k` — at most singleton, or every integer view
    bounded by `k`. -/
theorem a2_fold_posLe_Q : ∀ (tr : List TrailEntry)
    (doms : List (List Value)) (s : Nat) (k : Int),
    (∃ e ∈ tr, e.literal = posLe s k) →
    A2Q k ((tr.foldl (fun acc e => domOfLit acc e.literal) doms).getD s []) := by
  intro tr
  induction tr with
  | nil => intro doms s k hmem; exact absurd hmem (by simp)
  | cons e rest ih =>
      intro doms s k hmem
      obtain ⟨e2, he2mem, he2lit⟩ := hmem
      rcases List.mem_cons.mp he2mem with hhead | hrest
      · -- the head IS the posLe entry: fold at it, then preserve
        rw [List.foldl_cons]
        refine a2_Q_fold rest (domOfLit doms e.literal) s k ?_
        have hlite : e.literal = posLe s k := by
          rw [← hhead]; exact he2lit
        rw [hlite]
        exact a2_Q_posLe doms s k
      · -- the entry is deeper: recurse with the head's step applied
        rw [List.foldl_cons]
        exact ih (domOfLit doms e.literal) s k
          ⟨e2, hrest, he2lit⟩

/-! ## Helper 3: the decideLiteral inversion -/

/-- `decideLiteral st = some hl` pins the literal's shape: a bisection
    `¬(s ≤ (mn+mx)/2)` at a slot whose current domain has distinct
    integer extrema `mn < mx`. -/
theorem a2_decideLiteral_spec : ∀ (st : State) (hl : Literal),
    decideLiteral st = some hl →
    ∃ s mn mx,
      domMinI (st.domains.getD s []) = some mn ∧
      domMaxI (st.domains.getD s []) = some mx ∧
      mn < mx ∧ hl = negLe s ((mn + mx) / 2) := by
  intro st hl hq
  unfold decideLiteral at hq
  have main : ∀ (s : Nat) (doms : List (List Value)) (l : Literal),
      decideLiteral.go s doms = some l →
      ∃ s2 mn mx,
        domMinI (doms.getD s2 []) = some mn ∧
        domMaxI (doms.getD s2 []) = some mx ∧
        mn < mx ∧ l = negLe (s + s2) ((mn + mx) / 2) := by
    intro s doms
    induction doms generalizing s with
    | nil => intro l h; exact absurd h (by simp [decideLiteral.go])
    | cons d rest ih =>
        intro l h
        simp only [decideLiteral.go] at h
        cases hmn : domMinI d with
        | none =>
            rw [hmn] at h; simp only [] at h
            obtain ⟨s2, mn, mx, hm2, hx2, hlt, hl2⟩ :=
              ih (s + 1) l h
            refine ⟨s2 + 1, mn, mx, ?_, ?_, hlt, ?_⟩
            · show domMinI ((d :: rest).getD (s2 + 1) []) = some mn
              rw [List.getD_cons_succ]; exact hm2
            · show domMaxI ((d :: rest).getD (s2 + 1) []) = some mx
              rw [List.getD_cons_succ]; exact hx2
            · show l = negLe (s + (s2 + 1)) ((mn + mx) / 2)
              rw [show s + (s2 + 1) = (s + 1) + s2 from by omega]
              exact hl2
        | some mn =>
            cases hmx : domMaxI d with
            | none =>
                rw [hmn, hmx] at h; simp only [] at h
                obtain ⟨s2, mn, mx, hm2, hx2, hlt, hl2⟩ :=
                  ih (s + 1) l h
                refine ⟨s2 + 1, mn, mx, ?_, ?_, hlt, ?_⟩
                · show domMinI ((d :: rest).getD (s2 + 1) []) = some mn
                  rw [List.getD_cons_succ]; exact hm2
                · show domMaxI ((d :: rest).getD (s2 + 1) []) = some mx
                  rw [List.getD_cons_succ]; exact hx2
                · show l = negLe (s + (s2 + 1)) ((mn + mx) / 2)
                  rw [show s + (s2 + 1) = (s + 1) + s2 from by omega]
                  exact hl2
            | some mx =>
                rw [hmn, hmx] at h
                simp only [] at h
                by_cases hlt : mn < mx
                · rw [if_pos hlt] at h
                  injection h with h2
                  refine ⟨0, mn, mx, hmn, hmx, hlt, ?_⟩
                  show l = negLe (s + 0) ((mn + mx) / 2)
                  rw [Nat.add_zero]; exact h2.symm
                · rw [if_neg hlt] at h
                  obtain ⟨s2, mn, mx, hm2, hx2, hlt, hl2⟩ :=
                    ih (s + 1) l h
                  refine ⟨s2 + 1, mn, mx, ?_, ?_, hlt, ?_⟩
                  · show domMinI ((d :: rest).getD (s2 + 1) []) = some mn
                    rw [List.getD_cons_succ]; exact hm2
                  · show domMaxI ((d :: rest).getD (s2 + 1) []) = some mx
                    rw [List.getD_cons_succ]; exact hx2
                  · show l = negLe (s + (s2 + 1)) ((mn + mx) / 2)
                    rw [show s + (s2 + 1) = (s + 1) + s2 from by omega]
                    exact hl2
  obtain ⟨s2, mn, mx, hm2, hx2, hlt, hl2⟩ := main 0 st.domains hl hq
  refine ⟨s2, mn, mx, hm2, hx2, hlt, ?_⟩
  simpa using hl2

/-! ## Helper 4: singleton slots have equal extrema -/

/-- A slot with at most one value cannot carry distinct integer
    extrema: both are `some` only when equal (or `none` when the
    integer view is empty). -/
theorem a2_singleton_extrema {d : List Value} {mn mx : Int}
    (hlen : d.length ≤ 1)
    (hmn : domMinI d = some mn) (hmx : domMaxI d = some mx) :
    mn = mx := by
  cases hd : d with
  | nil =>
      rw [hd] at hmn
      exact absurd hmn (by
        intro hc
        have hdi : domMinI [] = none := rfl
        rw [hdi] at hc
        exact absurd hc (by simp))
  | cons v rest =>
      cases hrest : rest with
      | nil =>
          rw [hd, hrest] at hmn hmx
          cases v with
          | int i =>
              rw [show domMinI [Value.int i] = some i from rfl] at hmn
              rw [show domMaxI [Value.int i] = some i from rfl] at hmx
              rw [Option.some.injEq] at hmn hmx
              omega
          | bool b =>
              rw [show domMinI [Value.bool b] =
                some (if b then 1 else 0) from rfl] at hmn
              rw [show domMaxI [Value.bool b] =
                some (if b then 1 else 0) from rfl] at hmx
              rw [Option.some.injEq] at hmn hmx
              cases b <;> simp_all
          | setOfInt x =>
              rw [show domMinI [Value.setOfInt x] = none from rfl] at hmn
              exact absurd hmn (by simp)
          | array x =>
              rw [show domMinI [Value.array x] = none from rfl] at hmn
              exact absurd hmn (by simp)
      | cons w rest2 =>
          exfalso
          have hge : d.length ≥ 2 := by
            rw [hd, hrest]
            simp
          omega

/-! ## Helper 5: the opposing-branch exclusion -/

/-- THE EXCLUSION: a bisection decision never hits the opposing-fact
    branch. The trail entry `posLe s ((mn+mx)/2)` (the canonical
    negation of the decision literal) would force the folded slot's
    integer views below `(mn+mx)/2`; the extrema read by the bisection
    come from the very same folded slot, so the max is below the
    midpoint — yet the bisection required `mn < mx`, which puts the
    midpoint strictly below the max. (The degenerate escape — the slot
    becoming a Boolean singleton — collapses the extrema instead.) -/
theorem a2_decide_not_opposing {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st1 : State} {hl : Literal}
    (hcoh : DomainCoherent problem st1)
    (hq : decideLiteral st1 = some hl) :
    st1.negOnTrail hl.norm = false := by
  obtain ⟨s, mn, mx, hmn, hmx, hlt, hlq2⟩ :=
    a2_decideLiteral_spec st1 hl hq
  cases hbool : st1.negOnTrail hl.norm with
  | false => rfl
  | true =>
      exfalso
      -- the decision literal's canonical negation IS on the trail
      have hneg : st1.negOnTrail hl.norm = true := hbool
      unfold State.negOnTrail at hneg
      rw [List.any_eq_true] at hneg
      obtain ⟨e, hem, heb⟩ := hneg
      have hlit : e.literal = (hl.norm).negate.norm := by
        simpa only [litEqB, decide_eq_true_eq] using heb
      -- hl is the negLe bisection: all normalization is the identity
      rw [hlq2] at hlit
      have hentry : e.literal = posLe s ((mn + mx) / 2) := by
        -- for the negLe bisection, norm is the identity
        have hnorm : (negLe s ((mn + mx) / 2)).norm
            = negLe s ((mn + mx) / 2) := rfl
        have h2 : (negLe s ((mn + mx) / 2)).negate.norm
            = posLe s ((mn + mx) / 2) := rfl
        rw [hnorm, h2] at hlit
        exact hlit
      -- the coherence fold: the current slot is the trail fold
      have hfold : A2Q ((mn + mx) / 2)
          ((st1.trail.foldl (fun acc e => domOfLit acc e.literal)
            problem.domains).getD s []) :=
        a2_fold_posLe_Q st1.trail problem.domains s ((mn + mx) / 2)
          ⟨e, hem, hentry⟩
      rw [← hcoh] at hfold
      rcases hfold with h1 | h2
      · -- singleton: the extrema collapse
        have := a2_singleton_extrema h1 hmn hmx
        omega
      · -- bounded: the attained max is below the midpoint
        obtain ⟨v, hvm, hvv⟩ := a2_domMaxI_attained hmx
        have hle : mx ≤ (mn + mx) / 2 := h2 v hvm mx hvv
        omega

/-! ## Helper 6: the decided state's conflict clearance -/

/-- THE DECISION ARM'S CONFLICT CLEARANCE: enqueuing the bisection
    decision at a fresh level keeps the conflict slot clear — the skip
    and fresh arms never touch it (the propagated state is
    conflict-free), and the opposing arm is excluded by
    `a2_decide_not_opposing` (the level bump does not change the
    trail, so the branch conditions are the propagated state's). -/
theorem a2_decided_conflict_none {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {st1 : State} {hl : Literal}
    (hconf : st1.conflict = none)
    (hcoh : DomainCoherent problem st1)
    (hq : decideLiteral st1 = some hl) :
    (enqueueNorm (newDecisionLevel st1) hl none).conflict = none := by
  unfold enqueueNorm
  simp only
  split
  · -- skip arm: the state is newDecisionLevel st1 itself
    show (newDecisionLevel st1).conflict = none
    exact hconf
  · split
    · -- opposing arm: excluded
      exfalso
      rename_i hskip hopp
      have hopp' : st1.negOnTrail hl.norm = true := hopp
      rw [a2_decide_not_opposing hcoh hq] at hopp'
      exact absurd hopp' (by simp)
    · -- fresh arm: enqueue does not touch the conflict slot
      rename_i hskip hopp
      show (enqueue (newDecisionLevel st1) (hl.norm) none).conflict = none
      exact hconf

/-- The propagated state's Level0Solved, as a standalone lemma with
    exactly the hypotheses available at the decision-arm position
    (the level-split proof copied from the conflict arm's `hL01`,
    Run.lean 2143-2236 — arm-independent). -/
theorem a2_propagated_level0Solved
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (st : State)
    (hnone : st.conflict = none)
    (hinv : RunInv problem constraintHolds props st)
    (hL0 : Level0Solved problem constraintHolds st) :
    Level0Solved problem constraintHolds
      (propagateLoop (engineFuel st) props st) := by
  have hpl := propagateLoop_decisionLevel props
    (engineFuel st) st
  cases hlv : (propagateLoop (engineFuel st) props
    st).decisionLevel with
  | zero =>
      -- level-0: the conflict-carrying SolvedBy transfer
      have hlevel0 : st.decisionLevel = 0 := by
        rw [← hpl]; exact hlv
      have hsolved0 : SolvedBy problem constraintHolds st :=
        level0Solved_solvedBy hlevel0 hinv.rooted hinv.coherent hL0
      have hclent : ∀ c ∈ st.clauses, ∀ a,
          ProblemSolution problem constraintHolds a →
            ∃ l ∈ c, l.eval a = some true := by
        intro c hc a ha
        rw [hinv.clausesFixed] at hc
        exact hdb c hc a ha
      have hlnent : ∀ c ∈ st.learned, ∀ a,
          ProblemSolution problem constraintHolds a →
            ∃ l ∈ c, l.eval a = some true := by
        intro c hc a ha
        have hmem : c ∈ (repairAfterBackjump problem 0
            st).learned := hc
        exact (hL0 a ha).2.2.2 c hmem
      have hsolved1 : SolvedBy problem constraintHolds
          (propagateLoop (engineFuel st) props st) :=
        propagateLoop_solvedBy_any hsafe hsolvable st.clauses
          st.learned hclent hlnent (engineFuel st) st hnone
          hsolved0 hinv.coherent rfl rfl
      -- the level-0 shape: all entries at level 0
      have hrooted1 : ∀ e ∈ (propagateLoop (engineFuel st)
          props st).trail,
          e.level ≤ (propagateLoop (engineFuel st)
            props st).decisionLevel :=
        propagateLoop_rooted (engineFuel st) st
          hinv.rooted
      -- the level-0 solved: at a level-0 state whose entries
      -- are all at level 0, Level0Solved ↔ SolvedBy (the
      -- projection is the state itself); prove the backward
      -- direction here from hsolved1
      intro a ha
      have hrep := hsolved1 a ha
      obtain ⟨hfit, htrail, hcl, hln⟩ := hrep
      refine ⟨?_, ?_, hcl, hln⟩
      · exact repair0_fits (problem := problem) ha.1
          (fun e he _ => htrail e he)
      · intro e he
        -- the repair's trail IS the 0-filtered trail; all
        -- entries are at level 0 so the filter keeps
        -- everything and the trails coincide
        have hfil : List.filter (fun e =>
            decide (e.level ≤ 0))
            (propagateLoop (engineFuel st) props st).trail
            = (propagateLoop (engineFuel st)
              props st).trail := by
          rw [List.filter_eq_self]
          intro e2 he2
          have hle : e2.level ≤ (propagateLoop
              (engineFuel st) props st).decisionLevel :=
            hrooted1 e2 he2
          rw [hlv] at hle
          simpa using hle
        have hmem : e ∈ (propagateLoop (engineFuel st)
            props st).trail := by
          have hfilt : e ∈ List.filter (fun e =>
              decide (e.level ≤ 0))
              (propagateLoop (engineFuel st) props st).trail := he
          rw [hfil] at hfilt
          exact hfilt
        exact htrail e hmem
  | succ n =>
      -- positive level: the level-0 subtrail is the entry's
      -- own (fresh enqueues at the current positive level)
      unfold Level0Solved at hL0 ⊢
      -- the whole projection records are EQUAL: both are
      -- built from the same kept trail (hkey), the same
      -- fold, and the same fields — rewrite the hypothesis
      -- hL0's projection into the goal's by hkey's
      -- congruence on the repair record
      have hrec : repairAfterBackjump problem 0
          (propagateLoop (engineFuel st) props st)
          = repairAfterBackjump problem 0 st := by
        unfold repairAfterBackjump
        rw [propagateLoop_filter0_pos (engineFuel st) st
          (by rw [← hpl]; omega) hinv.rooted]
        -- the remaining fields: the propagated state's
        -- clauses/learned/queue are the entry's own (the
        -- loop never modifies them)
        rw [propagateLoop_clauses (engineFuel st) st,
          propagateLoop_learned (engineFuel st) st,
          propagateLoop_queue (engineFuel st) st]
      rw [hrec]
      exact hL0

/-- The decided state's RunInv, as a standalone lemma with exactly the
    hypotheses available at the decision-arm position. -/
theorem a2_decided_runInv
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    {st1 : State} {hl : Literal}
    (hinv1 : RunInv problem constraintHolds props st1)
    (_hq : decideLiteral st1 = some hl) :
    RunInv problem constraintHolds props
      (enqueueNorm (newDecisionLevel st1) hl none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- coherent: the level bump does not touch domains or trail
    exact enqueueNorm_coherent hinv1.coherent
  · -- clausesFixed
    exact enqueueNorm_clausesFixed hinv1.clausesFixed
  · -- learnedEntailed
    exact enqueueNorm_learnedEntailed hinv1.learnedEntailed
  · -- rooted: the fresh entry is stamped at the (positive) new level
    exact enqueueNorm_rooted
      (fun e he => Nat.le_trans (hinv1.rooted e he)
        (Nat.le_succ st1.decisionLevel))
  · -- trailNorm
    exact enqueueNorm_trailNorm hinv1.trailNorm
  · -- reasonNorm: the decision has no reason (vacuous fresh clause)
    exact enqueueNorm_reasonNorm hinv1.reasonNorm
      (fun r hr => absurd hr (by simp))
  · -- reasonValid: dually vacuous
    exact enqueueNorm_reasonValid hinv1.reasonValid
      (fun r hr => absurd hr (by simp))
  · -- rootFacts: the fresh entry is above level 0
    exact enqueueNorm_rootFacts_pos
      (by
        intro hcon
        have : st1.decisionLevel + 1 = 0 := hcon
        omega)
      hinv1.rootFacts
  · -- clausesNorm
    intro c hc q hq2
    have hcl : (enqueueNorm (newDecisionLevel st1) hl none).clauses
        = (newDecisionLevel st1).clauses := enqueueNorm_clauses
    rw [hcl] at hc
    exact hinv1.clausesNorm c hc q hq2
  · -- learnedNorm
    intro c hc q hq2
    have hln : (enqueueNorm (newDecisionLevel st1) hl none).learned
        = (newDecisionLevel st1).learned := enqueueNorm_learned
    rw [hln] at hc
    exact hinv1.learnedNorm c hc q hq2

/-! ## A4: trail distinctness, the analyzer lemmas, and the analysis arm transfer -/

/-! ## Part 1: literal algebra -/

/-- A literal and its (normalized) negation cannot both be true at
    an assignment. -/
theorem eval_not_both {l : Literal} {a : Assignment}
    (h : l.eval a = some true) :
    l.negate.eval a ≠ some true ∧ (l.negate.norm).eval a ≠ some true := by
  refine ⟨?_, ?_⟩
  · rw [Literal.eval_negate l a, h]; simp
  · rw [Literal.norm_eval (l.negate) a, Literal.eval_negate l a, h]; simp

/-- Negation and normalization commute: the normalized negation of a
    normalized literal is the negation's normal form. (Transport for
    the opposing-entry literal identity.) -/
theorem norm_negate_norm (l : Literal) :
    (l.norm).negate.norm = l.negate.norm := by
  cases l with
  | mk atom positive =>
      cases atom with
      | intLe s k => cases positive <;> rfl
      | boolEq s b => cases positive <;> cases b <;> rfl
      | intNe s k => cases positive <;> rfl

/-- Norm is idempotent — the leaf nogood's mapped literals (each
    `e.literal.negate.norm`) are their own normal form. -/
theorem leafNogood_norm (tr : List TrailEntry)
    (q : Literal)
    (hq : q ∈ (tr.filter (fun e => e.level > 0)).map
      (fun e => e.literal.negate.norm)) :
    q = q.norm := by
  obtain ⟨e, hemem, hqe⟩ := List.mem_map.mp hq
  rw [← hqe]
  cases e.literal with
  | mk atom positive =>
      cases atom with
      | intLe s k =>
          cases positive <;>
            (first
              | rfl
              | (show Literal.negate (Literal.norm (Literal.mk (Atom.intLe s k) _)) = _
                  rfl))
      | boolEq s b =>
          cases positive <;> cases b <;>
            (first
              | rfl
              | (show Literal.negate (Literal.norm (Literal.mk (Atom.boolEq s b) _)) = _
                  rfl))
      | intNe s k =>
          cases positive <;>
            (first
              | rfl
              | (show Literal.negate (Literal.norm (Literal.mk (Atom.intNe s k) _)) = _
                  rfl))

/-! ## Part 2: the trail-literal-distinctness invariant -/

/-- The engine's trail never carries two entries with the same
    literal: `enqueueNorm` skips already-present literals (and its
    opposing arm does not touch the trail), and repairs filter a
    distinct trail. This is the invariant A3's counterexample
    (`counterexample_opposing_fires`,
    `LeanFzn/Solver/UIP/Proofs/Obstructions.lean`)
    shows is NOT derivable from RunInv + Level0Solved — it must be
    carried by the induction (as a fourth IH premise, like
    Level0Solved). Stated over the raw trail so the analyzer
    (`analyzeTrail_uip_current`) can consume it. The counterexample
    witness itself is machine-checked in
    `LeanFzn/Solver/UIP/Proofs/Obstructions.lean` (`counterexample_opposing_fires`). -/
def TrailDistinct (trail : List TrailEntry) : Prop :=
  ∀ e1 ∈ trail, ∀ e2 ∈ trail, e1.literal = e2.literal → e1 = e2

/-- Appending a fresh entry whose literal is absent from the trail
    preserves distinctness. -/
theorem trailDistinct_append {trail : List TrailEntry} {l : Literal}
    {level : Nat} {reason : Option Reason}
    (h : TrailDistinct trail)
    (hnotmem : ∀ e ∈ trail, e.literal ≠ l) :
    TrailDistinct (trail ++ [TrailEntry.mk l level reason]) := by
  intro e1 he1 e2 he2 hlit
  rcases List.mem_append.mp he1 with h1 | h1
  · rcases List.mem_append.mp he2 with h2 | h2
    · exact h e1 h1 e2 h2 hlit
    · exfalso
      have h2' : e2 = TrailEntry.mk l level reason := by simpa using h2
      rw [h2'] at hlit
      exact hnotmem e1 h1 (by simpa using hlit)
  · rcases List.mem_append.mp he2 with h2 | h2
    · exfalso
      have h1' : e1 = TrailEntry.mk l level reason := by simpa using h1
      rw [h1'] at hlit
      exact hnotmem e2 h2 (by simpa using hlit.symm)
    · have h1' : e1 = TrailEntry.mk l level reason := by simpa using h1
      have h2' : e2 = TrailEntry.mk l level reason := by simpa using h2
      rw [h1', h2']

/-- `enqueueNorm` preserves trail distinctness UNCONDITIONALLY: the
    skip and opposing arms leave the trail unchanged, and the fresh
    arm fires only when the (normalized) literal is not on the
    trail. -/
theorem enqueueNorm_trailDistinct {st : State} {l0 : Literal}
    {reason : Option Reason}
    (h : TrailDistinct st.trail) :
    TrailDistinct (enqueueNorm st l0 reason).trail := by
  unfold enqueueNorm
  simp only
  split
  · exact h
  · split
    · exact h
    · -- fresh arm: the branch condition says the literal is absent
      rename_i hskip hopp
      have hnotmem : ∀ e ∈ st.trail, e.literal ≠ Literal.norm l0 := by
        intro e he hcon
        refine hskip ?_
        unfold State.litOnTrail
        rw [List.any_eq_true]
        refine ⟨e, he, ?_⟩
        simp only [litEqB, decide_eq_true_eq]
        rw [norm_norm l0]
        exact hcon
      show TrailDistinct (st.trail ++
        [TrailEntry.mk (Literal.norm l0) st.decisionLevel reason])
      exact trailDistinct_append h hnotmem

/-- Repairs preserve distinctness (the kept subtrail is a filter of
    a distinct trail). -/
theorem repair_trailDistinct {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {level : Nat} {st : State}
    (h : TrailDistinct st.trail) :
    TrailDistinct (repairAfterBackjump problem level st).trail := by
  intro e1 he1 e2 he2 hlit
  refine h e1 ?_ e2 ?_ hlit
  · unfold repairAfterBackjump at he1
    exact (List.mem_filter.mp he1).1
  · unfold repairAfterBackjump at he2
    exact (List.mem_filter.mp he2).1

/-- The propagator sweep preserves distinctness. -/
theorem runPropagators_trailDistinct (props : List Propagator) (st : State)
    (h : TrailDistinct st.trail) :
    TrailDistinct (runPropagators props st).trail := by
  have main : ∀ (ps : List Propagator) (acc : State),
      (∀ q ∈ ps, q ∈ props) →
      TrailDistinct acc.trail →
      TrailDistinct (runPropagators.go ps acc).trail := by
    intro ps
    induction ps with
    | nil => intro acc _ h; exact h
    | cons p rest ih =>
        intro acc hmem h
        simp only [runPropagators.go]
        split
        · exact h
        · rename_i hclear
          match hrun : p.run acc with
          | PropagationResult.stable =>
              exact ih acc (fun q hq => hmem q (List.mem_cons_of_mem _ hq)) h
          | PropagationResult.conflict c => exact h
          | PropagationResult.implied l r =>
              exact ih (enqueueNorm acc l (some r))
                (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
                (enqueueNorm_trailDistinct h)
  exact main props st (fun q hq => hq) h

/-- The propagation loop preserves distinctness (mirrors
    `propagateLoop_rooted`). -/
theorem propagateLoop_trailDistinct {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      TrailDistinct st.trail →
      TrailDistinct (propagateLoop fuel props st).trail := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
      intro st h
      simp only [propagateLoop]
      split
      · exact h
      · rename_i hclear
        cases hscan : scanAll st with
        | none =>
            by_cases hlen : ((runPropagators props st).trail.length ==
                st.trail.length) = true
            · rw [if_pos hlen]
              exact runPropagators_trailDistinct props st h
            · rw [if_neg hlen]
              exact ih (runPropagators props st)
                (runPropagators_trailDistinct props st h)
        | some verdict =>
            match verdict with
            | Sum.inl c => exact h
            | Sum.inr w =>
                obtain ⟨l, r⟩ := w
                exact ih (enqueueNorm st l (some r))
                  (enqueueNorm_trailDistinct h)

/-- The root-fact initialization fold preserves distinctness: its
    litOnTrail guard skips already-present literals, and a fresh
    append has an absent literal. -/
theorem fold_enqueue_trailDistinct : ∀ (ls : List Literal) (st : State),
    (∀ l ∈ ls, l = l.norm) →
    TrailDistinct st.trail →
    TrailDistinct (ls.foldl (fun st l =>
      if st.litOnTrail l then st else enqueue st l none) st).trail := by
  intro ls
  induction ls with
  | nil => intro st _ h; exact h
  | cons l rest ih =>
      intro st hnorm h
      simp only [List.foldl_cons]
      by_cases hg : st.litOnTrail l = true
      · rw [if_pos hg]
        exact ih st (fun l2 hl2 => hnorm l2 (List.mem_cons_of_mem _ hl2)) h
      · rw [if_neg hg]
        have hnotmem : ∀ e ∈ st.trail, e.literal ≠ l := by
          intro e he hcon
          refine hg ?_
          unfold State.litOnTrail
          rw [List.any_eq_true]
          refine ⟨e, he, ?_⟩
          simp only [litEqB, decide_eq_true_eq]
          exact hcon.trans (hnorm l (List.mem_cons_self ..))
        have hrestnorm : ∀ l2 ∈ rest, l2 = l2.norm :=
          fun l2 hl2 => hnorm l2 (List.mem_cons_of_mem _ hl2)
        have hgo := ih (enqueue st l none) hrestnorm
        have htr : (enqueue st l none).trail
            = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
        refine hgo ?_
        rw [htr]
        exact trailDistinct_append h hnotmem

/-- Front-door helper: the root facts are normalized literals. -/
theorem rootFacts_norm : ∀ (s : Nat) (ds : List (List Value))
    (l : Literal), l ∈ rootFacts.go s ds → l = l.norm := by
  intro s ds
  induction ds generalizing s with
  | nil => intro l hl; cases hl
  | cons d rest ih =>
      intro l hl
      simp only [rootFacts.go] at hl
      split at hl
      · -- the some/some arm: negLe s _ :: posLe s _ :: go
        rcases List.mem_cons.mp hl with hl | hl
        · cases hl
          rfl
        · rcases List.mem_cons.mp hl with hl | hl
          · cases hl
            rfl
          · exact ih (s + 1) l hl
      · -- the fallback arm: go (s+1) rest directly
        exact ih (s + 1) l hl

/-- FRONT-DOOR SEED: the initial state (with root facts enqueued)
    has a distinct trail. -/
theorem initialStateWithRoots_trailDistinct
    {Constraint Objective : Type}
    (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) :
    TrailDistinct (initialStateWithRoots problem).trail := by
  unfold initialStateWithRoots
  refine fold_enqueue_trailDistinct (rootFacts problem.domains)
    (initialState problem) ?_ ?_
  · exact rootFacts_norm 0 problem.domains
  · intro e1 h1
    exact absurd h1 (by simp [initialState])

/-! ## Part 3: the analyzer lemmas -/

/-- The falsifier chain (from the 2026-10-01 A3 analysis, re-proved): every
    below pair recorded by a successful trail analysis carries its own
    trail falsifier — an entry at exactly the recorded level whose
    literal is the normalized negation of the recorded literal. -/
private theorem analyzeStep_falsifiers (trail : List TrailEntry)
    (lvl : Nat) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    (∀ p ∈ learnt, ∃ e ∈ trail, p.2 = e.level ∧
        e.literal = p.1.negate.norm) →
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt
        = some (below, uip) →
      ∀ p ∈ below, ∃ e ∈ trail, p.2 = e.level ∧
        e.literal = p.1.negate.norm := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt _ below uip h
      rw [analyzeStep] at h; simp at h
  | succ fuel ih =>
      intro cs skip marks learnt hinv below uip h
      cases cs with
      | nil =>
          rw [analyzeStep] at h
          cases hpivot : nextPivot trail marks with
          | none => rw [hpivot] at h; simp at h
          | some e =>
              rw [hpivot] at h
              simp only [] at h
              by_cases hempty : (marks.filter fun m =>
                  !litEqB m.literal e.literal).isEmpty
              · rw [if_pos hempty] at h
                cases h
                exact hinv
              · rw [if_neg hempty] at h
                cases hreason : e.reason with
                | none => rw [hreason] at h; simp at h
                | some r =>
                    rw [hreason] at h
                    exact ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal)
                      learnt hinv below uip h
      | cons c cs' =>
          cases c with
          | nil =>
              rw [analyzeStep] at h
              exact ih cs' skip marks learnt hinv below uip h
          | cons q0 qs =>
              rw [analyzeStep] at h
              by_cases hskip : skipEq skip q0.norm
              · rw [if_pos hskip] at h
                exact ih (qs :: cs') skip marks learnt hinv below uip h
              · rw [if_neg hskip] at h
                cases hmark : markLit trail lvl marks learnt q0.norm with
                | none => rw [hmark] at h; simp at h
                | some res =>
                    obtain ⟨marks', learnt'⟩ := res
                    rw [hmark] at h
                    -- markLit's shapes (markLit_inv) keep every
                    -- pre-existing pair and add only the freshly
                    -- recorded one WITH its falsifier identity
                    have hinv' : ∀ p ∈ learnt', ∃ e ∈ trail, p.2 = e.level ∧
                        e.literal = p.1.negate.norm := by
                      obtain hshape := markLit_inv trail lvl marks learnt
                        q0.norm marks' learnt' hmark
                      rcases hshape with
                        ⟨m0, hm0, hmlit0, hmm, hlm⟩ |
                        ⟨p0, hp0, hp1_0, hmm, hlm⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, hlvl⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, he0, helv⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, hroot0⟩
                      · rw [hlm]; exact hinv
                      · rw [hlm]; exact hinv
                      · rw [hlm]; exact hinv
                      · -- fresh below record: the new pair IS
                        -- (q', e.level) with e.literal = q'.negate.norm
                        rw [hlm]
                        intro p hp
                        rcases List.mem_cons.mp hp with rfl | hp
                        · exact ⟨e, hetr, rfl, helit⟩
                        · exact hinv p hp
                      · rw [hlm]; exact hinv
                    exact ih (qs :: cs') skip marks' learnt' hinv'
                      below uip h

/-- THE FALSIFIER CHAIN (hbelow's honest replacement). -/
theorem analyzeTrail_falsifiers (trail : List TrailEntry) (lvl : Nat)
    (conflict : Clause) (below : List (Literal × Nat)) (uip : Literal)
    (h : analyzeTrail trail lvl conflict = some (below, uip)) :
    ∀ p ∈ below, ∃ e ∈ trail, p.2 = e.level ∧
      e.literal = p.1.negate.norm := by
  unfold analyzeTrail at h
  exact analyzeStep_falsifiers trail lvl
    (4 * trail.length * trail.length + 256) [conflict] none [] []
    (by intro p hp; cases hp) below uip h

/-- The fold-max fact: `backjumpLevel` = the fold-max of the below
    levels; when it is 0, every below level is 0 (the max of a list
    reaching 0 from below bounds every member by 0). -/
theorem backjump_zero_below_levels
    (trail : List TrailEntry) (lvl : Nat) (conflict : Clause)
    (below : List (Literal × Nat)) (uip : Literal)
    (_h : analyzeTrail trail lvl conflict = some (below, uip)) :
    (below.foldl (fun acc p => max acc p.2) 0 = 0 →
      ∀ p ∈ below, p.2 = 0) ∧
    (∀ p ∈ below, p.2 ≤
      below.foldl (fun acc p => max acc p.2) 0) := by
  -- the fold is monotone in the accumulator
  have hmono : ∀ (bs : List (Literal × Nat)) (acc acc' : Nat),
      acc ≤ acc' →
      acc ≤ bs.foldl (fun a q => max a q.2) acc' := by
    intro bs acc acc' hle
    induction bs generalizing acc acc' with
    | nil => exact hle
    | cons q rest ih2 =>
        simp only [List.foldl_cons]
        exact ih2 acc (max acc' q.2) (Nat.le_trans hle (Nat.le_max_left _ _))
  -- the fold's members are bounded by the fold's value
  have hmemle : ∀ (bs : List (Literal × Nat)) (acc : Nat),
      ∀ p ∈ bs, p.2 ≤ bs.foldl (fun a q => max a q.2) acc := by
    intro bs
    induction bs with
    | nil => intro acc p hp; cases hp
    | cons q rest ih =>
        intro acc p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [List.foldl_cons]
          -- p.2 ≤ max acc p.2 ≤ rest-fold at (max acc p.2)
          -- (hmono at the same accumulator: acc ≤ fold acc)
          have h2 : max acc p.2 ≤
              rest.foldl (fun a q => max a q.2) (max acc p.2) :=
            hmono rest (max acc p.2) (max acc p.2) (Nat.le_refl _)
          omega
        · simp only [List.foldl_cons]
          have h1 := ih (max acc q.2) p hp
          omega
  refine ⟨?_, hmemle below 0⟩
  intro hzero p hp
  have hle := hmemle below 0 p hp
  rw [hzero] at hle
  exact Nat.le_zero.mp hle

/-- `nextPivot`'s found entry matches some mark's literal. -/
private theorem nextPivot_marks (trail : List TrailEntry)
    (marks : List TrailEntry) (e : TrailEntry)
    (h : nextPivot trail marks = some e) :
    ∃ m ∈ marks, e.literal = m.literal := by
  unfold nextPivot at h
  obtain ⟨hp, _, _, _, _⟩ := List.find?_eq_some_iff_append.mp h
  rw [List.any_eq_true] at hp
  obtain ⟨m, hm, hbeq⟩ := hp
  exact ⟨m, hm, (by simpa [litEqB] using hbeq : m.literal = e.literal).symm⟩

/-- The UIP is a CURRENT-LEVEL trail literal: a successful analysis
    terminates at `some (learnt, e.literal)` where `e` is a trail
    entry at the analysis level. The mark discipline (every marked
    entry is a trail entry at exactly lvl) is threaded as the
    auxiliary invariant; it is seeded vacuously and maintained by
    `markLit`'s shapes. The finalization's `nextPivot` finds the
    latest trail entry whose literal matches a mark's; under
    `TrailDistinct` that entry IS the mark, so it carries the
    current level. -/
private theorem analyzeStep_uip_current (trail : List TrailEntry)
    (lvl : Nat) (hdist : TrailDistinct trail) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    ∀ (below : List (Literal × Nat)) (uip : Literal),
      analyzeStep trail lvl fuel cs skip marks learnt
        = some (below, uip) →
      (∀ m ∈ marks, m ∈ trail ∧ m.level = lvl) →
      ∃ f ∈ trail, f.literal = uip ∧ f.level = lvl := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt below uip h _
      rw [analyzeStep] at h; simp at h
  | succ fuel ih =>
      intro cs skip marks learnt below uip h hmarks
      cases cs with
      | nil =>
          rw [analyzeStep] at h
          cases hpivot : nextPivot trail marks with
          | none => rw [hpivot] at h; simp at h
          | some e =>
              rw [hpivot] at h
              simp only [] at h
              by_cases hempty : (marks.filter fun m =>
                  !litEqB m.literal e.literal).isEmpty
              · -- UIP finalization: the returned uip IS e.literal;
                -- e is the LATEST trail entry matching a mark's
                -- literal — under TrailDistinct, e IS that mark
                rw [if_pos hempty] at h
                cases h
                have hetr := nextPivot_trail_mem trail marks e hpivot
                obtain ⟨m, hmm, hlit⟩ := nextPivot_marks trail marks e
                  hpivot
                obtain ⟨mtr, mlvl⟩ := hmarks m hmm
                have heqm : e = m := hdist e hetr m mtr hlit
                exact ⟨e, hetr, rfl, heqm ▸ mlvl⟩
              · rw [if_neg hempty] at h
                cases hreason : e.reason with
                | none => rw [hreason] at h; simp at h
                | some r =>
                    rw [hreason] at h
                    exact ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal)
                      learnt below uip h
                      (fun m hm => hmarks m ((List.mem_filter.mp hm).1))
      | cons c cs' =>
          cases c with
          | nil =>
              rw [analyzeStep] at h
              exact ih cs' skip marks learnt below uip h hmarks
          | cons q0 qs =>
              rw [analyzeStep] at h
              by_cases hskip : skipEq skip q0.norm
              · rw [if_pos hskip] at h
                exact ih (qs :: cs') skip marks learnt below uip h hmarks
              · rw [if_neg hskip] at h
                cases hmark : markLit trail lvl marks learnt q0.norm with
                | none => rw [hmark] at h; simp at h
                | some res =>
                    obtain ⟨marks', learnt'⟩ := res
                    rw [hmark] at h
                    have hmarks' : ∀ m ∈ marks', m ∈ trail ∧
                        m.level = lvl := by
                      obtain hshape := markLit_inv trail lvl marks learnt
                        q0.norm marks' learnt' hmark
                      rcases hshape with
                        ⟨m0, hm0, hmlit0, hmm, hlm⟩ |
                        ⟨p0, hp0, hp1_0, hmm, hlm⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, hlvl⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, he0, helv⟩ |
                        ⟨e, hetr, q', hq'0, helit, hmm, hlm, hroot0⟩
                      · rw [hmm]; exact hmarks
                      · rw [hmm]; exact hmarks
                      · rw [hmm]
                        intro m hm
                        rcases List.mem_cons.mp hm with rfl | hm
                        · exact ⟨hetr, hlvl⟩
                        · exact hmarks m hm
                      · rw [hmm]; exact hmarks
                      · rw [hmm]; exact hmarks
                    exact ih (qs :: cs') skip marks' learnt' below uip h
                      hmarks'

/-- The UIP is a current-level trail literal. -/
theorem analyzeTrail_uip_current (trail : List TrailEntry) (lvl : Nat)
    (hdist : TrailDistinct trail)
    (conflict : Clause) (below : List (Literal × Nat)) (uip : Literal)
    (h : analyzeTrail trail lvl conflict = some (below, uip)) :
    ∃ f ∈ trail, f.literal = uip ∧ f.level = lvl := by
  unfold analyzeTrail at h
  exact analyzeStep_uip_current trail lvl hdist
    (4 * trail.length * trail.length + 256) [conflict] none [] []
    below uip h (by intro m hm; cases hm)

/-! ## Part 4: the backjump-0 asserting justification -/

/-- THE ASSERTING JUSTIFICATION AT BACKJUMP LEVEL 0 (the st2-side
    reconstruction of `asserting_true_at_solutions`'s argument,
    Run.lean:1381 — that lemma requires st1.decisionLevel = 0 and so
    does not apply at a positive-level/backjump-0 conflict): the
    normalized learned clause `lnt` is entailed, and every
    NON-asserting member of `lnt` is falsified at every internal
    solution by a LEVEL-0 root-true entry of the repaired state
    (st2.decisionLevel = 0 + rootedness make ALL of st2's entries
    level-0 root facts). Hence the asserting literal — the remaining
    possible witness — is TRUE at every internal solution. -/
theorem asserting_norm_true_at_backjump_zero
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st2 : State}
    (hrootF2 : RootFacts problem constraintHolds st2.trail)
    (lnt : Clause) (asserting : Literal)
    (hentN : Clause.EntailedBy problem constraintHolds lnt)
    (hbelow2 : ∀ q ∈ lnt, q ≠ asserting →
      ∃ e ∈ st2.trail, e.level = 0 ∧
        e.literal = q.negate.norm)
    (a : Assignment)
    (ha : ProblemSolution problem constraintHolds a) :
    asserting.eval a = some true := by
  -- the entailed clause has a witness true at a
  obtain ⟨w, hw, hev⟩ := hentN a ha
  by_cases hwa : w = asserting
  · rw [← hwa]; exact hev
  · exfalso
    -- w is a below literal: falsified at a by a level-0 root fact
    obtain ⟨e, hemem, hezero, hfals⟩ := hbelow2 w hw hwa
    have hetrue : e.literal.eval a = some true :=
      hrootF2 e hemem hezero a ha
    -- derive w false at a from e's truth
    rw [hfals] at hetrue
    rw [Literal.norm_eval (w.negate) a] at hetrue
    rw [Literal.eval_negate w a] at hetrue
    cases hw2 : w.eval a with
    | none => rw [hw2] at hetrue; exact absurd hetrue (by simp)
    | some b =>
        rw [hw2] at hetrue
        cases b
        · rw [hw2] at hev; exact absurd hev (by simp)
        · simp at hetrue

/-! ## Part 5: the enqueue/repair transfer helpers -/

/-- `SolvedBy` survives a learned-clause gain when the gained clause
    is entailed (the learned field's extra clause is satisfied at
    every internal solution). -/
theorem solvedBy_cons_learned
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {c : Clause}
    (h : SolvedBy problem constraintHolds st)
    (hent : Clause.EntailedBy problem constraintHolds c) :
    SolvedBy problem constraintHolds
      {st with learned := c :: st.learned} := by
  intro a ha
  obtain ⟨hfit, htrail, hcl, hln⟩ := h a ha
  exact ⟨hfit, htrail, hcl, fun c2 hc2 => by
    rcases List.mem_cons.mp hc2 with rfl | hc2
    · exact hent a ha
    · exact hln c2 hc2⟩

/-- Repair-to-zero commutes with the learned gain (the repair only
    reads the trail/clauses/queue; the learned field passes
    through). -/
theorem repair0_learned_update (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (st : State) (c : Clause) :
    repairAfterBackjump problem 0 {st with learned := c :: st.learned}
      = {repairAfterBackjump problem 0 st with
          learned := c :: (repairAfterBackjump problem 0 st).learned} := by
  rfl

/-- The learned-DB extension preserves the run invariant: every field
    is either untouched by the record update or (for
    `learnedEntailed`) the cons of the new clause's own entitlement. -/
theorem runInv_cons_learned
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {st : State} {c : Clause}
    (h : RunInv problem constraintHolds props st)
    (hent : c.EntailedBy problem constraintHolds)
    (hnorm : ∀ l ∈ c, l = l.norm) :
    RunInv problem constraintHolds props
      {st with learned := c :: st.learned} := by
  refine ⟨h.coherent, h.clausesFixed, ?_, h.rooted, h.trailNorm,
    h.reasonNorm, h.reasonValid, h.rootFacts, h.clausesNorm, ?_⟩
  · intro c2 hc2
    rcases List.mem_cons.mp hc2 with rfl | hc3
    · exact hent
    · exact h.learnedEntailed c2 hc3
  · intro c2 hc2 q hq
    rcases List.mem_cons.mp hc2 with rfl | hc3
    · exact hnorm q hq
    · exact h.learnedNorm c2 hc3 q hq

/-- Raising the decision level preserves all run facts; only the upper
    bound on trail levels changes. -/
theorem newDecisionLevel_runInv
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {st : State}
    (h : RunInv problem constraintHolds props st) :
    RunInv problem constraintHolds props (newDecisionLevel st) := by
  exact ⟨h.coherent, h.clausesFixed, h.learnedEntailed,
    fun e he => Nat.le_trans (h.rooted e he) (Nat.le_succ _),
    h.trailNorm, h.reasonNorm, h.reasonValid, h.rootFacts,
    h.clausesNorm, h.learnedNorm⟩

/-- An explained enqueue above level zero preserves the run invariant.
    Entailment and pivot membership validate the reason; the positive
    stamp keeps the new literal out of the root-fact obligation. -/
theorem enqueueNorm_runInv_pos
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {st : State} {l : Literal} {c : Clause}
    (h : RunInv problem constraintHolds props st)
    (hpos : st.decisionLevel ≠ 0)
    (hent : c.EntailedBy problem constraintHolds)
    (hnorm : ∀ q ∈ c, q = q.norm)
    (hpiv : l.norm ∈ c) :
    RunInv problem constraintHolds props
      (enqueueNorm st l (some { clause := c })) := by
  refine ⟨enqueueNorm_coherent h.coherent,
    enqueueNorm_clausesFixed h.clausesFixed,
    enqueueNorm_learnedEntailed h.learnedEntailed,
    enqueueNorm_rooted h.rooted, enqueueNorm_trailNorm h.trailNorm,
    enqueueNorm_reasonNorm h.reasonNorm ?_,
    enqueueNorm_reasonValid h.reasonValid ?_,
    enqueueNorm_rootFacts_pos hpos h.rootFacts, ?_, ?_⟩
  · intro r hr q hq
    cases hr
    exact hnorm q hq
  · intro r hr
    cases hr
    exact ⟨hent, by simpa using hpiv⟩
  · intro c2 hc q hq
    rw [enqueueNorm_clauses] at hc
    exact h.clausesNorm c2 hc q hq
  · intro c2 hc q hq
    rw [enqueueNorm_learned] at hc
    exact h.learnedNorm c2 hc q hq

/-- Repair-to-zero ignores an enqueue at a POSITIVE level: the fresh
    entry is stamped above 0 and dropped by the 0-filter; the skip and
    opposing arms leave the trail unchanged (and the repair clears
    the opposing arm's conflict). -/
theorem repair0_enqueue (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (st : State) (l0 : Literal) (reason : Option Reason)
    (hpos : 0 < st.decisionLevel) :
    repairAfterBackjump problem 0 (enqueueNorm st l0 reason)
      = repairAfterBackjump problem 0 st := by
  unfold repairAfterBackjump
  simp only [enqueueNorm]
  split
  · -- skip arm: the state is unchanged
    rfl
  · split
    · -- opposing arm: the conflict slot is set; the repair clears it
      rfl
    · -- fresh arm: the enqueue's trail equation and the 0-filter drop
      rename_i hskip hopp
      have htr : (enqueue st (Literal.norm l0) reason).trail
          = st.trail ++ [TrailEntry.mk (Literal.norm l0) st.decisionLevel
              reason] := rfl
      rw [htr]
      have hfil : (st.trail ++ [TrailEntry.mk (Literal.norm l0)
          st.decisionLevel reason]).filter (fun e =>
            decide (e.level ≤ 0))
          = st.trail.filter (fun e => decide (e.level ≤ 0)) := by
        rw [List.filter_append]
        have hnil : List.filter (fun e => decide (e.level ≤ 0))
            [TrailEntry.mk (Literal.norm l0) st.decisionLevel reason]
            = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [if_neg]
          intro hcon
          have hh : st.decisionLevel ≤ 0 := of_decide_eq_true hcon
          omega
        rw [hnil, List.append_nil]
      rw [hfil]
      -- the remaining fields coincide (enqueue only extends the
      -- trail; the repair's fold sees the same kept trail)
      rfl

/-- Repair-to-zero is the identity on a level-0, conflict-free,
    coherent state whose entries all sit at level 0. -/
theorem repair0_id (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective) (st : State)
    (hall0 : ∀ e ∈ st.trail, e.level ≤ 0)
    (hcoh : DomainCoherent problem st)
    (hconf : st.conflict = none)
    (hdl : st.decisionLevel = 0) :
    repairAfterBackjump problem 0 st = st := by
  have hfil : st.trail.filter (fun e => decide (e.level ≤ 0))
      = st.trail := by
    rw [List.filter_eq_self]
    intro e he
    have := hall0 e he
    simpa using this
  unfold repairAfterBackjump
  simp only [hfil]
  have hfold : st.trail.foldl (fun acc e => domOfLit acc e.literal)
      problem.domains = st.domains := hcoh.symm
  rw [hfold, ← hdl, ← hconf]

/-- The enqueue's conflict clearance given the opposing branch's
    exclusion: the skip and fresh arms keep the (clear) entry slot. -/
theorem enqueueNorm_conflict_none_of_neg {st : State} {l0 : Literal}
    {reason : Option Reason}
    (hnone : st.conflict = none)
    (hneg : st.negOnTrail l0.norm = false) :
    (enqueueNorm st l0 reason).conflict = none := by
  unfold enqueueNorm
  simp only
  split
  · exact hnone
  · split
    · exfalso
      rename_i hskip hneg2
      rw [hneg] at hneg2
      exact absurd hneg2 (by simp)
    · exact hnone

/-! ## Part 6: the analysis arm's complete transfer -/

/-- THE ANALYSIS ARM'S COMPLETE TRANSFER: from the propagated state
    st1 (run-invariant, trail-distinct, conflict-carrying with an
    entitled conflict cc0) whose analysis yields `an`, the composite
    recursive entry
      st4 = enqueueNorm {st2 with learned := lnt :: st2.learned}
              an.asserting (some {clause := lnt})
    (st2 = repairAfterBackjump .. an.backjumpLevel st1,
     lnt = an.learned.map (·.norm)) satisfies ALL FOUR IH premises:
    conflict-clear, RunInv, Level0Solved, TrailDistinct.

    The opposing branch of the asserting enqueue is REFUTED in both
    backjump shapes:
    * backjump 0: the asserting literal is TRUE at every internal
      solution — the entailed normalized learned clause's other
      members are falsified by level-0 root-true entries of st1
      (the analyzer's falsifier chain + the fold-max collapse to 0
      + st1's rooted level-0 trail) — while the opposing branch's
      entry would make the NEGATION true at every solution (a
      retained level-0 root fact): `eval_not_both` + `hsolvable`
      refute.
    * backjump > 0 (hstrict): the UIP is a current-level trail
      literal of st1 (analyzeTrail_uip_current), DROPPED by the
      repair (backjump < st1.decisionLevel), while an opposing
      entry would be RETAINED at the backjump level with the same
      (normalized) literal — two distinct st1-trail entries with
      one literal: TrailDistinct st1 refutes. -/
theorem a4_analyzed_entry
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator}
    {st1 : State} {an : ConflictAnalysis} {cc0 : Clause}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hinv1 : RunInv problem constraintHolds props st1)
    (hdist1 : TrailDistinct st1.trail)
    (hconf1 : st1.conflict = some cc0)
    (hanalyze : analyzeConflict st1 = some an)
    (hentN : Clause.EntailedBy problem constraintHolds
      (an.learned.map (fun l => l.norm)))
    (hstrict : an.backjumpLevel < st1.decisionLevel)
    (hL01 : Level0Solved problem constraintHolds st1) :
    ∀ (st2 st3 : State) (lnt : Clause),
      st2 = repairAfterBackjump problem an.backjumpLevel st1 →
      lnt = an.learned.map (fun l => l.norm) →
      st3 = {st2 with learned := lnt :: st2.learned} →
      (enqueueNorm st3 an.asserting
          (some { clause := lnt })).conflict = none ∧
      RunInv problem constraintHolds props
        (enqueueNorm st3 an.asserting (some { clause := lnt })) ∧
      Level0Solved problem constraintHolds
        (enqueueNorm st3 an.asserting (some { clause := lnt })) ∧
      TrailDistinct (enqueueNorm st3 an.asserting
        (some { clause := lnt })).trail := by
  intro st2 st3 lnt hst2 hlnt hst3
  -- the st2-side invariants (the repair's own transfers)
  have hbl : an.backjumpLevel ≤ st1.decisionLevel :=
    (Nat.lt_iff_le_and_ne.mp hstrict).1
  have hinv2 : RunInv problem constraintHolds props st2 :=
    hst2 ▸ repair_runInv hinv1 hbl
  have hL02 : Level0Solved problem constraintHolds st2 :=
    hst2 ▸ level0Solved_repair hL01
  have hst2lvl : st2.decisionLevel = an.backjumpLevel :=
    hst2 ▸ (repair_decisionLevel problem _ _)
  have hst2conf : st2.conflict = none :=
    hst2 ▸ (repair_conflict problem _ _)
  -- the st3-side field projections (the learned update changes only
  -- the learned field)
  have hentNl : Clause.EntailedBy problem constraintHolds lnt := by
    rw [hlnt]; exact hentN
  -- the analysis output's construction: invert hanalyze into the
  -- analyzer's (below, uip) and the field equations
  obtain ⟨below, uip, htrail, hfold, hlearned, hassert⟩ :
      ∃ below uip, analyzeTrail st1.trail st1.decisionLevel cc0
          = some (below, uip) ∧
        an.backjumpLevel = below.foldl (fun acc p => max acc p.2) 0 ∧
        an.learned = uip.negate :: below.map (fun p => p.1) ∧
        an.asserting = uip.negate := by
    unfold analyzeConflict at hanalyze
    simp only [hconf1] at hanalyze
    cases hres : analyzeTrail st1.trail st1.decisionLevel cc0 with
    | none => rw [hres] at hanalyze; exact absurd hanalyze (by simp)
    | some res =>
        obtain ⟨below, uip⟩ := res
        rw [hres] at hanalyze
        refine ⟨below, uip, rfl, ?_, ?_, ?_⟩ <;>
          · injection hanalyze with h1
            cases h1
            rfl
  -- the UIP is normalized (it is a st1-trail literal)
  have huipnorm : uip = uip.norm := by
    obtain ⟨f, hfmem1, hflit, _⟩ :=
      analyzeTrail_uip_current st1.trail st1.decisionLevel hdist1
        cc0 below uip htrail
    rw [← hflit]
    exact hinv1.trailNorm f hfmem1
  -- THE OPPOSING EXCLUSION, both backjump shapes
  have hneg : st3.negOnTrail an.asserting.norm = false := by
    unfold State.negOnTrail
    cases hneg : (st3.trail.any
        fun e => litEqB e.literal an.asserting.norm.negate.norm) with
    | false => rfl
    | true =>
        exfalso
        rw [List.any_eq_true] at hneg
        obtain ⟨e, hemem3, hbeq⟩ := hneg
        have helit : e.literal
            = an.asserting.norm.negate.norm := by
          simpa only [litEqB, decide_eq_true_eq] using hbeq
        -- e is a retained st1-trail entry
        have hkept : e ∈ st1.trail ∧ e.level ≤ an.backjumpLevel := by
          have hemem2 : e ∈ st2.trail := by
            rw [hst3] at hemem3
            exact hemem3
          rw [hst2] at hemem2
          unfold repairAfterBackjump at hemem2
          have hmem := (List.mem_filter.mp hemem2)
          exact ⟨hmem.1, of_decide_eq_true hmem.2⟩
        obtain ⟨hemem1, heleve⟩ := hkept
        cases hb : an.backjumpLevel with
        | zero =>
            rw [hb] at heleve
            -- CASE backjump 0: the asserting literal is TRUE at
            -- every solution while e (a level-0 root fact of st1)
            -- makes its normalized negation true there
            have hezero : e.level = 0 := Nat.le_zero.mp heleve
            have hbelow2 : ∀ q ∈ lnt, q ≠ an.asserting.norm →
                ∃ f ∈ st2.trail, f.level = 0 ∧
                  f.literal = q.negate.norm := by
              intro q hq hqne
              rw [hlnt] at hq
              obtain ⟨w, hw, hqeq⟩ := List.mem_map.mp hq
              have hwne : w ≠ an.asserting := by
                intro hwcon
                rw [hwcon] at hqeq
                exact hqne hqeq.symm
              have hwmem : ∃ p ∈ below, p.1 = w := by
                rw [hlearned] at hw
                rcases List.mem_cons.mp hw with hw2 | hw2
                · exfalso
                  rw [hw2] at hwne
                  exact hwne (hassert ▸ rfl)
                · obtain ⟨p, hpmem, hpeq⟩ := List.mem_map.mp hw2
                  exact ⟨p, hpmem, hpeq⟩
              obtain ⟨p, hpmem, hpeq⟩ := hwmem
              obtain ⟨f, hfmem1, hflvl, hflit⟩ :=
                analyzeTrail_falsifiers st1.trail st1.decisionLevel
                  cc0 below uip htrail p hpmem
              have hfoldzero : below.foldl (fun acc p => max acc p.2) 0
                  = 0 := by rw [← hfold, hb]
              have hp0 : p.2 = 0 :=
                (backjump_zero_below_levels st1.trail st1.decisionLevel
                  cc0 below uip htrail).1 hfoldzero p hpmem
              have hfmem2 : f ∈ st2.trail := by
                rw [hst2]
                refine repair_kept_mem problem an.backjumpLevel st1 f
                  hfmem1 ?_
                show decide (f.level ≤ an.backjumpLevel) = true
                rw [← hflvl, hp0]
                simp
              refine ⟨f, hfmem2, by rw [← hflvl, hp0], ?_⟩
              rw [← hqeq, ← hpeq, norm_negate_norm p.1]
              exact hflit
            have hlita : an.asserting.norm.eval
                (hsolvable.choose) = some true :=
              asserting_norm_true_at_backjump_zero
                (problem := problem)
                (constraintHolds := constraintHolds)
                hinv2.rootFacts lnt an.asserting.norm hentNl hbelow2
                hsolvable.choose hsolvable.choose_spec
            have hete : e.literal.eval hsolvable.choose = some true :=
              hinv1.rootFacts e hemem1 hezero _ hsolvable.choose_spec
            rw [helit] at hete
            exact absurd hete (eval_not_both hlita).2
        | succ bj =>
            -- CASE backjump > 0: the UIP-vs-retained distinctness
            obtain ⟨f, hfmem1, hflit, hflvl⟩ :=
              analyzeTrail_uip_current st1.trail st1.decisionLevel
                hdist1 cc0 below uip htrail
            have heuip : e.literal = uip.norm := by
              rw [helit, norm_negate_norm an.asserting, hassert,
                Literal.negate_negate uip]
            have hebelow : e.level < f.level := by
              rw [hflvl]
              have hlt : an.backjumpLevel < st1.decisionLevel :=
                hstrict
              omega
            have hfinal : f = e :=
              hdist1 f hfmem1 e hemem1
                (hflit.trans (huipnorm.trans heuip.symm))
            rw [hfinal] at hebelow
            exact absurd hebelow (by omega)
  -- with the opposing excluded, the conflict stays clear
  have hst3conf : st3.conflict = none := by
    rw [hst3]; exact hst2conf
  have hconf4 : (enqueueNorm st3 an.asserting
      (some { clause := lnt })).conflict = none :=
    enqueueNorm_conflict_none_of_neg hst3conf hneg
  -- hoisted st3-side facts (shared by the RunInv and Level0Solved arms)
  have hnormr : ∀ q ∈ lnt, q = q.norm := by
    intro q hq
    rw [hlnt] at hq
    obtain ⟨w, hw, hq2⟩ := List.mem_map.mp hq
    rw [← hq2, norm_norm w]
  have hpiv : an.asserting.norm ∈ lnt := by
    rw [hlnt]
    exact analyzeHead_mem (state := st1) (an := an) hanalyze
  have hfreshN : ∀ r ∈ (some ({ clause := lnt } : Reason) :
      Option Reason), ∀ q ∈ r.clause, q = q.norm := by
    intro r hrmem q hq
    cases hrmem
    exact hnormr q hq
  have hfreshV : ∀ r ∈ (some ({ clause := lnt } : Reason) :
      Option Reason),
      Reason.Valid problem constraintHolds r an.asserting.norm := by
    intro r hrmem
    cases hrmem
    exact ⟨hentNl, by simpa using hpiv⟩
  have hlearn3 : ∀ c ∈ st3.learned,
      Clause.EntailedBy problem constraintHolds c := by
    intro c hc
    rw [hst3] at hc
    rcases List.mem_cons.mp hc with rfl | hc2
    · exact hentNl
    · exact hinv2.learnedEntailed c hc2
  have hlit0 : an.backjumpLevel = 0 →
      ∀ a, ProblemSolution problem constraintHolds a →
        an.asserting.norm.eval a = some true := by
    intro hzero a ha
    have hbelow2 : ∀ q ∈ lnt, q ≠ an.asserting.norm →
        ∃ f ∈ st2.trail, f.level = 0 ∧
          f.literal = q.negate.norm := by
      intro q hq hqne
      rw [hlnt] at hq
      obtain ⟨w, hw, hqeq⟩ := List.mem_map.mp hq
      have hwne : w ≠ an.asserting := by
        intro hwcon
        rw [hwcon] at hqeq
        exact hqne hqeq.symm
      have hwmem : ∃ p ∈ below, p.1 = w := by
        rw [hlearned] at hw
        rcases List.mem_cons.mp hw with hw2 | hw2
        · exfalso
          rw [hw2] at hwne
          exact hwne (hassert ▸ rfl)
        · obtain ⟨p, hpmem, hpeq⟩ := List.mem_map.mp hw2
          exact ⟨p, hpmem, hpeq⟩
      obtain ⟨p, hpmem, hpeq⟩ := hwmem
      obtain ⟨f, hfmem1, hflvl, hflit⟩ :=
        analyzeTrail_falsifiers st1.trail st1.decisionLevel
          cc0 below uip htrail p hpmem
      have hfoldzero : below.foldl (fun acc p => max acc p.2) 0
          = 0 := by rw [← hfold, hzero]
      have hp0 : p.2 = 0 :=
        (backjump_zero_below_levels st1.trail st1.decisionLevel
          cc0 below uip htrail).1 hfoldzero p hpmem
      have hfmem2 : f ∈ st2.trail := by
        rw [hst2]
        refine repair_kept_mem problem an.backjumpLevel st1 f
          hfmem1 ?_
        show decide (f.level ≤ an.backjumpLevel) = true
        rw [← hflvl, hp0]
        simp
      refine ⟨f, hfmem2, by rw [← hflvl, hp0], ?_⟩
      rw [← hqeq, ← hpeq, norm_negate_norm p.1]
      exact hflit
    exact asserting_norm_true_at_backjump_zero
      (problem := problem) (constraintHolds := constraintHolds)
      hinv2.rootFacts lnt an.asserting.norm hentNl hbelow2 a ha
  have hrootF3 : RootFacts problem constraintHolds st3.trail := by
    rw [hst3]; exact hinv2.rootFacts
  have hrootF4 : RootFacts problem constraintHolds
      (enqueueNorm st3 an.asserting (some { clause := lnt })).trail := by
    cases hb : an.backjumpLevel with
    | zero => exact enqueueNorm_rootFacts_level0 hrootF3 (hlit0 hb)
    | succ bj =>
        refine enqueueNorm_rootFacts_pos ?_ hrootF3
        intro hcon
        have hzero : st3.decisionLevel = 0 := hcon
        rw [hst3, hst2lvl, hb] at hzero
        exact absurd hzero (by simp)
  have hcoh3 : DomainCoherent problem st3 := by
    rw [hst3]; exact hinv2.coherent
  have hrooted3 : ∀ e ∈ st3.trail, e.level ≤ st3.decisionLevel := by
    rw [hst3]; exact hinv2.rooted
  have htrailNorm3 : ∀ e ∈ st3.trail, e.literal = e.literal.norm := by
    rw [hst3]; exact hinv2.trailNorm
  have hreasonNorm3 : ∀ e ∈ st3.trail, ∀ r ∈ e.reason,
      ∀ q ∈ r.clause, q = q.norm := by
    rw [hst3]; exact hinv2.reasonNorm
  have hreasonValid3 : ∀ e ∈ st3.trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal := by
    rw [hst3]; exact hinv2.reasonValid
  have hclausesNorm3 : ∀ c ∈ st3.clauses, ∀ q ∈ c, q = q.norm := by
    rw [hst3]; exact hinv2.clausesNorm
  have hlearnedNorm3 : ∀ c ∈ st3.learned, ∀ q ∈ c, q = q.norm := by
    rw [hst3]
    intro c hc q hq
    rcases List.mem_cons.mp hc with rfl | hc2
    · exact hnormr q hq
    · exact hinv2.learnedNorm c hc2 q hq
  have hclfix3 : st3.clauses = problem.clauses := by
    rw [hst3]; exact hinv2.clausesFixed
  refine ⟨hconf4, ?_, ?_, ?_⟩
  · -- RunInv of the enqueued state
    refine ⟨enqueueNorm_coherent hcoh3,
      enqueueNorm_clausesFixed hclfix3,
      enqueueNorm_learnedEntailed hlearn3,
      enqueueNorm_rooted hrooted3,
      enqueueNorm_trailNorm htrailNorm3,
      enqueueNorm_reasonNorm hreasonNorm3 hfreshN,
      enqueueNorm_reasonValid hreasonValid3 hfreshV,
      hrootF4, ?_, ?_⟩
    · intro c hc q hq
      have hcl : (enqueueNorm st3 an.asserting
          (some { clause := lnt })).clauses = st3.clauses :=
        enqueueNorm_clauses
      rw [hcl] at hc
      exact hclausesNorm3 c hc q hq
    · intro c hc q hq
      have hln : (enqueueNorm st3 an.asserting
          (some { clause := lnt })).learned = st3.learned :=
        enqueueNorm_learned
      rw [hln] at hc
      exact hlearnedNorm3 c hc q hq
  · -- Level0Solved of the enqueued state
    unfold Level0Solved
    cases hb : an.backjumpLevel with
    | zero =>
        have hdl4 : (enqueueNorm st3 an.asserting
            (some { clause := lnt })).decisionLevel = 0 := by
          rw [enqueueNorm_decisionLevel, hst3, hst2lvl, hb]
        have hall0 : ∀ e ∈ (enqueueNorm st3 an.asserting
            (some { clause := lnt })).trail, e.level ≤ 0 := by
          intro e he
          have hrooted4 := enqueueNorm_rooted
            (st := st3) (l0 := an.asserting)
            (reason := some { clause := lnt }) hrooted3
          have := hrooted4 e he
          rw [hdl4] at this
          exact this
        have hsol2 : SolvedBy problem constraintHolds st2 := by
          have hL02' := hL02
          rw [Level0Solved] at hL02'
          have hst2id : repairAfterBackjump problem 0 st2 = st2 :=
            repair0_id problem st2
              (fun e he => by
                have := hinv2.rooted e he
                rw [hst2lvl, hb] at this
                omega)
              hinv2.coherent hst2conf (by rw [hst2lvl, hb])
          rw [hst2id] at hL02'
          exact hL02'
        have hsol3 : SolvedBy problem constraintHolds st3 := by
          rw [hst3]
          exact solvedBy_cons_learned hsol2 hentNl
        obtain ⟨_, hsol4⟩ :=
          enqueueNorm_solvedBy (problem := problem)
            (constraintHolds := constraintHolds)
            (st := st3) (l0 := an.asserting)
            (reason := some { clause := lnt })
            hst3conf hsol3 (hlit0 hb)
        have hst4id : repairAfterBackjump problem 0
            (enqueueNorm st3 an.asserting (some { clause := lnt }))
            = enqueueNorm st3 an.asserting (some { clause := lnt }) :=
          repair0_id problem _
            hall0
            (enqueueNorm_coherent (problem := problem) hcoh3)
            hconf4 hdl4
        rw [hst4id]
        exact hsol4
    | succ bj =>
        have hpos3 : 0 < st3.decisionLevel := by
          rw [hst3, hst2lvl, hb]
          omega
        have hproj : repairAfterBackjump problem 0
            (enqueueNorm st3 an.asserting (some { clause := lnt }))
            = repairAfterBackjump problem 0 st3 :=
          repair0_enqueue problem st3 an.asserting
            (some { clause := lnt }) hpos3
        rw [hproj, hst3, repair0_learned_update problem st2 lnt]
        exact solvedBy_cons_learned
          (show SolvedBy problem constraintHolds
              (repairAfterBackjump problem 0 st2) from hL02) hentNl
  · -- TrailDistinct of the enqueued state
    refine enqueueNorm_trailDistinct ?_
    show TrailDistinct st3.trail
    rw [hst3, hst2]
    exact repair_trailDistinct (problem := problem)
      (st := st1) (level := an.backjumpLevel) hdist1

/-- **THE DECISION-DESCENT MASTER THEOREM (§3 item 3)**: every
    `.unsat` outcome of the engine loop arises at a LEVEL-0,
    CONFLICT-CLEAR entry that solves-by and carries the run
    invariant — exactly the `UnsatRun` obligation's entry shape. The
    induction threads the invariants through every recursive call:
    decisions preserve the level-0 projection
    (`level0Solved_decision`), backjumps preserve it
    (`level0Solved_repair`), the analysis arm's asserting enqueue at
    backjump level 0 is justified by the entailed learned clause and
    the below literals' level-0 falsification
    (`asserting_true_at_solutions` + `enqueueNorm_solvedBy`), and
    conflict-free propagation preserves everything
    (`level0Solved_propagate_clear` + `propagateLoop_runInv`). -/
theorem go_unsat_entry_invariant
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator}
    (hsafe : CoherentSafeUniv problem constraintHolds props)
    (hjust : ∀ (acc : State), DomainCoherent problem acc →
      acc.decisionLevel = 0 →
      RootFacts problem constraintHolds acc.trail →
      (∀ e ∈ acc.trail, e.level ≤ acc.decisionLevel) →
      ∀ p ∈ props, ∀ l r, p.run acc = .implied l r →
        ∀ a, ProblemSolution problem constraintHolds a →
          l.norm.eval a = some true)
    (hreason : ReasonSafeUniv problem constraintHolds props)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true)
    (hconfent : ∀ (st : State), st.conflict = none →
      RunInv problem constraintHolds props st →
      ∀ cc, (propagateLoop (engineFuel st) props st).conflict
          = some cc → cc ≠ [] →
        Clause.EntailedBy problem constraintHolds cc)
    (hleafng : ∀ (st : State), st.conflict = none →
      RunInv problem constraintHolds props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      ∀ a0, allSingleton
          (propagateLoop (engineFuel st) props st) = true →
        singletonAssignment
          (propagateLoop (engineFuel st) props st) = some a0 →
        ¬ (fitsB problem a0 &&
            problem.constraints.all (fun c => constraintHoldsB c a0)) →
        Clause.EntailedBy problem constraintHolds
          (List.map (fun e => e.literal.negate.norm)
            (List.filter (fun e => decide (e.level > 0))
              (propagateLoop (engineFuel st) props st).trail)))
    (hfallbackng : ∀ (st : State), st.conflict = none →
      RunInv problem constraintHolds props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      (propagateLoop (engineFuel st) props st).conflict = some [] →
      Clause.EntailedBy problem constraintHolds
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st) props st).trail))) :
    ∀ (fuel : Nat) (st : State),
      st.conflict = none →
      RunInv problem constraintHolds props st →
      Level0Solved problem constraintHolds st →
      TrailDistinct st.trail →
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
      UnsatEntryShape problem constraintHolds constraintHoldsB props := by
  intro fuel
  induction fuel with
  | zero =>
      intro st _ _ _ _ h
      simp only [lcgSearch.go, lcgSearchGo] at h
      cases h
  | succ fuel ih =>
      intro st hnone hinv hL0 hdist hunsat
      -- the propagated state's run invariant
      have hinv1 : RunInv problem constraintHolds props
          (propagateLoop (engineFuel st) props st) :=
        propagateLoop_runInv hreason hjust hdb (engineFuel st) st
          hnone hinv
      simp only [lcgSearch.go, lcgSearchGo] at hunsat
      split at hunsat
      · -- conflict at level 0: the terminal arm — the propagated
        -- state is the generating entry
        next hval hconf =>
          -- the pre-propagation entry st IS the generating entry:
          -- conflict-clear (hnone), level 0 (the propagated level 0
          -- transfers back through propagateLoop_decisionLevel),
          -- SolvedBy (Level0Solved at the level-0 entry), and the
          -- propagated state reports the conflict
          have hlevel0 : st.decisionLevel = 0 := by
            have hpl := propagateLoop_decisionLevel props
              (engineFuel st) st
            rw [← hpl]
            exact hconf
          exists st
          refine ⟨hlevel0, hnone,
            level0Solved_solvedBy hlevel0 hinv.rooted hinv.coherent hL0,
            hinv.coherent, hinv.clausesFixed, hinv.learnedEntailed, ?_⟩
          refine Or.inl ⟨?_, ?_⟩
          · simp only [Option.isSome_iff_exists]
            rw [show engineFuel st = 32 + 8 * st.domains.length
              + 4 * st.trail.length from rfl]
            exact ⟨_, hval⟩
          · -- SolvedBy of the propagated state: the clear-free
            -- variant of the representation theorem (the conflict
            -- verdict does not change the trail)
            have hclent : ∀ c ∈ st.clauses, ∀ a,
                ProblemSolution problem constraintHolds a →
                  ∃ l ∈ c, l.eval a = some true := by
              intro c hc a ha
              rw [hinv.clausesFixed] at hc
              exact hdb c hc a ha
            have hlnent : ∀ c ∈ st.learned, ∀ a,
                ProblemSolution problem constraintHolds a →
                  ∃ l ∈ c, l.eval a = some true := by
              intro c hc a ha
              have hmem : c ∈ (repairAfterBackjump problem 0
                  st).learned := hc
              have hsat : c.SatisfiedBy a :=
                (hL0 a ha).2.2.2 c hmem
              exact hsat
            exact propagateLoop_solvedBy_any hsafe hsolvable st.clauses
              st.learned hclent hlnent (engineFuel st) st hnone
              (level0Solved_solvedBy hlevel0 hinv.rooted hinv.coherent
                hL0) hinv.coherent rfl rfl
      · -- conflict above 0: the recursion arms
        rename_i w hw hpos
        -- the conflict witness (for the fallback premise's isSome)
        have hconfSome : (propagateLoop (engineFuel st) props
            st).conflict.isSome = true := by
          rw [show engineFuel st = 32 + 8 * st.domains.length
            + 4 * st.trail.length from rfl]
          exact hw ▸ rfl
        -- the propagated state's level-0 solved-ness (for the repair
        -- transfers below)
        have hL01 : Level0Solved problem constraintHolds
            (propagateLoop (engineFuel st) props st) := by
          have hpl := propagateLoop_decisionLevel props
            (engineFuel st) st
          cases hlv : (propagateLoop (engineFuel st) props
            st).decisionLevel with
          | zero =>
              -- level-0: the conflict-carrying SolvedBy transfer
              have hlevel0 : st.decisionLevel = 0 := by
                rw [← hpl]; exact hlv
              have hsolved0 : SolvedBy problem constraintHolds st :=
                level0Solved_solvedBy hlevel0 hinv.rooted hinv.coherent hL0
              have hclent : ∀ c ∈ st.clauses, ∀ a,
                  ProblemSolution problem constraintHolds a →
                    ∃ l ∈ c, l.eval a = some true := by
                intro c hc a ha
                rw [hinv.clausesFixed] at hc
                exact hdb c hc a ha
              have hlnent : ∀ c ∈ st.learned, ∀ a,
                  ProblemSolution problem constraintHolds a →
                    ∃ l ∈ c, l.eval a = some true := by
                intro c hc a ha
                have hmem : c ∈ (repairAfterBackjump problem 0
                    st).learned := hc
                exact (hL0 a ha).2.2.2 c hmem
              have hsolved1 : SolvedBy problem constraintHolds
                  (propagateLoop (engineFuel st) props st) :=
                propagateLoop_solvedBy_any hsafe hsolvable st.clauses
                  st.learned hclent hlnent (engineFuel st) st hnone
                  hsolved0 hinv.coherent rfl rfl
              -- the level-0 shape: all entries at level 0
              have hrooted1 : ∀ e ∈ (propagateLoop (engineFuel st)
                  props st).trail,
                  e.level ≤ (propagateLoop (engineFuel st)
                    props st).decisionLevel :=
                propagateLoop_rooted (engineFuel st) st
                  hinv.rooted
              -- the level-0 solved: at a level-0 state whose entries
              -- are all at level 0, Level0Solved ↔ SolvedBy (the
              -- projection is the state itself); prove the backward
              -- direction here from hsolved1
              intro a ha
              have hrep := hsolved1 a ha
              obtain ⟨hfit, htrail, hcl, hln⟩ := hrep
              refine ⟨?_, ?_, hcl, hln⟩
              · exact repair0_fits (problem := problem) ha.1
                  (fun e he _ => htrail e he)
              · intro e he
                -- the repair's trail IS the 0-filtered trail; all
                -- entries are at level 0 so the filter keeps
                -- everything and the trails coincide
                have hfil : List.filter (fun e =>
                    decide (e.level ≤ 0))
                    (propagateLoop (engineFuel st) props st).trail
                    = (propagateLoop (engineFuel st)
                      props st).trail := by
                  rw [List.filter_eq_self]
                  intro e2 he2
                  have hle : e2.level ≤ (propagateLoop
                      (engineFuel st) props st).decisionLevel :=
                    hrooted1 e2 he2
                  rw [hlv] at hle
                  simpa using hle
                have hmem : e ∈ (propagateLoop (engineFuel st)
                    props st).trail := by
                  have hfilt : e ∈ List.filter (fun e =>
                      decide (e.level ≤ 0))
                      (propagateLoop (engineFuel st) props st).trail := he
                  rw [hfil] at hfilt
                  exact hfilt
                exact htrail e hmem
          | succ n =>
              -- positive level: the level-0 subtrail is the entry's
              -- own (fresh enqueues at the current positive level)
              unfold Level0Solved at hL0 ⊢
              -- the whole projection records are EQUAL: both are
              -- built from the same kept trail (hkey), the same
              -- fold, and the same fields — rewrite the hypothesis
              -- hL0's projection into the goal's by hkey's
              -- congruence on the repair record
              have hrec : repairAfterBackjump problem 0
                  (propagateLoop (engineFuel st) props st)
                  = repairAfterBackjump problem 0 st := by
                unfold repairAfterBackjump
                rw [propagateLoop_filter0_pos (engineFuel st) st
                  (by rw [← hpl]; omega) hinv.rooted]
                -- the remaining fields: the propagated state's
                -- clauses/learned/queue are the entry's own (the
                -- loop never modifies them)
                rw [propagateLoop_clauses (engineFuel st) st,
                  propagateLoop_learned (engineFuel st) st,
                  propagateLoop_queue (engineFuel st) st]
              rw [hrec]
              exact hL0
        split at hunsat
        · -- the chronological fallback arm (analysis returned none):
          -- the match on the conflict clause decides learning; the
          -- some [] arm splits again on the pins gate
          rename_i _hscr heqnone
          split at hunsat
          · -- the conflict clause is some []: the learning gate is ON
            split at hunsat
            · -- the pins gate's TRUE branch: learn the nogood and
              -- retreat (the entitlement threads the hfallbackng
              -- premise, mirroring the leaf arm below)
              rename_i hconfnil hgate
              have hconfNil : (propagateLoop (engineFuel st) props
                  st).conflict = some [] := hconfnil
              have hgateEf : trailBoolPinsOk problem
                  (propagateLoop (engineFuel st) props st).trail
                  = true := hgate
              have hent := hfallbackng st hnone hinv hdist
                hgateEf hconfNil
              have hL01' : SolvedBy problem constraintHolds
                  (repairAfterBackjump problem 0
                    (propagateLoop (engineFuel st) props st)) := hL01
              -- P3b SECOND-MAX BACKJUMP + FLIP (engine change
              -- 2026-10-06): the arm retreats to the SECOND-highest
              -- falsifier level and — unconditionally when a
              -- max-level entry exists — enqueues that entry's
              -- negation with the nogood as reason (a branch-
              -- exclusion flip). The four IH obligations mirror
              -- a4_analyzed_entry; spell the engine's composite.
              -- The flipped state st2: the repair + learned nogood.
              -- Its RunInv: the learned gain is entitled (hent) and
              -- normalized (leafNogood_norm), then the repair's own
              -- transfers; its level is bjL ≤ the conflict level.
              have hdl1 : (propagateLoop (engineFuel st) props
                  st).decisionLevel =
                  (propagateLoop (engineFuel st) props
                    st).decisionLevel := rfl
              -- the nogood is the engine's ng
              let ng : Clause :=
                (((propagateLoop (engineFuel st) props
                    st).trail.filter
                      (fun e => decide (e.level > 0))).map
                        (fun e => e.literal.negate.norm))
              -- the positive-level entries (the flip's level source)
              let lvls : List TrailEntry :=
                ((propagateLoop (engineFuel st) props
                    st).trail.filter
                      (fun e => decide (e.level > 0)))
              -- the max/second-max levels and the found entry: case
              -- on the engine's find? directly (the engine's own
              -- match splits the recursion into the flip arm and
              -- the plain arm). The invariants hold at the repaired
              -- state for any level AT OR BELOW the propagated state's
              -- own level (the repair's filter only keeps entries at
              -- ≤ that level, and rootedness bounds them all) —
              -- state the auxiliary facts with the level-bound
              -- premise so the recursion can instantiate them at the
              -- engine's second-max level (which the engine's own
              -- fold bound guarantees is ≤ the propagated level —
              -- proved in hbnd below).
              have hbnd : lvls.foldl (fun acc e =>
                  if (e.level == lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0) = true
                    then acc else max acc e.level) 0 ≤
                  (propagateLoop (engineFuel st) props st).decisionLevel := by
                -- the second-max fold ≤ the max fold ≤ the level. The
                -- level bound: every positive-level entry's level is ≤
                -- the propagated state's decisionLevel (rootedness).
                have hrootedst1 : ∀ e ∈ (propagateLoop (engineFuel st)
                    props st).trail,
                    e.level ≤ (propagateLoop (engineFuel st) props
                      st).decisionLevel :=
                  propagateLoop_rooted (engineFuel st) st hinv.rooted
                have hmaxle : lvls.foldl
                      (fun acc e => max acc e.level) 0 ≤
                      (propagateLoop (engineFuel st) props st).decisionLevel := by
                    have hmain : ∀ (ls : List TrailEntry),
                        (∀ e ∈ ls, e.level ≤
                          (propagateLoop (engineFuel st) props
                            st).decisionLevel) →
                        ls.foldl (fun acc e => max acc e.level) 0 ≤
                          (propagateLoop (engineFuel st) props
                            st).decisionLevel := by
                          intro ls
                          induction ls with
                          | nil => intro _; simp [Nat.zero_le]
                          | cons e2 rest2 ih3 =>
                              intro hmem2
                              simp only [List.foldl_cons]
                              have hrest : rest2.foldl
                                  (fun acc e => max acc e.level) 0 ≤
                                  (propagateLoop (engineFuel st) props
                                    st).decisionLevel :=
                                ih3 (fun e3 he3 => hmem2 e3
                                  (List.mem_cons_of_mem _ he3))
                              have h1 : e2.level ≤
                                  (propagateLoop (engineFuel st) props
                                    st).decisionLevel :=
                                hmem2 e2 (List.mem_cons_self)
                              -- max (fold) e2.level ≤ level: the
                              -- cons-fold seeds with max 0 e2.level
                              -- (= e2.level, levels ≥ 0) and its value
                              -- IS max (rest2-fold) e2.level — bound
                              -- each part by the propagated level
                              show List.foldl
                                  (fun acc e => max acc e.level)
                                  (max 0 e2.level) rest2 ≤
                                (propagateLoop (engineFuel st) props
                                  st).decisionLevel
                              have hseed : max 0 e2.level = e2.level := by
                                have : (0 : Int) ≤ e2.level := by omega
                                simp [Nat.max_def, this]
                              rw [hseed]
                              -- the seeded fold ≤ level: every
                              -- accumulator step is a max with a
                              -- member level ≤ the propagated level,
                              -- so the fold's final value is too
                              have hgen2 : ∀ (seed : Nat)
                                  (ls : List TrailEntry),
                                  seed ≤
                                    (propagateLoop (engineFuel st) props
                                      st).decisionLevel →
                                  (∀ e3 ∈ ls, e3.level ≤
                                    (propagateLoop (engineFuel st) props
                                      st).decisionLevel) →
                                  ls.foldl (fun acc e => max acc e.level)
                                    seed ≤
                                    (propagateLoop (engineFuel st) props
                                      st).decisionLevel := by
                                intro seed ls
                                induction ls generalizing seed with
                                | nil => intro hs _; exact hs
                                | cons e3 rest3 ih4 =>
                                    intro hs hmem3
                                    simp only [List.foldl_cons]
                                    have h3i : e3.level ≤
                                        (propagateLoop (engineFuel st)
                                          props st).decisionLevel :=
                                      hmem3 e3 (List.mem_cons_self)
                                    have hs2 : max seed e3.level ≤
                                        (propagateLoop (engineFuel st)
                                          props st).decisionLevel :=
                                      Nat.max_le.mpr ⟨hs, h3i⟩
                                    show List.foldl
                                        (fun acc e => max acc e.level)
                                        (max seed e3.level) rest3 ≤
                                      (propagateLoop (engineFuel st)
                                        props st).decisionLevel
                                    exact ih4 (max seed e3.level) hs2
                                      (fun e4 he4 => hmem3 e4
                                        (List.mem_cons_of_mem _ he4))
                              exact hgen2 e2.level rest2 h1
                                (fun e4 he4 => hmem2 e4
                                  (List.mem_cons_of_mem _ he4))
                    exact hmain lvls
                      (fun e he => hrootedst1 e
                        ((List.mem_filter.mp he).1))
                -- the second-max fold is ≤ the max fold: every
                -- accumulator step either keeps the seed or takes an
                -- entry level, both ≤ the max fold's final value
                have h2le : lvls.foldl (fun acc e =>
                    if (e.level == lvls.foldl
                      (fun acc2 e2 => max acc2 e2.level) 0) = true
                      then acc else max acc e.level) 0 ≤
                    lvls.foldl (fun acc e => max acc e.level) 0 := by
                  have hgen : ∀ (ls : List TrailEntry) (mx : Nat),
                      ls.foldl (fun acc e =>
                        if (e.level == mx) = true then acc
                        else max acc e.level) 0 ≤
                        ls.foldl (fun acc e => max acc e.level) 0 := by
                        intro ls mx
                        induction ls with
                        | nil => exact Nat.le_refl _
                        | cons e2 rest2 ih3 =>
                            simp only [List.foldl_cons]
                            -- the second-max fold over the cons list:
                            --   foldl f' 0 (e2 :: rest2)
                            --    = foldl f' (f' 0 e2) rest2, where
                            --    f' 0 e2 = if (e2.level == mx) = true
                            --    then 0 else max 0 e2.level
                            -- SEED MONOTONICITY: a max-fold with a
                            -- smaller seed is ≤ one with a bigger seed
                            have hmono : ∀ (s1 s2 : Nat)
                                (ls : List TrailEntry),
                                s1 ≤ s2 →
                                List.foldl (fun acc e => max acc e.level)
                                  s1 ls ≤
                                List.foldl (fun acc e => max acc e.level)
                                  s2 ls := by
                              intro s1 s2 ls
                              induction ls generalizing s1 s2 with
                              | nil => intro h; exact h
                              | cons e3 rest3 ih4 =>
                                  intro hle
                                  simp only [List.foldl_cons]
                                  show List.foldl
                                      (fun acc e => max acc e.level)
                                      (max s1 e3.level) rest3 ≤
                                    List.foldl
                                      (fun acc e => max acc e.level)
                                      (max s2 e3.level) rest3
                                  exact ih4 (max s1 e3.level)
                                    (max s2 e3.level)
                                    (Nat.max_le.mpr
                                      ⟨Nat.le_trans hle
                                        (Nat.le_trans (Nat.le_refl s2)
                                          (Nat.le_max_left s2 e3.level)),
                                        Nat.le_max_right s2 e3.level⟩)
                            -- the cons list's max fold dominates its
                            -- members (needed below): unfold max and
                            -- split on the accumulator's two values;
                            -- keep the ∀-form for reuse in the arms
                            have hdom' : ∀ e3 ∈ (e2 :: rest2 : List
                                TrailEntry), e3.level ≤
                                List.foldl (fun acc e => max acc e.level)
                                  0 (e2 :: rest2) := by
                              intro e3 he3
                              -- the fold's value is ≥ every member's
                              -- level: the cons-fold's seed is
                              -- max 0 e2.level = e2.level (levels ≥ 0)
                              show e3.level ≤ List.foldl
                                  (fun acc e => max acc e.level)
                                  (max 0 e2.level) rest2
                              -- members of the cons list: e2 itself
                              -- (seed-dominated) or a rest2 member
                              -- (absorbed by the fold)
                              have hgen3 : ∀ (ls : List TrailEntry)
                                  (seed : Nat) (v : TrailEntry),
                                  seed ≤ v.level →
                                  v ∈ ls →
                                  List.foldl (fun acc e => max acc e.level)
                                    seed ls ≥ v.level := by
                                intro ls
                                induction ls with
                                | nil => intro seed v hv hvv; cases hvv
                                | cons e4 rest4 ih5 =>
                                    intro seed v hseed hv
                                    show List.foldl
                                        (fun acc e => max acc e.level)
                                        (max seed e4.level) rest4 ≥
                                      v.level
                                    rcases List.mem_cons.mp hv with hv3 | hv2
                                    · -- v = e4: a general fold-bound
                                      -- lemma — the fold is ≥ its
                                      -- own seed for any list
                                      rw [hv3] at hseed
                                      rw [hv3]
                                      have hbound : ∀ (ls2 : List
                                          TrailEntry) (s : Nat),
                                          List.foldl
                                            (fun acc e =>
                                              max acc e.level) s ls2 ≥
                                            s := by
                                        intro ls2
                                        induction ls2 with
                                        | nil => intro s; exact Nat.le_refl _
                                        | cons e5 rest5 ih6 =>
                                            intro s
                                            simp only [List.foldl_cons]
                                            have h6 := ih6
                                              (max s e5.level)
                                            have hgt : max s e5.level ≥ s :=
                                              Nat.le_max_left s e5.level
                                            omega
                                      -- goal: fold ≥ e4.level;
                                      -- hseed : seed ≤ e4.level
                                      have h2 := hbound rest4
                                        (max seed e4.level)
                                      have h3 : max seed e4.level ≥
                                          e4.level :=
                                        Nat.le_max_right seed e4.level
                                      omega
                                    · -- v ∈ rest4: the IH at the
                                      -- ORIGINAL seed — then lift
                                      -- with seed monotonicity
                                      have hmono : ∀ (ls2 : List
                                          TrailEntry) (s1 s2 : Nat),
                                          s1 ≤ s2 →
                                          List.foldl
                                            (fun acc e =>
                                              max acc e.level) s1 ls2 ≤
                                          List.foldl
                                            (fun acc e =>
                                              max acc e.level) s2 ls2 := by
                                        intro ls2
                                        induction ls2 with
                                        | nil => intro s1 s2 h; exact h
                                        | cons e5 rest5 ih6 =>
                                            intro s1 s2 hle
                                            simp only [List.foldl_cons]
                                            show List.foldl
                                                (fun acc e =>
                                                  max acc e.level)
                                                (max s1 e5.level) rest5 ≤
                                              List.foldl
                                                (fun acc e =>
                                                  max acc e.level)
                                                (max s2 e5.level) rest5
                                            exact ih6 (max s1 e5.level)
                                              (max s2 e5.level)
                                              (Nat.max_le.mpr
                                                ⟨Nat.le_trans hle
                                                  (Nat.le_trans
                                                    (Nat.le_refl s2)
                                                    (Nat.le_max_left s2
                                                      e5.level)),
                                                  Nat.le_max_right s2
                                                    e5.level⟩)
                                      have hstep : List.foldl
                                          (fun acc e =>
                                            max acc e.level) seed rest4 ≤
                                        List.foldl
                                          (fun acc e => max acc e.level)
                                          (max seed e4.level) rest4 :=
                                        hmono rest4 seed
                                          (max seed e4.level)
                                          (Nat.le_max_left seed e4.level)
                                      have hih : List.foldl
                                          (fun acc e =>
                                            max acc e.level) seed rest4 ≥
                                          v.level := ih5 seed v hseed hv2
                                      omega
                              -- members: e2 itself (the fold's
                              -- seed dominates) or a rest2 member
                              -- (hgen3 at seed max 0 e2.level)
                              -- ∀-member domination: the max fold
                              -- over the rest (any seed) absorbs
                              -- every rest member's level
                              have hdomrest : ∀ (ls2 : List TrailEntry)
                                  (s : Nat) (v : TrailEntry),
                                  v ∈ ls2 →
                                  List.foldl (fun acc e =>
                                    max acc e.level) s ls2 ≥ v.level := by
                                intro ls2
                                induction ls2 with
                                | nil => intro s v hv; cases hv
                                | cons e4 rest4 ih5 =>
                                    intro s v hv
                                    show List.foldl
                                        (fun acc e => max acc e.level)
                                        (max s e4.level) rest4 ≥ v.level
                                    rcases List.mem_cons.mp hv with hv3 | hv2
                                    · -- v = e4: the rest-fold is ≥ its
                                      -- seed, which is ≥ e4.level
                                      rw [hv3]
                                      have hge : ∀ (ls3 : List TrailEntry)
                                          (s2 : Nat),
                                          List.foldl (fun acc e =>
                                            max acc e.level) s2 ls3 ≥ s2 :=
                                        by
                                          intro ls3
                                          induction ls3 with
                                          | nil => intro s2; exact Nat.le_refl _
                                          | cons e5 rest5 ih6 =>
                                              intro s2
                                              simp only [List.foldl_cons]
                                              have h6 := ih6
                                                (max s2 e5.level)
                                              have hgt : s2 ≤ max s2 e5.level :=
                                                Nat.le_max_left s2 e5.level
                                              omega
                                      exact Nat.le_trans
                                        (Nat.le_max_right s e4.level)
                                        (hge rest4 (max s e4.level))
                                    · exact ih5 (max s e4.level) v hv2
                              rcases List.mem_cons.mp he3 with hv3 | hv3
                              · rw [hv3]
                                have hge : ∀ (ls3 : List TrailEntry)
                                    (s2 : Nat),
                                    List.foldl (fun acc e =>
                                      max acc e.level) s2 ls3 ≥ s2 := by
                                  intro ls3
                                  induction ls3 with
                                  | nil => intro s2; exact Nat.le_refl _
                                  | cons e5 rest5 ih6 =>
                                      intro s2
                                      simp only [List.foldl_cons]
                                      have h6 := ih6 (max s2 e5.level)
                                      have hgt : s2 ≤ max s2 e5.level :=
                                        Nat.le_max_left s2 e5.level
                                      omega
                                exact Nat.le_trans
                                  (Nat.le_max_right 0 e2.level)
                                  (hge rest2 (max 0 e2.level))
                              · have hseedv : max 0 e2.level = e2.level := by simp
                                rw [hseedv]
                                exact hdomrest rest2 e2.level e3 hv3
                            have hdom : List.foldl
                                (fun acc e => max acc e.level) 0
                                (e2 :: rest2) ≥ e2.level :=
                              hdom' e2 (List.mem_cons_self)
                            cases hbv : (e2.level == mx) with
                            | true =>
                                -- the seed collapses to 0: the rest
                                -- fold (≤ max fold over rest, ≤ max
                                -- fold over cons) closes. The goal's
                                -- seed collapses too (hbv already
                                -- reduced it); keep the engine's own
                                -- shapes and chain ih3 + hmono + hdom.
                                show List.foldl
                                    (fun acc e =>
                                      if (e.level == mx) = true then acc
                                      else max acc e.level)
                                    0 rest2 ≤
                                  List.foldl
                                    (fun acc e => max acc e.level)
                                    (max 0 e2.level) rest2
                                exact Nat.le_trans (ih3)
                                  (hmono 0 (max 0 e2.level) rest2
                                    (by simp))
                            | false =>
                                -- the seed is max 0 e2.level: the rest
                                -- fold grows to at most max(seed, e2)
                                -- ≤ the cons max fold. The goal is the
                                -- second-max fold over rest2 ≤ the max
                                -- fold over rest2: f' at each step is
                                -- either the accumulated second-max or
                                -- a member level — both bounded by the
                                -- max fold's accumulator (which absorbs
                                -- every member level). Generalize over
                                -- the seed pair.
                                have hgen2 : ∀ (ls : List TrailEntry)
                                    (acc1 acc2 : Nat),
                                    acc1 ≤ acc2 →
                                    ls.foldl (fun acc e =>
                                      if (e.level == mx) = true then acc
                                      else max acc e.level) acc1 ≤
                                    ls.foldl (fun acc e =>
                                      max acc e.level) acc2 := by
                                  intro ls
                                  induction ls with
                                  | nil => intro a1 a2 h; exact h
                                  | cons e3 rest3 ih4 =>
                                      intro a1 a2 hle
                                      simp only [List.foldl_cons]
                                      -- step: f' a1 e3 vs max a2 e3.level
                                      have hstep :
                                          (if (e3.level == mx) = true
                                              then a1
                                          else max a1 e3.level) ≤
                                        max a2 e3.level := by
                                        by_cases h3 :
                                            (e3.level == mx) = true
                                        · simp [h3]
                                          exact Nat.le_trans hle
                                            (Nat.le_max_left a2 e3.level)
                                        · simp [h3]
                                          omega
                                      show rest3.foldl (fun acc e =>
                                        if (e.level == mx) = true then acc
                                        else max acc e.level)
                                        ((if (e3.level == mx) = true then a1
                                          else max a1 e3.level)) ≤
                                        rest3.foldl (fun acc e =>
                                          max acc e.level)
                                        (max a2 e3.level)
                                      exact ih4 _ _ hstep
                                -- instantiate at the cons pair's seed:
                                -- f' 0 e2 = max 0 e2.level (hbv
                                -- false); the goal's RHS reduces to
                                -- the max fold at seed max 0 e2.level
                                -- (rfl), and hgen2 at equal seeds
                                -- closes it
                                show List.foldl (fun acc e =>
                                  if (e.level == mx) = true then acc
                                  else max acc e.level)
                                  (max 0 e2.level) rest2 ≤
                                List.foldl
                                  (fun acc e => max acc e.level)
                                  (max 0 e2.level) rest2
                                exact hgen2 rest2 (max 0 e2.level)
                                  (max 0 e2.level) (Nat.le_refl _)
                  exact hgen lvls
                    (lvls.foldl (fun acc2 e2 =>
                      max acc2 e2.level) 0)
                exact Nat.le_trans h2le hmaxle
              have hst2inv : ∀ (bjL : Nat), bjL ≤
                  (propagateLoop (engineFuel st) props st).decisionLevel →
                  RunInv problem constraintHolds props
                    (repairAfterBackjump problem bjL
                      {propagateLoop (engineFuel st) props st with
                       learned := ng :: (propagateLoop (engineFuel st)
                         props st).learned}) := by
                intro bjL hbjl
                refine repair_runInv
                  (runInv_cons_learned hinv1 hent
                    (leafNogood_norm _)) hbjl
              have hst2L0 : ∀ (bjL : Nat),
                  Level0Solved problem constraintHolds
                    (repairAfterBackjump problem bjL
                      {propagateLoop (engineFuel st) props st with
                       learned := ng :: (propagateLoop (engineFuel st)
                         props st).learned}) := by
                intro lvl
                show SolvedBy problem constraintHolds
                  (repairAfterBackjump problem 0
                    (repairAfterBackjump problem lvl
                      {propagateLoop (engineFuel st) props st with
                       learned := ng :: (propagateLoop (engineFuel st)
                         props st).learned}))
                rw [repair0_repair problem lvl]
                rw [repair0_learned_update problem
                  (propagateLoop (engineFuel st) props st) ng]
                exact solvedBy_cons_learned hL01' hent
              have hst2dist : ∀ (bjL : Nat),
                  TrailDistinct
                    (repairAfterBackjump problem bjL
                      {propagateLoop (engineFuel st) props st with
                       learned := ng :: (propagateLoop (engineFuel st)
                         props st).learned}).trail := by
                intro bjL
                exact repair_trailDistinct
                  (propagateLoop_trailDistinct (engineFuel st) st hdist)
              have hst2conf : ∀ (bjL : Nat),
                  (repairAfterBackjump problem bjL
                    {propagateLoop (engineFuel st) props st with
                     learned := ng :: (propagateLoop (engineFuel st)
                       props st).learned}).conflict = none :=
                fun bjL => repair_conflict problem _ _
              -- the flip's literal is a NOGOOD MEMBER: the found
              -- entry d is a positive-level st1-trail entry, so its
              -- negated norm is one of the nogood's mapped members
              have hdmem : ∀ (de : TrailEntry),
                  de ∈ (propagateLoop (engineFuel st) props st).trail →
                  decide (de.level > 0) = true →
                  de.literal.negate.norm ∈ ng := by
                intro de hemem hpos
                exact List.mem_map_of_mem
                  (List.mem_filter.mpr ⟨hemem, hpos⟩)
              -- the flip's opposing branch is excluded: a retained
              -- (level ≤ bjL) st1 entry carrying the flip literal's
              -- negation (= de's own literal, normalized) would be a
              -- second trail entry with de's literal, but de itself
              -- was DROPPED by the repair (its level is the max,
              -- strictly above the second-max bjL) — TrailDistinct
              -- refutes the duplicate
              have hnegflip : ∀ (bjL : Nat) (de : TrailEntry),
                  bjL < lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0 →
                  de ∈ (propagateLoop (engineFuel st) props st).trail →
                  de.level = lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0 →
                  (repairAfterBackjump problem bjL
                    {propagateLoop (engineFuel st) props st with
                     learned := ng :: (propagateLoop (engineFuel st)
                       props st).learned}).negOnTrail
                    de.literal.negate.norm = false := by
                intro bjL de hbj hdmem1 hdlvl
                -- the propagated trail is distinct
                have hdist1 : TrailDistinct
                    (propagateLoop (engineFuel st) props st).trail :=
                  propagateLoop_trailDistinct (engineFuel st) st hdist
                unfold State.negOnTrail repairAfterBackjump
                simp only
                cases hany : ((({propagateLoop (engineFuel st) props st with
                  learned := ng :: (propagateLoop (engineFuel st)
                    props st).learned} : State).trail).filter
                    (fun e => decide (e.level ≤ bjL))).any
                    (fun e => litEqB e.literal
                      de.literal.negate.norm.negate.norm) with
                | false => rfl
                | true =>
                    exfalso
                    rw [List.any_eq_true] at hany
                    obtain ⟨e, hemem, hbeq⟩ := hany
                    have helit : e.literal =
                        de.literal.negate.norm.negate.norm := by
                      simpa only [litEqB, decide_eq_true_eq] using hbeq
                    obtain ⟨hemem1, hele⟩ := List.mem_filter.mp hemem
                    have hele' : e.level ≤ bjL := of_decide_eq_true hele
                    -- the flip's negated-negated norm is de's own
                    -- (normalized) literal
                    have hdnn : de.literal.negate.norm.negate.norm
                        = de.literal := by
                      rw [norm_negate_norm (de.literal.negate),
                        Literal.negate_negate,
                        ← hinv1.trailNorm de hdmem1]
                    have hlit2 : de.literal = e.literal :=
                      (helit.trans hdnn).symm
                    have hdee : de.level = e.level := by
                      have := hdist1 de hdmem1 e hemem1 hlit2
                      rw [this]
                    omega
              split at hunsat
              · -- the flip arm: the found max-level entry's negation
                -- is enqueued (SOUNDNESS FIX: at bjL = 0 on a fresh
                -- decision level, at bjL > 0 on the repaired state)
                -- with the nogood as reason — the four IH obligations
                -- from the arm's assembly, mirroring a4's shape
                rename_i hde hdeeq
                -- the found entry's facts: membership and its level
                -- equation (from the find?)
                have hdemem : hde ∈ (propagateLoop (engineFuel st) props
                    st).trail := List.mem_of_find?_eq_some hdeeq
                have hdelv : hde.level = lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0 := by
                  have h9 := List.find?_some hdeeq
                  rw [beq_iff_eq] at h9
                  exact h9
                -- the max fold dominates every member's level (and
                -- its own seed): the standard fold-max bounds
                have hfge : ∀ (ls : List TrailEntry) (s : Nat),
                    s ≤ ls.foldl (fun acc e2 => max acc e2.level) s := by
                  intro ls
                  induction ls with
                  | nil => intro s; exact Nat.le_refl s
                  | cons e5 rest5 ih5 =>
                      intro s
                      simp only [List.foldl_cons]
                      exact Nat.le_trans (Nat.le_max_left s e5.level)
                        (ih5 (max s e5.level))
                -- the fold-max over the levels dominates every
                -- member's level: prove it by induction over the
                -- list, generalizing the seed (a bigger seed only
                -- grows the fold)
                have hdomlev : ∀ e ∈ lvls, e.level ≤
                    lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 := by
                  -- the direct induction: a member's level is absorbed
                  -- by the fold from ANY seed (seed-monotone max fold)
                  have hmem : ∀ (ls : List TrailEntry) (s : Nat)
                      (v : TrailEntry), v ∈ ls →
                      v.level ≤ ls.foldl
                        (fun acc2 e2 => max acc2 e2.level) s := by
                    intro ls
                    induction ls with
                    | nil => intro s v hv; cases hv
                    | cons hd5 rest5 ih5 =>
                        intro s v hv
                        simp only [List.foldl_cons]
                        rcases List.mem_cons.mp hv with hv1 | hv2
                        · have hveq : v = hd5 := by
                            cases hv1; rfl
                          rw [hveq]
                          exact Nat.le_trans (Nat.le_max_right s hd5.level)
                            (hfge rest5 (max s hd5.level))
                        · exact ih5 (max s hd5.level) v hv2
                  intro e he
                  exact hmem lvls 0 e he
                -- the max level is POSITIVE: otherwise lvls has no
                -- members (the fold dominates every member's level,
                -- and members have level > 0), so the nogood ng is
                -- the empty clause, whose entitlement (hent) refutes
                -- the existence of any internal solution — but
                -- hsolvable supplies one
                have hmaxpos : 0 < lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0 := by
                  by_cases hcon : 0 < lvls.foldl
                    (fun acc2 e2 => max acc2 e2.level) 0
                  · exact hcon
                  have hle : lvls.foldl
                      (fun acc2 e2 => max acc2 e2.level) 0 ≤ 0 := by omega
                  have hempty : lvls = [] := by
                    by_cases hne : lvls = []
                    · exact hne
                    exfalso
                    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil lvls hne
                    have h1 := hdomlev e he
                    have h2 : e.level > 0 :=
                      of_decide_eq_true (List.mem_filter.mp he).2
                    omega
                  have hngnil : ng = [] := by
                    have : (List.filter (fun e => decide (e.level > 0))
                        (propagateLoop (engineFuel st) props st).trail) = [] := hempty
                    show ng = []
                    unfold ng
                    rw [this]
                    rfl
                  obtain ⟨b, hb⟩ := hsolvable
                  have hsat : ng.SatisfiedBy b := hent b hb
                  rw [hngnil] at hsat
                  obtain ⟨w, hw, _⟩ := hsat
                  cases hw
                -- the strict bound: secondmax < maxL. Every second-max
                -- accumulator step either keeps the accumulator or
                -- takes a member level < maxL (≤ maxL and ≠ maxL);
                -- starting below maxL (0 < maxL), the fold stays
                -- below maxL
                have hstr : lvls.foldl (fun acc e =>
                    if (e.level == lvls.foldl (fun acc2 e2 =>
                      max acc2 e2.level) 0) = true then acc
                  else max acc e.level) 0 <
                  lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 := by
                  have hgen : ∀ (ls : List TrailEntry) (acc : Nat),
                      (∀ e ∈ ls, e.level ≤
                        lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0) →
                      acc < lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 →
                      ls.foldl (fun acc e =>
                        if (e.level == lvls.foldl (fun acc2 e2 =>
                          max acc2 e2.level) 0) = true then acc
                        else max acc e.level) acc <
                      lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 := by
                    intro ls
                    induction ls with
                    | nil => intro acc _ hlt; exact hlt
                    | cons e5 rest5 ih5 =>
                        intro acc hmem hlt
                        simp only [List.foldl_cons]
                        by_cases hc : (e5.level ==
                            lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0)
                            = true
                        · rw [if_pos hc]
                          exact ih5 acc
                            (fun e6 he6 => hmem e6 (List.mem_cons_of_mem _ he6))
                            hlt
                        · rw [if_neg hc]
                          have hne5 : e5.level ≠
                              lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 := by
                            intro heq
                            exact hc (beq_iff_eq.mpr heq)
                          have hlt5 : e5.level <
                              lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 := by
                            have h1 := hmem e5 (List.mem_cons_self)
                            omega
                          have hmax : max acc e5.level <
                              lvls.foldl (fun acc2 e2 => max acc2 e2.level) 0 :=
                            Nat.max_lt.mpr ⟨hlt, hlt5⟩
                          exact ih5 (max acc e5.level)
                            (fun e6 he6 => hmem e6 (List.mem_cons_of_mem _ he6))
                            hmax
                  exact hgen lvls 0 hdomlev hmaxpos
                -- the flip's literal is a NOGOOD MEMBER (hde's level
                -- is the positive max)
                have hdememng : hde.literal.negate.norm ∈ ng :=
                  hdmem hde hdemem (by
                    show decide (hde.level > 0) = true
                    rw [hdelv]
                    exact decide_eq_true hmaxpos)
                -- the flip's entry is at a POSITIVE decision level in
                -- BOTH engine arms: bjL > 0 (the repaired state's own
                -- level) or the bumped level 0 + 1 = 1 — this is the
                -- soundness fix's proof dividend: no root-fact
                -- obligation for the flip entry, and the level-0
                -- projection drops it
                let bj := lvls.foldl (fun acc e =>
                  if (e.level == lvls.foldl (fun acc2 e2 =>
                    max acc2 e2.level) 0) = true then acc
                  else max acc e.level) 0
                let st2 := repairAfterBackjump problem bj
                  {propagateLoop (engineFuel st) props st with
                    learned := ng :: (propagateLoop (engineFuel st) props st).learned}
                have hi : RunInv problem constraintHolds props st2 := hst2inv bj hbnd
                have hc : st2.conflict = none := hst2conf bj
                have hn : st2.negOnTrail hde.literal.negate.norm = false :=
                  hnegflip bj hde hstr hdemem hdelv
                have hd : TrailDistinct st2.trail := hst2dist bj
                have h0 : Level0Solved problem constraintHolds st2 := hst2L0 bj
                split at hunsat
                · -- A fresh level keeps the zero-backjump flip out
                  -- of root facts and the zero projection.
                  refine ih _ ?_ ?_ ?_ ?_ hunsat
                  · exact enqueueNorm_conflict_none_of_neg
                      (st := newDecisionLevel st2) hc hn
                  · exact enqueueNorm_runInv_pos
                      (newDecisionLevel_runInv hi)
                      (by show st2.decisionLevel + 1 ≠ 0; omega)
                      hent (leafNogood_norm _) hdememng
                  · unfold Level0Solved
                    rw [repair0_enqueue problem _ _ _ (by
                      show 0 < st2.decisionLevel + 1; omega)]
                    exact h0
                  · exact enqueueNorm_trailDistinct (st := newDecisionLevel st2) hd
                · -- A positive backjump already stamps the flip
                  -- above the root projection.
                  rename_i hbjzero
                  have hbjpos : 0 < bj := by
                    apply Nat.pos_of_ne_zero
                    intro hz
                    apply hbjzero
                    exact beq_iff_eq.mpr hz
                  refine ih _ ?_ ?_ ?_ ?_ hunsat
                  · exact enqueueNorm_conflict_none_of_neg hc hn
                  · exact enqueueNorm_runInv_pos hi
                      (by show bj ≠ 0; omega)
                      hent (leafNogood_norm _) hdememng
                  · unfold Level0Solved
                    rw [repair0_enqueue problem _ _ _ hbjpos]
                    exact h0
                  · exact enqueueNorm_trailDistinct hd
              · -- the plain arm: no max-level entry found — retreat
                refine ih _ (hst2conf _) (hst2inv _ ?_) (hst2L0 _)
                  (hst2dist _) hunsat
                · exact hbnd
            · -- the pins gate's FALSE branch: the plain retreat
              exact ih (repairAfterBackjump problem
                  ((propagateLoop (engineFuel st) props st).decisionLevel - 1)
                  (propagateLoop (engineFuel st) props st))
                (repair_conflict problem _ _)
                (repair_runInv hinv1 (by omega))
                (level0Solved_repair hL01)
                (repair_trailDistinct
                  (propagateLoop_trailDistinct (engineFuel st) st hdist))
                hunsat
          · -- the conflict clause is NOT some [] (a NONEMPTY
            -- unanalyzable conflict): the plain retreat — the
            -- fits-exclusion fails for scan-origin conflicts, so the
            -- engine never learns there; every invariant is
            -- preserved by the repair
            exact ih (repairAfterBackjump problem
                ((propagateLoop (engineFuel st) props st).decisionLevel - 1)
                (propagateLoop (engineFuel st) props st))
              (repair_conflict problem _ _)
              (repair_runInv hinv1 (by omega))
              (level0Solved_repair hL01)
              (repair_trailDistinct
                (propagateLoop_trailDistinct (engineFuel st) st hdist))
              hunsat
        · -- the analysis arm: the asserting enqueue's entry
          rename_i an heq
          -- the propagated state's WellFormed (for the level bound)
          have foldlen : ∀ (tr : List TrailEntry)
              (doms : List (List Value)),
              (tr.foldl (fun acc e =>
                domOfLit acc e.literal) doms).length
                = doms.length := by
            intro tr
            induction tr with
            | nil => intro _; rfl
            | cons e rest ih =>
                intro doms
                rw [List.foldl_cons, ih (domOfLit doms e.literal),
                  domOfLit_length e.literal]
          have hst1len : (propagateLoop (engineFuel st) props
              st).domains.length = problem.domains.length := by
            rw [hinv1.coherent, foldlen]
          have hstate1 : (propagateLoop (engineFuel st) props
              st).WellFormed problem constraintHolds :=
            ⟨hst1len, hinv1.rooted, hinv1.learnedEntailed⟩
          have hbl : an.backjumpLevel ≤ (propagateLoop (engineFuel st)
              props st).decisionLevel :=
            analyzeConflict_level hstate1 heq
          -- the repaired state's invariants
          have hinv2 : RunInv problem constraintHolds props
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st)) :=
            repair_runInv hinv1 hbl
          have hL02 : Level0Solved problem constraintHolds
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st)) :=
            level0Solved_repair hL01
          -- the norm-mapped learned clause is entailed (the
          -- analysis output's entailment survives normalization by
          -- Literal.norm_eval's witness transfer)
          -- AnalysisReady at the propagated state: reasons valid
          -- and normalized (RunInv), root facts (RunInv), and the
          -- conflict entitlement supplied by the front door's
          -- premise (hconfent shape — carried by hbelow's caller
          -- context via the conflict-entitlement chain)
          have hready1 : (propagateLoop (engineFuel st) props
              st).AnalysisReady problem constraintHolds := by
            refine ⟨?_, hinv1.reasonValid, hinv1.rootFacts,
              hinv1.reasonNorm⟩
            intro cc hcc
            cases hconf : (propagateLoop (engineFuel st) props
              st).conflict with
            | none => rw [hconf] at hcc; exact absurd hcc (by simp)
            | some c =>
                rw [hconf] at hcc
                have hccc : cc = c := by cases hcc; rfl
                rw [hccc]
                -- nonemptiness: an EMPTY conflict clause never
                -- analyzes (analyzeStep skips empty worklist clauses
                -- and nextPivot on no marks is none), so the analysis
                -- arm's own success heq forces c ≠ []
                have hcne : c ≠ [] := by
                  intro hempty
                  rw [hempty] at hconf
                  have hnone2 : analyzeConflict
                      (propagateLoop (engineFuel st) props st) = none :=
                    analyzeConflict_empty_none hconf
                  rw [show engineFuel st = 32 + 8 * st.domains.length
                    + 4 * st.trail.length from rfl] at hnone2
                  rw [hnone2] at heq
                  exact absurd heq (by simp)
                exact hconfent st hnone hinv c hconf hcne
          obtain ⟨hent, _, _⟩ :=
            analyzeConflict_correct (problem := problem)
              (constraintHolds := constraintHolds) hstate1
              hready1
              (by rw [show engineFuel st = 32 + 8 * st.domains.length
                + 4 * st.trail.length from rfl]; exact heq)
          have hentN : Clause.EntailedBy problem constraintHolds
              (an.learned.map (fun l => l.norm)) := by
            intro a ha
            obtain ⟨w, hw, hev⟩ := hent a ha
            refine ⟨w.norm, ?_, ?_⟩
            · exact List.mem_map_of_mem (f := fun l => l.norm) hw
            · rw [Literal.norm_eval w a]
              exact hev
          -- the enqueue's fresh-entry obligations: the reason's
          -- clause (the normalized learned clause) is normalized
          -- (double-norm) and valid (entailed + the asserting
          -- literal is a member — the learned clause's head)
          have hnormr : ∀ q ∈ (an.learned.map
              (fun l => l.norm)), q = q.norm := by
            intro q hq
            obtain ⟨w, hw, hq2⟩ := List.mem_map.mp hq
            rw [← hq2, norm_norm w]
          -- the composite entry's three invariants, then the IH.
          have hst2none : (repairAfterBackjump problem an.backjumpLevel
              (propagateLoop (engineFuel st) props st)).conflict
              = none := repair_conflict problem _ _
          have hst2inv : RunInv problem constraintHolds props
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st)) :=
            repair_runInv hinv1 hbl
          have hst2L0 : Level0Solved problem constraintHolds
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st)) :=
            level0Solved_repair hL01
          have hst2lvl : (repairAfterBackjump problem an.backjumpLevel
              (propagateLoop (engineFuel st) props st)).decisionLevel
              = an.backjumpLevel := repair_decisionLevel problem _ _
          -- the composite record's learned gain is entitled:
          -- hentN at the head, st2's own below
          have hlearn3 : ∀ c ∈ ((an.learned.map (fun l => l.norm)) ::
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st)).learned :
                List Clause),
              Clause.EntailedBy problem constraintHolds c := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc2
            · exact hentN
            · exact hst2inv.learnedEntailed c hc2
          -- the fresh-entry reason obligations: the reason's clause
          -- is lnt (entailed, normalized)
          have hfreshN : ∀ r ∈ (some (Reason.mk
              (an.learned.map (fun l => l.norm))) : Option Reason),
              ∀ q ∈ r.clause, q = q.norm := by
            intro r hrmem q hq
            cases hrmem
            exact hnormr q hq
          have hpiv : an.asserting.norm ∈ an.learned.map
              (fun l => l.norm) := analyzeHead_mem heq
          have hfreshV : ∀ r ∈ (some (Reason.mk
              (an.learned.map (fun l => l.norm))) : Option Reason),
              Reason.Valid problem constraintHolds r an.asserting.norm := by
            intro r hrmem
            cases hrmem
            exact ⟨hentN, by simpa using hpiv⟩
          -- the recursive entry: the composite record {st2 with
          -- learned := lnt :: st2.learned} enqueued with
          -- an.asserting — apply the IH with the three invariants
          -- assembled from the field lemmas. CONFLICT-CLEAR: the
          -- enqueue from the conflict-free repaired state keeps
          -- the slot clear in the skip and fresh arms; the opposing
          -- arm is excluded by the learned clause's justification
          -- (enqueueNorm_no_opposing at the solutions the branch
          -- still represents). RunInv: the field lemmas transfer
          -- with the learned gain (hlearn3) and the reason
          -- obligations (hfreshN/hfreshV). Level0Solved: at
          -- positive backjump levels the fresh entry is above 0
          -- (dropped by the 0-filter — enqueueNorm at the repaired
          -- level); at level 0 the asserting literal is justified
          -- (hbelow + asserting_true_at_solutions), so
          -- enqueueNorm_solvedBy preserves the representation.
          -- A4's honest transfer: the composite entry's four
          -- premises from a4_analyzed_entry (the opposing branch
          -- refuted in both backjump shapes), then the IH.
          obtain ⟨cc0, hconf1⟩ : ∃ c, (propagateLoop (engineFuel st)
              props st).conflict = some c := by
            rw [show engineFuel st = 32 + 8 * st.domains.length
              + 4 * st.trail.length from rfl] at ⊢
            unfold analyzeConflict at heq
            cases hconf : (propagateLoop (32 + 8 * st.domains.length
              + 4 * st.trail.length) props st).conflict with
            | none => rw [hconf] at heq; exact absurd heq (by simp)
            | some c => exact ⟨c, rfl⟩
          have hstrict : an.backjumpLevel < (propagateLoop
              (engineFuel st) props st).decisionLevel := by
            have hdisj := (analyzeConflict_correct (problem := problem)
              (constraintHolds := constraintHolds) hstate1 hready1
              heq).2.2
            rcases hdisj with hzero | hlt
            · exact absurd hzero hpos
            · exact hlt
          obtain ⟨hconflict4, hinv4, hL04, hdist4⟩ :=
            a4_analyzed_entry
              (problem := problem)
              (constraintHolds := constraintHolds)
              (props := props)
              (st1 := propagateLoop (engineFuel st) props st)
              (an := an) (cc0 := cc0)
              hsolvable hinv1
              (propagateLoop_trailDistinct (engineFuel st) st hdist)
              hconf1 heq hentN hstrict hL01
              (repairAfterBackjump problem an.backjumpLevel
                (propagateLoop (engineFuel st) props st))
              ({ repairAfterBackjump problem an.backjumpLevel
                  (propagateLoop (engineFuel st) props st) with
                 learned := (an.learned.map (fun l => l.norm)) ::
                   (repairAfterBackjump problem an.backjumpLevel
                     (propagateLoop (engineFuel st) props st)).learned })
              (an.learned.map (fun l => l.norm)) rfl rfl rfl
          exact ih _ hconflict4 hinv4 hL04 hdist4 hunsat
      · -- no conflict: leaf or decision
        rename_i hconfnone
        split at hunsat
        · -- allSingleton: leaf
          rename_i hsingle
          split at hunsat
          · -- singletonAssignment some
            split at hunsat
            · -- leaf check passed: sat — contradicts unsat
              cases hunsat
            · -- leaf failed
              split at hunsat
              · -- at level 0: the terminal leaf arm — the propagated
                -- state IS the generating entry
                rename_i a0 hassign hfail hlevel0
                -- st is at level 0 (the level transfers back)
                have hst0 : st.decisionLevel = 0 := by
                  have hpl := propagateLoop_decisionLevel props
                    (engineFuel st) st
                  rw [← hpl]
                  have hef : engineFuel st
                      = 32 + 8 * st.domains.length
                        + 4 * st.trail.length := rfl
                  have hlv0 : (propagateLoop (engineFuel st)
                      props st).decisionLevel = 0 := by
                    rw [hef]
                    simpa using hlevel0
                  exact hlv0
                exists st
                refine ⟨hst0, hnone,
                  level0Solved_solvedBy hst0
                    hinv.rooted hinv.coherent hL0,
                  hinv.coherent, hinv.clausesFixed,
                  hinv.learnedEntailed, ?_⟩
                refine Or.inr ⟨hconfnone, hsingle, a0, hassign, ?_⟩
                -- the failed leaf test at the propagated state:
                -- the goal is literally the split hypothesis's type
                -- (both come from the engine's leaf-test `if` at the
                -- same propagated state and witness `a0`)
                exact hfail
              · -- above 0: the chronological retreat recursion
                -- (now with leaf-nogood learning: the engine inserts
                -- the failed leaf's nogood into the learned DB)
                rename_i a0 hassign hfail hne0
                -- the propagated state's Level0Solved (conflict-
                -- clear case): the level-split proof is arm-
                -- independent (`propagateLoop_solvedBy_any` never
                -- consults the conflict verdict)
                have hL01 : Level0Solved problem constraintHolds
                    (propagateLoop (engineFuel st) props st) := by
                  have hpl := propagateLoop_decisionLevel props
                    (engineFuel st) st
                  cases hlv : (propagateLoop (engineFuel st) props
                    st).decisionLevel with
                  | zero =>
                      have hlevel0 : st.decisionLevel = 0 := by
                        rw [← hpl]; exact hlv
                      have hsolved0 : SolvedBy problem constraintHolds st :=
                        level0Solved_solvedBy hlevel0 hinv.rooted
                          hinv.coherent hL0
                      have hclent : ∀ c ∈ st.clauses, ∀ a,
                          ProblemSolution problem constraintHolds a →
                            ∃ l ∈ c, l.eval a = some true := by
                        intro c hc a ha
                        rw [hinv.clausesFixed] at hc
                        exact hdb c hc a ha
                      have hlnent : ∀ c ∈ st.learned, ∀ a,
                          ProblemSolution problem constraintHolds a →
                            ∃ l ∈ c, l.eval a = some true := by
                        intro c hc a ha
                        have hmem : c ∈ (repairAfterBackjump problem 0
                            st).learned := hc
                        exact (hL0 a ha).2.2.2 c hmem
                      have hsolved1 : SolvedBy problem constraintHolds
                          (propagateLoop (engineFuel st) props st) :=
                        propagateLoop_solvedBy_any hsafe hsolvable
                          st.clauses st.learned hclent hlnent
                          (engineFuel st) st hnone hsolved0
                          hinv.coherent rfl rfl
                      have hrooted1 : ∀ e ∈ (propagateLoop
                          (engineFuel st) props st).trail,
                          e.level ≤ (propagateLoop (engineFuel st)
                            props st).decisionLevel :=
                        propagateLoop_rooted (engineFuel st) st
                          hinv.rooted
                      intro a ha
                      have hrep := hsolved1 a ha
                      obtain ⟨hfit, htrail, hcl, hln⟩ := hrep
                      refine ⟨?_, ?_, hcl, hln⟩
                      · exact repair0_fits (problem := problem) ha.1
                          (fun e he _ => htrail e he)
                      · intro e he
                        have hfil : List.filter (fun e =>
                            decide (e.level ≤ 0))
                            (propagateLoop (engineFuel st) props st).trail
                            = (propagateLoop (engineFuel st)
                              props st).trail := by
                          rw [List.filter_eq_self]
                          intro e2 he2
                          have hle : e2.level ≤ (propagateLoop
                              (engineFuel st) props st).decisionLevel :=
                            hrooted1 e2 he2
                          rw [hlv] at hle
                          simpa using hle
                        have hmem : e ∈ (propagateLoop (engineFuel st)
                            props st).trail := by
                          have hfilt : e ∈ List.filter (fun e =>
                              decide (e.level ≤ 0))
                              (propagateLoop (engineFuel st) props
                                st).trail := he
                          rw [hfil] at hfilt
                          exact hfilt
                        exact htrail e hmem
                  | succ n =>
                      unfold Level0Solved at hL0 ⊢
                      have hrec : repairAfterBackjump problem 0
                          (propagateLoop (engineFuel st) props st)
                          = repairAfterBackjump problem 0 st := by
                        unfold repairAfterBackjump
                        rw [propagateLoop_filter0_pos (engineFuel st) st
                          (by rw [← hpl]; omega) hinv.rooted]
                        rw [propagateLoop_clauses (engineFuel st) st,
                          propagateLoop_learned (engineFuel st) st,
                          propagateLoop_queue (engineFuel st) st]
                      rw [hrec]
                      exact hL0
                -- the engine's new leaf-nogood learning (gated on
                -- trailBoolPinsOk; the plain retreat is the fallback)
                cases hgate : trailBoolPinsOk problem
                  (propagateLoop (engineFuel st) props st).trail with
                | false =>
                    -- the plain retreat (the pre-leaf-ng engine arm)
                    rw [show engineFuel st = 32 + 8 * st.domains.length
                      + 4 * st.trail.length from rfl] at hgate
                    rw [if_neg (by simp [hgate])] at hunsat
                    exact ih (repairAfterBackjump problem
                        ((propagateLoop (engineFuel st) props
                          st).decisionLevel - 1)
                        (propagateLoop (engineFuel st) props st))
                      (repair_conflict problem _ _)
                      (repair_runInv hinv1 (by omega))
                      (level0Solved_repair hL01)
                      (repair_trailDistinct
                        (propagateLoop_trailDistinct (engineFuel st) st hdist))
                      hunsat
                | true =>
                  rw [show engineFuel st = 32 + 8 * st.domains.length
                    + 4 * st.trail.length from rfl] at hgate
                  rw [if_pos hgate] at hunsat
                  have hent := hleafng st hnone hinv hdist hgate a0
                    hsingle hassign hfail
                  have hL01' : SolvedBy problem constraintHolds
                      (repairAfterBackjump problem 0
                        (propagateLoop (engineFuel st) props st)) := hL01
                  -- the retreat entry, spelled exactly as the engine
                  -- (structure eta: the let-form and the record-update
                  -- form are definitionally equal, so the IH applies)
                  exact ih (repairAfterBackjump problem
                      ((propagateLoop (engineFuel st) props
                        st).decisionLevel - 1)
                      {propagateLoop (engineFuel st) props st with
                       learned := (((propagateLoop (engineFuel st)
                          props st).trail.filter
                            (fun e => decide (e.level > 0))).map
                              (fun e => e.literal.negate.norm)) ::
                        (propagateLoop (engineFuel st) props st).learned})
                    (repair_conflict problem _ _)
                    (repair_runInv
                      (runInv_cons_learned hinv1 hent
                        (leafNogood_norm _))
                      (Nat.le_trans (Nat.sub_le _ _)
                        (Nat.le_of_eq rfl)))
                    (by
                      unfold Level0Solved
                      rw [repair0_repair]
                      show SolvedBy problem constraintHolds
                        (repairAfterBackjump problem 0
                          {propagateLoop (engineFuel st) props st with
                           learned := (((propagateLoop (engineFuel st)
                              props st).trail.filter
                                (fun e => decide (e.level > 0))).map
                                  (fun e => e.literal.negate.norm)) ::
                            (propagateLoop (engineFuel st) props st).learned})
                      have hrec2 : repairAfterBackjump problem 0
                          {propagateLoop (engineFuel st) props st with
                           learned := (((propagateLoop (engineFuel st)
                              props st).trail.filter
                                (fun e => decide (e.level > 0))).map
                                  (fun e => e.literal.negate.norm)) ::
                            (propagateLoop (engineFuel st) props st).learned}
                        = {repairAfterBackjump problem 0
                            (propagateLoop (engineFuel st) props st) with
                           learned := (((propagateLoop (engineFuel st)
                              props st).trail.filter
                                (fun e => decide (e.level > 0))).map
                                  (fun e => e.literal.negate.norm)) ::
                            (repairAfterBackjump problem 0
                              (propagateLoop (engineFuel st)
                                props st)).learned} := rfl
                      rw [hrec2]
                      exact solvedBy_cons_learned hL01' hent)
                    (repair_trailDistinct
                      (propagateLoop_trailDistinct (engineFuel st) st hdist))
                    hunsat
          · -- singletonAssignment none: unknown — contradicts unsat
            cases hunsat
        · -- not allSingleton: decide or unknown
          split at hunsat
          · -- decideLiteral none: unknown — contradicts unsat
            cases hunsat
          · -- the decision arm: the fresh entry is above level 0;
            -- the level-0 projection is untouched
            rename_i hl hlq
            have hdecL0 : Level0Solved problem constraintHolds
                (enqueueNorm (newDecisionLevel
                  (propagateLoop (engineFuel st) props st)) hl
                  none) :=
              level0Solved_decision
                (a2_propagated_level0Solved hsafe hsolvable hdb st
                  hnone hinv hL0)
            have hconfdec : (enqueueNorm (newDecisionLevel
                (propagateLoop (engineFuel st) props st)) hl
                none).conflict = none :=
              a2_decided_conflict_none hconfnone hinv1.coherent hlq
            have hinvdec : RunInv problem constraintHolds props
                (enqueueNorm (newDecisionLevel
                  (propagateLoop (engineFuel st) props st)) hl
                  none) :=
              a2_decided_runInv hinv1 hlq
            exact ih (enqueueNorm (newDecisionLevel
                (propagateLoop (engineFuel st) props st)) hl none)
              hconfdec hinvdec hdecL0
              (enqueueNorm_trailDistinct
                (propagateLoop_trailDistinct (engineFuel st) st hdist))
              hunsat

end LeanFzn.Solver.Propagation
#print axioms LeanFzn.Solver.Propagation.go_unsat_entry_invariant
#print axioms LeanFzn.Solver.Propagation.a4_analyzed_entry
