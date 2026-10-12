/-
File: LeanFzn/Solver/Propagation/AnalysisEventsCore.lean

Purpose:
  O1 — REAL analyzer event accounting (the analyzer-level core).
  This module sits BELOW the scheduler consumers (SchedulerStep imports
  it for `analyzeEventsExpansions`); the composed-phase accumulation and
  the path composition lemma live in `LeanFzn/Solver/UIP/AnalysisEvents.lean`,
  which imports this file plus `Proofs.Scheduler`.

  B1's `analyzeTrace` (`AnalysisCompletion.lean`) counts the analyzer's
  transitions but does not say WHICH operation each one performed: a pivot
  reason-EXPANSION, a worklist literal (or empty clause) SCAN, and the
  current-level MARK that the scan's `markLit` records are all "1 step".
  This module separates them on the analyzer that actually runs:

  * `IsExpansion` / `IsScan` — the exact characterisation of the two
    continuing arms of the real `analyzeNext` (empty worklist + selected
    pivot + seeded reason vs. dropped-empty-clause / skipped-pivot /
    scanned-literal). `next_iff_expansion_or_scan` proves that every
    `AnalyzerStep.next` of `analyzeNext` is exactly one of the two, and
    `isExpansion_iff_work_nil_of_next` reads the expansion condition off
    the executed transition: an expansion is EXACTLY a transition that
    continues from an empty worklist.
  * `stepCounts` — the event contribution of ONE executed transition:
    `1` expansion, or `1` scan plus the current-level marks the scan added
    (`st'.marks.length - st.marks.length`), so marks are counted separately
    from scans. `stepCounts_expansions_eq_one_iff` ties the expansion
    counter to `IsExpansion` (not to a re-implementation of the arm).
  * `analyzeEvents` — the executed run with the event counts accumulated
    from the transitions actually taken, plus the exactness theorems:
    `analyzeEvents_trace_of_events` (a completed counted run stops exactly
    where `analyzeTrace` does, `expansions + scans + 1 = k`) — an exact
    decomposition, not the mere fuel bound `analyzeEvents_steps_le_fuel`
    (kept only as a counterpoint); and `analyzeEvents_of_trace` /
    `analyzeEvents_complete_of_reachable` (on B1's reachable class the
    counted run COMPLETES, so the counts are those of a semantic stop).
  * `analyzeEvents_result_eq_analyzeAtAllowance` — the counted run's result
    IS the result of the executable allowance entry point.
  * a completed multi-resolution fixture with concretely derived counts
    (one reason expansion, nine scans, two marks, eleven trace steps).

  The counter `expansions` is the number C3 wires into
  `RuntimeEvents.reasonResolutions` at the `analyzeConflict` site. The
  vocabulary (`expansions`, `scans`, `marks`) matches C1's record; the
  record itself is NOT imported — this module deliberately sits BELOW the
  consumers in the import DAG.

Dependencies:
  - LeanFzn.Solver.Propagation.AnalysisCompletion: `analyzeNext`, `analyzeTrace`,
    `analyzeLoop`, `initAnalysisState`, `AnalyzerReachable`,
    `analysis_complete_of_reachable`.

DAG (import list, proving the DAG constraint):
  `LeanFzn.Solver.Propagation.AnalysisCompletion` ONLY — no `SchedulerState`, no `Pruned`,
  no `Scheduler*`.  AnalysisCompletion -> LeanFzn.Solver.UIP.AnalysisEventsCore
  -> (SchedulerStep, LeanFzn.Solver.UIP.AnalysisEvents) -> consumers.
-/

import LeanFzn.Solver.Propagation.AnalysisCompletion
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The event vocabulary

`expansions` mirrors the pivot-expansion count C3 records into
`RuntimeEvents.reasonResolutions`; `scans` and `marks` are the fine-grained
operations B1's single step count conflates. -/

/-- The event counts of an analysis run. They are accumulated per executed
transition, never bounded by a fuel constant. -/
structure EventCounts where
  /-- reason expansions: the worklist was empty, a pivot was selected and
  its reason clause was seeded -/
  expansions : Nat := 0
  /-- scans: a worklist literal (or an already-empty clause) was consumed -/
  scans : Nat := 0
  /-- current-level marks recorded by `markLit` inside the executed scans -/
  marks : Nat := 0
  deriving DecidableEq, Repr, BEq

/-- Accumulate two runs' counts. -/
def EventCounts.add (a b : EventCounts) : EventCounts where
  expansions := a.expansions + b.expansions
  scans := a.scans + b.scans
  marks := a.marks + b.marks

@[simp] theorem EventCounts.add_expansions (a b : EventCounts) :
    (a.add b).expansions = a.expansions + b.expansions := rfl

@[simp] theorem EventCounts.add_scans (a b : EventCounts) :
    (a.add b).scans = a.scans + b.scans := rfl

@[simp] theorem EventCounts.add_marks (a b : EventCounts) :
    (a.add b).marks = a.marks + b.marks := rfl

/-! ## The exact characterisation of the transition kinds

`analyzeNext` continues in exactly two ways: a REASON EXPANSION (empty
worklist, a pivot entry whose marks survive the filter, a reason clause
seeded with the pivot as the skip) or a SCAN (a dropped already-empty
clause, a literal equal to the skip, or a literal handed to `markLit`).
These definitions name the states the real arms produce, they do not
re-implement the decision. -/

/-- The exact transition shape of the reason-expansion arm of `analyzeNext`:
the worklist is empty; `nextPivot` selects `e`; the pivot's marks survive
the filter (so the arm does not stop); `e` has a reason whose clause is
seeded as the new (single-clause) worklist with `e.literal` as the skip,
and the pivot is removed from the marks. -/
def IsExpansion (trail : List TrailEntry) (_lvl : Nat)
    (st st' : AnalyzerState) : Prop :=
  ∃ e : TrailEntry,
    st.work = [] ∧
    nextPivot trail st.marks = some e ∧
    (st.marks.filter (fun m => !litEqB m.literal e.literal)).isEmpty = false ∧
    ∃ r : Reason,
      e.reason = some r ∧
      st' = { work := [r.clause], skip := some e.literal,
              marks := (st.marks.filter fun m => !litEqB m.literal e.literal),
              learnt := st.learnt }

/-- The exact transition shapes of the three continuing SCAN arms of
`analyzeNext`: the dropped already-empty clause, the skipped pivot literal,
and the scanned literal whose `markLit` result becomes the new marks and
learnt lists. -/
def IsScan (trail : List TrailEntry) (lvl : Nat)
    (st st' : AnalyzerState) : Prop :=
  (∃ cs : List Clause,
      st.work = [] :: cs ∧
      st' = { work := cs, skip := st.skip, marks := st.marks,
              learnt := st.learnt }) ∨
  (∃ (q : Literal) (qs : Clause) (cs : List Clause),
      st.work = (q :: qs) :: cs ∧
      skipEq st.skip q.norm = true ∧
      st' = { work := qs :: cs, skip := st.skip, marks := st.marks,
              learnt := st.learnt }) ∨
  (∃ (q : Literal) (qs : Clause) (cs : List Clause)
     (marks' : List TrailEntry) (learnt' : List (Literal × Nat)),
      st.work = (q :: qs) :: cs ∧
      skipEq st.skip q.norm = false ∧
      markLit trail lvl st.marks st.learnt q.norm = some (marks', learnt') ∧
      st' = { work := qs :: cs, skip := st.skip, marks := marks',
              learnt := learnt' })

/-- A scan consumes a worklist item, so its state has a nonempty worklist. -/
theorem isScan_work_ne_nil {trail : List TrailEntry} {lvl : Nat}
    {st st' : AnalyzerState} (h : IsScan trail lvl st st') : st.work ≠ [] := by
  rcases h with ⟨cs, hw, -⟩ | ⟨q, qs, cs, hw, -⟩
    | ⟨q, qs, cs, marks', learnt', hw, -, -, -⟩
  · simp [hw]
  · simp [hw]
  · simp [hw]

/-- Every continuing transition of the REAL `analyzeNext` is an expansion
or a scan. -/
theorem expansion_or_scan_of_next (trail : List TrailEntry) (lvl : Nat)
    {st st' : AnalyzerState}
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    IsExpansion trail lvl st st' ∨ IsScan trail lvl st st' := by
  unfold IsExpansion IsScan
  obtain ⟨work, skip, marks, learnt⟩ := st
  cases work with
  | nil =>
      simp only [analyzeNext] at h
      cases hp : nextPivot trail marks with
      | none => simp [hp] at h
      | some e =>
          by_cases hq : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty = true
          · simp [hp, hq] at h
          · have hq' : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty
                = false := by
              cases hb : (marks.filter fun m => !litEqB m.literal e.literal).isEmpty
              · rfl
              · exact absurd hb hq
            cases hr : e.reason with
            | none => simp [hp, hq, hr] at h
            | some r =>
                simp only [hp, hq, hr] at h
                injection h with hst
                exact Or.inl ⟨e, rfl, rfl, hq', r, hr, hst.symm⟩
  | cons c cs =>
      cases c with
      | nil =>
          simp only [analyzeNext] at h
          injection h with hst
          exact Or.inr (Or.inl ⟨cs, rfl, hst.symm⟩)
      | cons q qs =>
          by_cases hs : skipEq skip q.norm = true
          · simp only [analyzeNext, hs] at h
            injection h with hst
            exact Or.inr (Or.inr (Or.inl ⟨q, qs, cs, rfl, hs, hst.symm⟩))
          · have hs' : skipEq skip q.norm = false := by
              cases hb : skipEq skip q.norm
              · rfl
              · exact absurd hb hs
            cases hm : markLit trail lvl marks learnt q.norm with
            | none => simp [analyzeNext, hs, hm] at h
            | some mp =>
                obtain ⟨marks', learnt'⟩ := mp
                simp [analyzeNext, hs, hm] at h
                exact Or.inr (Or.inr (Or.inr
                  ⟨q, qs, cs, marks', learnt', rfl, hs', hm, h.symm⟩))

/-- Conversely, every expansion or scan shape IS the transition the real
`analyzeNext` takes. -/
theorem next_of_expansion_or_scan (trail : List TrailEntry) (lvl : Nat)
    {st st' : AnalyzerState}
    (h : IsExpansion trail lvl st st' ∨ IsScan trail lvl st st') :
    analyzeNext trail lvl st = AnalyzerStep.next st' := by
  rcases h with ⟨e, hw, hp, hne, r, hr, hst⟩ | hscan
  · rw [hst]
    simp [analyzeNext, hw, hp, hr, hne]
  · rcases hscan with ⟨cs, hw, hst⟩ | ⟨q, qs, cs, hw, hs, hst⟩
      | ⟨q, qs, cs, marks', learnt', hw, hs, hm, hst⟩
    · rw [hst]
      simp [analyzeNext, hw]
    · rw [hst]
      simp [analyzeNext, hw, hs]
    · rw [hst]
      simp [analyzeNext, hw, hs, hm]

/-- THE CHARACTERISATION: the continuing transitions of the real
`analyzeNext` are EXACTLY the reason expansions plus the scans. -/
theorem next_iff_expansion_or_scan (trail : List TrailEntry) (lvl : Nat)
    (st st' : AnalyzerState) :
    analyzeNext trail lvl st = AnalyzerStep.next st' ↔
      IsExpansion trail lvl st st' ∨ IsScan trail lvl st st' :=
  ⟨fun h => expansion_or_scan_of_next trail lvl h,
   fun h => next_of_expansion_or_scan trail lvl h⟩

/-- Read off the executed transition: a continuing transition is an
expansion EXACTLY when its worklist is empty (and then it is the
reason-seeding arm). -/
theorem isExpansion_iff_work_nil_of_next (trail : List TrailEntry) (lvl : Nat)
    {st st' : AnalyzerState}
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    IsExpansion trail lvl st st' ↔ st.work = [] := by
  constructor
  · intro he
    rcases he with ⟨e, hw, -⟩
    exact hw
  · intro hw
    rcases (next_iff_expansion_or_scan trail lvl st st').mp h with he | hs
    · exact he
    · exact absurd hw (isScan_work_ne_nil hs)

/-! ## The event contribution of one executed transition

`stepCounts` reads the contribution off the transition: an expansion
contributes one expansion event; every other continuing transition
contributes one scan event plus the current-level marks the executed scan
actually added (`st'.marks` grew by them). The terminal `.done` transition
performs no operation and contributes no event; the trace's step count is
therefore `expansions + scans + 1`. -/

/-- The event contribution of one executed `.next` transition. Only applied
to transitions of the real analyzer: on those, the `[]` case is exactly the
reason-expansion arm (`isExpansion_iff_work_nil_of_next`). -/
def stepCounts (st st' : AnalyzerState) : EventCounts :=
  match st.work with
  | [] => { expansions := 1, scans := 0, marks := 0 }
  | _ => { expansions := 0, scans := 1,
           marks := st'.marks.length - st.marks.length }

/-- The read-off on an empty worklist: one expansion event. -/
theorem stepCounts_of_work_nil {st st' : AnalyzerState} (hw : st.work = []) :
    stepCounts st st' = { expansions := 1, scans := 0, marks := 0 } := by
  obtain ⟨w, s, m, l⟩ := st
  subst hw
  rfl

/-- The read-off on a nonempty worklist: one scan event, with the marks the
scan added as a separate counter. -/
theorem stepCounts_of_work_cons {st st' : AnalyzerState} {c : Clause}
    {cs : List Clause} (hw : st.work = c :: cs) :
    stepCounts st st'
      = { expansions := 0, scans := 1,
          marks := st'.marks.length - st.marks.length } := by
  obtain ⟨w, s, m, l⟩ := st
  subst hw
  rfl

/-- The event counter of a continuing transition is EXACTLY the expansion
indicator: `1` for a reason expansion, `0` for a scan — tied through
`IsExpansion`, not through a re-implementation of the arm. -/
theorem stepCounts_expansions_eq_one_iff (trail : List TrailEntry) (lvl : Nat)
    {st st' : AnalyzerState}
    (h : analyzeNext trail lvl st = AnalyzerStep.next st') :
    (stepCounts st st').expansions = 1 ↔ IsExpansion trail lvl st st' := by
  rw [isExpansion_iff_work_nil_of_next trail lvl h]
  cases hw : st.work <;> simp [stepCounts, hw]

/-- One continuing transition contributes exactly one event of the
expansion/scan kinds. -/
theorem stepCounts_expansions_add_scans (st st' : AnalyzerState) :
    (stepCounts st st').expansions + (stepCounts st st').scans = 1 := by
  cases hw : st.work <;> simp [stepCounts, hw]

/-! ## The counted executed run

`analyzeEvents` performs the same recursion as `analyzeTrace`, but also
accumulates the events of the transitions it actually takes (unlike
`analyzeTrace`, which only counts them). The theorems below pin its
stopping behaviour and its counts to the executed trace. -/

/-- The analyzer run with its event counts accumulated from the executed
transitions; `none` iff the fuel runs out first, exactly as
`analyzeTrace`. -/
def analyzeEvents (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (EventCounts × Option (List (Literal × Nat) × Literal))
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext trail lvl st with
      | .done r => some ({ expansions := 0, scans := 0, marks := 0 }, r)
      | .next st' =>
          match analyzeEvents trail lvl fuel st' with
          | none => none
          | some (c, r) => some (EventCounts.add (stepCounts st st') c, r)

/-- The executed analyzer's pivot-expansion count — the value the
scheduler's analyze site records into `events.reasonResolutions` (O1
wiring). Total: `0` when the run exhausts its fuel, so the call site
stays computable; the run's completeness on supported inputs is
`analyzeEvents_complete_of_reachable`. -/
def analyzeEventsExpansions (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : Nat :=
  ((analyzeEvents trail lvl (analysisFuel trail c)
      (initAnalysisState c)).map (fun p => p.1.expansions)).getD 0

/-- EXACTNESS: a completed counted run stops exactly where `analyzeTrace`
stops, with the same result, and its events decompose the trace's step
count exactly: `expansions + scans + 1 = k` (the `+ 1` is the terminal
`.done` transition, which performs no operation). This identifies the count
of expansions in the completed trace; it is NOT a bound by fuel. -/
theorem analyzeEvents_trace_of_events (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (c : EventCounts)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeEvents trail lvl fuel st = some (c, r) →
    ∃ k : Nat, analyzeTrace trail lvl fuel st = some (k, r) ∧
      c.expansions + c.scans + 1 = k := by
  intro fuel
  induction fuel with
  | zero => intro st c r h; simp [analyzeEvents] at h
  | succ fuel ih =>
      intro st c r h
      cases hn : analyzeNext trail lvl st with
      | done res =>
          simp only [analyzeEvents, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨1, by simp only [analyzeTrace, hn], by simp⟩
      | next st' =>
          cases he : analyzeEvents trail lvl fuel st' with
          | none => simp [analyzeEvents, hn, he] at h
          | some cr =>
              obtain ⟨c', r'⟩ := cr
              simp only [analyzeEvents, hn, he, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨hc, hr⟩ := h
              obtain ⟨k', hk', har⟩ := ih st' c' r' he
              refine ⟨k' + 1, ?_, ?_⟩
              · simp only [analyzeTrace_succ, hn, hk', hr]
              · rw [← hc]
                simp only [EventCounts.add_expansions, EventCounts.add_scans]
                have hsep := stepCounts_expansions_add_scans st st'
                omega

/-- CONVERSELY (completion): every completed trace has a counted run with
the same result and the same exact decomposition. -/
theorem analyzeEvents_of_trace (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace trail lvl fuel st = some (k, r) →
    ∃ c : EventCounts, analyzeEvents trail lvl fuel st = some (c, r) ∧
      c.expansions + c.scans + 1 = k := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{ expansions := 0, scans := 0, marks := 0 }, ?_, ?_⟩
          · simp only [analyzeEvents, hn]
          · simp
      | next st' =>
          cases ht : analyzeTrace trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace_succ, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨c', hc', har⟩ := ih st' k' r' ht
              refine ⟨EventCounts.add (stepCounts st st') c', ?_, ?_⟩
              · simp only [analyzeEvents, hn, hc']
              · simp only [EventCounts.add_expansions, EventCounts.add_scans]
                have hsep := stepCounts_expansions_add_scans st st'
                omega

/-- THE COUNTERPOINT (not the deliverable): the counts also fit inside the
fuel, but that bound alone would not identify expansions, scans or marks.
The exact statement is `analyzeEvents_trace_of_events`. -/
theorem analyzeEvents_steps_le_fuel (trail : List TrailEntry) (lvl : Nat)
    {fuel : Nat} {st : AnalyzerState} {c : EventCounts}
    {r : Option (List (Literal × Nat) × Literal)}
    (h : analyzeEvents trail lvl fuel st = some (c, r)) :
    c.expansions + c.scans + 1 ≤ fuel := by
  obtain ⟨k, hk, har⟩ := analyzeEvents_trace_of_events trail lvl fuel st c r h
  have := analyzeTrace_steps_le trail lvl fuel st k r hk
  omega

/-! ## Relation to the existing allowance analyzer

The counted run is not a parallel instrument: its result IS the result of
`analyzeAtAllowance`, and on B1's reachable input class it COMPLETES (so
the counts belong to a semantic stop, not to a truncated run). -/

/-- The counted run's result is the executable allowance entry point's
result. -/
theorem analyzeEvents_result_eq_analyzeAtAllowance (trail : List TrailEntry)
    (lvl : Nat) (c : Clause) {cs : EventCounts}
    {r : Option (List (Literal × Nat) × Literal)}
    (h : analyzeEvents trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (cs, r)) :
    analyzeAtAllowance trail lvl c = r := by
  obtain ⟨k, hk, -⟩ := analyzeEvents_trace_of_events trail lvl
    (analysisFuel trail c) (initAnalysisState c) cs r h
  rw [analyzeAtAllowance_fuel_eq]
  exact analyzeTrace_snd trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk

/-- On supported reachable inputs the counted run COMPLETES at the executable
allowance, and the observed counts decompose the trace exactly. This is the
"completed multi-resolution trace with correct counts" contract in theorem
form: `analyzeEvents_of_trace` turns B1's no-exhaustion theorem into a
counted, non-truncated run. -/
theorem analyzeEvents_complete_of_reachable (c : Clause)
    {trail : List TrailEntry} {lvl : Nat} (hne : 1 ≤ c.length)
    (hr : AnalyzerReachable trail lvl c (initAnalysisState c)) :
    ∃ (cs : EventCounts) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
      analyzeEvents trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (cs, r) ∧
      analyzeTrace trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, r) ∧
      cs.expansions + cs.scans + 1 = k := by
  obtain ⟨k, r, hk⟩ := analysis_complete_of_reachable c hne hr
  obtain ⟨cs, hcs, har⟩ := analyzeEvents_of_trace trail lvl
    (analysisFuel trail c) (initAnalysisState c) k r hk
  exact ⟨cs, k, r, hcs, hk, har⟩

/-! ## A completed multi-resolution trace with derived counts

A fixture of the same shape as B1's worked example (its definitions are
`private`, so this module states its own): four level-1 decisions falsify
the side literals of a five-literal reason, a level-2 decision and a
level-2 implication provide the conflict. Resolving it takes one reason
expansion, nine scans (two of which mark a current-level pivot, four of
which record a below-level falsifier, and two of which drop an empty
clause), and the terminal stop. -/

/-- A decision entry of the fixture. -/
private def evDec (l : Literal) (lv : Nat) : TrailEntry :=
  { literal := l, level := lv, reason := none }

/-- An implication entry of the fixture. -/
private def evImp (l : Literal) (lv : Nat) (cl : Clause) : TrailEntry :=
  { literal := l, level := lv, reason := some { clause := cl } }

/-- The fixture trail: four level-1 decisions falsifying the side literals of
the reason, a level-2 decision, and the level-2 implication whose reason is
the five-literal clause `[x2 ≤ 3, ¬(x3 ≤ 0), ¬(x3 ≤ 1), ¬(x3 ≤ 2), ¬(x3 ≤ 3)]`. -/
private def evTrail : List TrailEntry :=
  [ evDec (posLe 3 0) 1, evDec (posLe 3 1) 1, evDec (posLe 3 2) 1,
    evDec (posLe 3 3) 1, evDec (posLe 1 5) 2,
    evImp (posLe 2 3) 2
      [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3] ]

/-- The conflict clause of the fixture, falsified at level 2. -/
private def evConflict : Clause := [negLe 2 3, negLe 1 5]

/-- The below-level falsifiers the fixture records (newest mark first). -/
private def evBelow : List (Literal × Nat) :=
  [(negLe 3 3, 1), (negLe 3 2, 1), (negLe 3 1, 1), (negLe 3 0, 1)]

-- THE COMPLETED COUNTED TRACE OF THE FIXTURE: one reason expansion, nine
-- scans, two current-level marks, and a completed semantic stop with the
-- expected below-level set and asserting literal. Derived by evaluation of
-- the REAL `analyzeEvents` recursion at the executable allowance.
example :
    analyzeEvents evTrail 2 (analysisFuel evTrail evConflict)
        (initAnalysisState evConflict)
      = some ({ expansions := 1, scans := 9, marks := 2 },
              some (evBelow, posLe 1 5)) := rfl

-- The same fixture through B1's trace: eleven steps, so the counted events
-- account for the trace exactly: 1 + 9 + 1 = 11.
example :
    analyzeTrace evTrail 2 (analysisFuel evTrail evConflict)
        (initAnalysisState evConflict)
      = some (11, some (evBelow, posLe 1 5)) := rfl

-- The exactness theorem INSTANTIATED on the fixture: the expansion count is
-- the specific number 1, and it decomposes the observed trace length.
example :
    ∃ k : Nat,
      analyzeTrace evTrail 2 (analysisFuel evTrail evConflict)
          (initAnalysisState evConflict)
        = some (k, some (evBelow, posLe 1 5)) ∧
      1 + 9 + 1 = k ∧
      ({ expansions := 1, scans := 9, marks := 2 } : EventCounts).expansions = 1 ∧
      ({ expansions := 1, scans := 9, marks := 2 } : EventCounts).marks = 2 := by
  obtain ⟨k, hk, har⟩ := analyzeEvents_trace_of_events evTrail 2
    (analysisFuel evTrail evConflict) (initAnalysisState evConflict)
    { expansions := 1, scans := 9, marks := 2 } (some (evBelow, posLe 1 5)) rfl
  have hk11 : k = 11 := by simpa using har.symm
  subst hk11
  exact ⟨11, rfl, rfl, rfl, rfl⟩

-- The counted run's result is the executable allowance entry point's result.
example : analyzeAtAllowance evTrail 2 evConflict = some (evBelow, posLe 1 5) :=
  analyzeEvents_result_eq_analyzeAtAllowance evTrail 2 evConflict rfl

end LeanFzn.Solver.Propagation
