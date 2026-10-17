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

`IsExpansion`/`IsScan` and the characterisation `expansion_or_scan_of_next`
/ `next_of_expansion_or_scan` live with the analyzer (`LcgAnalyzer.lean`). -/

/-- A scan consumes a worklist item, so its state has a nonempty worklist. -/
theorem isScan_work_ne_nil {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {st st' : AnalyzerState} (h : IsScan orig trail lvl st st') : st.work ≠ [] := by
  rcases h with ⟨cs, hw, -⟩ | ⟨q, qs, cs, hw, -⟩
    | ⟨q, qs, cs, marks', learnt', hw, -, -, -⟩
  · simp [hw]
  · simp [hw]
  · simp [hw]

/-- THE CHARACTERISATION: the continuing transitions of the real
`analyzeNext` are EXACTLY the reason expansions plus the scans. -/
theorem next_iff_expansion_or_scan (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) (st st' : AnalyzerState) :
    analyzeNext orig trail lvl st = AnalyzerStep.next st' ↔
      IsExpansion trail st st' ∨ IsScan orig trail lvl st st' :=
  ⟨fun h => expansion_or_scan_of_next h, fun h => next_of_expansion_or_scan h⟩

/-- A continuing transition is an expansion EXACTLY when its worklist is
empty. -/
theorem isExpansion_iff_work_nil_of_next {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st st' : AnalyzerState}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.next st') :
    IsExpansion trail st st' ↔ st.work = [] := by
  constructor
  · intro he
    rcases he with ⟨_, _, _, hw, -⟩
    exact hw
  · intro hw
    rcases expansion_or_scan_of_next h with he | hs
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
  obtain ⟨w, s, b, m, l⟩ := st
  subst hw
  rfl

/-- The read-off on a nonempty worklist: one scan event, with the marks the
scan added as a separate counter. -/
theorem stepCounts_of_work_cons {st st' : AnalyzerState} {c : Clause}
    {cs : List Clause} (hw : st.work = c :: cs) :
    stepCounts st st'
      = { expansions := 0, scans := 1,
          marks := st'.marks.length - st.marks.length } := by
  obtain ⟨w, s, b, m, l⟩ := st
  subst hw
  rfl

/-- The event counter of a continuing transition is EXACTLY the expansion
indicator: `1` for a reason expansion, `0` for a scan — tied through
`IsExpansion`, not through a re-implementation of the arm. -/
theorem stepCounts_expansions_eq_one_iff {orig : List Domain} (trail : List TrailEntry)
    (lvl : Nat) {st st' : AnalyzerState}
    (h : analyzeNext orig trail lvl st = AnalyzerStep.next st') :
    (stepCounts st st').expansions = 1 ↔ IsExpansion trail st st' := by
  rw [isExpansion_iff_work_nil_of_next h]
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
def analyzeEvents (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (EventCounts × Option (List (Literal × Nat) × Literal))
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext orig trail lvl st with
      | .done r => some ({ expansions := 0, scans := 0, marks := 0 }, r)
      | .next st' =>
          match analyzeEvents orig trail lvl fuel st' with
          | none => none
          | some (c, r) => some (EventCounts.add (stepCounts st st') c, r)

/-- The executed analyzer's pivot-expansion count — the value the
scheduler's analyze site records into `events.reasonResolutions` (O1
wiring). Total: `0` when the run exhausts its fuel, so the call site
stays computable; the run's completeness on supported inputs is
`analyzeEvents_complete_of_reachable`. -/
def analyzeEventsExpansions (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : Nat :=
  ((analyzeEvents orig trail lvl (analysisFuel trail c)
      (initAnalysisState c)).map (fun p => p.1.expansions)).getD 0

/-- EXACTNESS: a completed counted run stops exactly where `analyzeTrace`
stops, with the same result, and its events decompose the trace's step
count exactly: `expansions + scans + 1 = k` (the `+ 1` is the terminal
`.done` transition, which performs no operation). This identifies the count
of expansions in the completed trace; it is NOT a bound by fuel. -/
theorem analyzeEvents_trace_of_events (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (c : EventCounts)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeEvents orig trail lvl fuel st = some (c, r) →
    ∃ k : Nat, analyzeTrace orig trail lvl fuel st = some (k, r) ∧
      c.expansions + c.scans + 1 = k := by
  intro fuel
  induction fuel with
  | zero => intro st c r h; simp [analyzeEvents] at h
  | succ fuel ih =>
      intro st c r h
      cases hn : analyzeNext orig trail lvl st with
      | done res =>
          simp only [analyzeEvents, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨1, by simp only [analyzeTrace, hn], by simp⟩
      | next st' =>
          cases he : analyzeEvents orig trail lvl fuel st' with
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
theorem analyzeEvents_of_trace (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace orig trail lvl fuel st = some (k, r) →
    ∃ c : EventCounts, analyzeEvents orig trail lvl fuel st = some (c, r) ∧
      c.expansions + c.scans + 1 = k := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext orig trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{ expansions := 0, scans := 0, marks := 0 }, ?_, ?_⟩
          · simp only [analyzeEvents, hn]
          · simp
      | next st' =>
          cases ht : analyzeTrace orig trail lvl fuel st' with
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
theorem analyzeEvents_steps_le_fuel (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    {fuel : Nat} {st : AnalyzerState} {c : EventCounts}
    {r : Option (List (Literal × Nat) × Literal)}
    (h : analyzeEvents orig trail lvl fuel st = some (c, r)) :
    c.expansions + c.scans + 1 ≤ fuel := by
  obtain ⟨k, hk, har⟩ := analyzeEvents_trace_of_events orig trail lvl fuel st c r h
  have := analyzeTrace_steps_le orig trail lvl fuel st k r hk
  omega

/-! ## Relation to the existing allowance analyzer

The counted run is not a parallel instrument: its result IS the result of
`analyzeAtAllowance`, and on B1's reachable input class it COMPLETES (so
the counts belong to a semantic stop, not to a truncated run). -/

/-- The counted run's result is the executable allowance entry point's
result. -/
theorem analyzeEvents_result_eq_analyzeAtAllowance (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) (c : Clause) {cs : EventCounts}
    {r : Option (List (Literal × Nat) × Literal)}
    (h : analyzeEvents orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (cs, r)) :
    analyzeAtAllowance orig trail lvl c = r := by
  obtain ⟨k, hk, -⟩ := analyzeEvents_trace_of_events orig trail lvl
    (analysisFuel trail c) (initAnalysisState c) cs r h
  exact analyzeTrace_snd orig trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk

/-- The counted run COMPLETES at the executable allowance on EVERY input
(R1a: formerly `analyzeEvents_complete_of_reachable`, which needed a
nonempty clause and the reachable class), and the observed counts decompose
the trace exactly. -/
theorem analyzeEvents_complete (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) (c : Clause) :
    ∃ (cs : EventCounts) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
      analyzeEvents orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (cs, r) ∧
      analyzeTrace orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, r) ∧
      cs.expansions + cs.scans + 1 = k := by
  obtain ⟨k, r, hk⟩ := analysis_complete orig trail lvl c
  obtain ⟨cs, hcs, har⟩ := analyzeEvents_of_trace orig trail lvl
    (analysisFuel trail c) (initAnalysisState c) k r hk
  exact ⟨cs, k, r, hcs, hk, har⟩

/-! ## A completed multi-resolution trace with derived counts

A fixture of the same shape as B1's worked example (its definitions are
`private`, so this module states its own): four level-1 decisions falsify
the side literals of a five-literal reason, a level-2 decision and a
level-2 implication provide the conflict. Resolving it takes one reason
expansion, nine scans (two of which mark a current-level pivot, one of
which records the weakened below-level literal, three of which deduplicate
it, and two of which drop an empty clause), and the terminal stop. -/

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

/-- Four integer slots with domain `0..9`. -/
private def evOrig : List Domain :=
  List.replicate 4 ((List.range 10).map fun i => Value.int (Int.ofNat i))

/-- The below-level literal the fixture learns: the four side literals
`x3 > 0 … x3 > 3` all have the EARLIEST implying entry `x3 ≤ 0`, so they are
learnt as the single weakened literal `x3 > 0` (R1a semantic weakening). -/
private def evBelow : List (Literal × Nat) := [(negLe 3 0, 1)]

-- THE COMPLETED COUNTED TRACE OF THE FIXTURE: one reason expansion, nine
-- scans, two current-level marks, and a completed semantic stop. Derived by
-- evaluation of the REAL `analyzeEvents` recursion at the executable allowance.
example :
    analyzeEvents evOrig evTrail 2 (analysisFuel evTrail evConflict)
        (initAnalysisState evConflict)
      = some ({ expansions := 1, scans := 9, marks := 2 },
              some (evBelow, posLe 1 5)) := by decide

-- The same fixture through B1's trace: eleven steps = 1 + 9 + 1.
example :
    analyzeTrace evOrig evTrail 2 (analysisFuel evTrail evConflict)
        (initAnalysisState evConflict)
      = some (11, some (evBelow, posLe 1 5)) := by decide

-- The counted run's result is the executable allowance entry point's result.
example : analyzeAtAllowance evOrig evTrail 2 evConflict = some (evBelow, posLe 1 5) :=
  analyzeEvents_result_eq_analyzeAtAllowance evOrig evTrail 2 evConflict
    (cs := { expansions := 1, scans := 9, marks := 2 }) (by decide)

end LeanFzn.Solver.Propagation
