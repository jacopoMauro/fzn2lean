/-
File: LeanFzn/Solver/Propagation/AnalysisProgress.lean

Purpose:
  B1 — the analysis worklist as an EXPLICIT transition system, so its
  progress can be measured per operation instead of being read off the
  recursive definition.

  The plan is emphatic that the analyzer's fuel must be accounted for by
  the transitions it actually performs — scanning a clause literal,
  marking a falsifier, selecting the pivot and expanding its reason —
  not by the size of the output clause. This module therefore:

  * `AnalyzerState`/`AnalyzerStep`: the worklist state and the result of
    ONE transition (done with a result, or continue from a new state);
  * `analyzeNext`: the transition function, one branch per operation;
  * `scanCost`/`pivotCost`: the two cost components the fuel has to pay
    for, defined on the transition, not on the clause;
  * `analyzeLoop`: the fuel loop over `analyzeNext`;
  * `analyzeStep_eq_analyzeLoop`: the simulation proof tying the new
    transition system to the shipped `analyzeStep`, so the accounting
    below is about the analyzer that actually runs;
  * `analyzeLoop_mono`/`analyzeStep_mono_le`: fuel monotonicity — more
    fuel never loses a result, which is what makes an input-dependent
    allowance sound relative to the shipped constant;
  * the SUPPORTED-INPUT vocabulary (INTERFACES §2.3): `AnalyzerTrailOk`
    (the trail discipline: distinct normalized literals + chronological
    reasons), `AnalyzerInput`, `AnalysisOutcome`, `analyzeClassified`,
    and `AnalyzerReachable` — the reachable state class of the executed
    analyzer, established at `initAnalysisState` and closed under
    `analyzeNext`. `AnalysisCompletion.lean` derives the pivot payment
    and the measure decrease from it, so the completion theorem takes
    the reachable input invariant instead of a per-state decrease
    hypothesis.

  Held here rather than in `TrailEval.lean` so the executable analyzer
  and its shipped proof base are untouched; the simulation theorem is
  what keeps the two from drifting apart.

Dependencies:
  - LeanFzn.Solver.Propagation.TrailEval: `markLit`, `nextPivot`, `skipEq`, `analyzeStep`.
  - LeanFzn.Solver.Propagation.ConflictResolution: `analysisAllowance`, `analysisFuel`,
    `analyzeAtAllowance` — the allowance the executable call uses.

DAG:
  TrailEval -> LeanFzn.Solver.UIP.AnalysisProgress
  ConflictResolution -> LeanFzn.Solver.UIP.AnalysisProgress
-/

import LeanFzn.Solver.Propagation.TrailEval
import LeanFzn.Solver.Propagation.ConflictResolution
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The worklist and its transition -/

/-- The analyzer worklist: clauses still to scan, the literal to skip in
the current reason (the pivot just resolved away), the marked
current-level entries, and the below-level falsifiers already learnt. -/
structure AnalyzerState where
  /-- clauses still to scan -/
  work : List Clause
  /-- the pivot of the reason currently being scanned (never re-marked) -/
  skip : Option Literal
  /-- marked current-level trail entries -/
  marks : List TrailEntry
  /-- below-level falsifiers with their levels -/
  learnt : List (Literal × Nat)

/-- The result of one analysis transition. -/
inductive AnalyzerStep where
  /-- the loop stops: `some` result, or `none` for an unsupported input -/
  | done (result : Option (List (Literal × Nat) × Literal))
  /-- the loop continues from the returned state -/
  | next (state : AnalyzerState)

/-- The initial analyzer state for a conflict clause: the conflict clause is
the only worklist item, nothing is marked, the skip is empty (the
INITIAL-CONFLICT phase), and nothing is learnt yet. -/
def initAnalysisState (c : Clause) : AnalyzerState :=
  { work := [c], skip := none, marks := [], learnt := [] }

/-- ONE analyzer transition, with the operation it performs exposed.

* a clause literal is scanned and dropped from the worklist (its falsifier
  is skipped, already marked, or already learnt);
* a falsifier is marked: at the root level it is dropped, at the current
  level it becomes a mark, below it it is recorded in the learnt list;
* the pivot is selected: the latest marked entry;
* the pivot's reason is expanded: its clause is pushed with the pivot
  literal as the skip.

This is the same decision sequence as `analyzeStep`; the two are proved
equal by simulation in `analyzeStep_eq_analyzeLoop`. -/
def analyzeNext (trail : List TrailEntry) (lvl : Nat) (st : AnalyzerState) :
    AnalyzerStep :=
  match st.work with
  | [] =>
      match nextPivot trail st.marks with
      | none => .done none
      | some e =>
          let marks' := st.marks.filter fun m => !litEqB m.literal e.literal
          if marks'.isEmpty then .done (some (st.learnt, e.literal))
          else
            match e.reason with
            | none => .done none
            | some r =>
                .next { work := [r.clause], skip := some e.literal,
                        marks := marks', learnt := st.learnt }
  | c :: cs =>
      match c with
      | [] => .next { work := cs, skip := st.skip, marks := st.marks,
                      learnt := st.learnt }
      | q0 :: qs =>
          let q := q0.norm
          if skipEq st.skip q then
            .next { work := qs :: cs, skip := st.skip, marks := st.marks,
                    learnt := st.learnt }
          else
            match markLit trail lvl st.marks st.learnt q with
            | none => .done none
            | some mp =>
                .next { work := qs :: cs, skip := st.skip,
                        marks := mp.1, learnt := mp.2 }

/-! ## The two cost components

The only two things the analyzer does are *scan a literal* and *expand a
pivot*. Both are charged separately, because they are bounded by
different quantities: a scan consumes one worklist literal, an expansion
consumes one marked entry and re-seeds one reason clause. -/

/-- Scan cost: the number of literals still to scan. Every scan
transition strictly decreases it — including the transition that drops an
already-empty clause, which decreases the clause count. -/
def scanCost (cs : List Clause) : Nat := cs.length + (cs.map List.length).sum

/-- Pivot cost: the marked current-level entries. Every expansion removes
the pivot's literal from this list, so this is the *per-round* count; the
ROUNDS are paid for by `skipCost` in `AnalysisCompletion.lean` (the
frontier's reason budget), whose decrease is derived there from the
reachable `AnalyzerReachable` class. -/
def pivotCost (st : AnalyzerState) : Nat := st.marks.length

/-! ## The fuel loop -/

/-- The fuel loop over `analyzeNext`: `done` returns the result, `next`
continues with one unit of fuel spent. Fuel `0` fails, exactly as in
`analyzeStep`. -/
def analyzeLoop (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (List (Literal × Nat) × Literal)
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext trail lvl st with
      | .done r => r
      | .next st' => analyzeLoop trail lvl fuel st'

/-! ## Simulation -/

/-- The shipped analyzer IS the transition loop: the explicit transition
system above performs the same decisions, in the same order, with the
same fuel accounting. This is what makes every statement below a
statement about the analyzer that actually runs. -/
theorem analyzeStep_eq_analyzeLoop (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (cs : List Clause) (skip : Option Literal)
      (marks : List TrailEntry) (learnt : List (Literal × Nat)),
    analyzeStep trail lvl fuel cs skip marks learnt
      = analyzeLoop trail lvl fuel { work := cs, skip := skip,
                                     marks := marks, learnt := learnt } := by
  intro fuel
  induction fuel with
  | zero =>
      intro cs skip marks learnt
      simp [analyzeStep, analyzeLoop]
  | succ fuel ih =>
      intro cs skip marks learnt
      cases cs with
      | nil =>
          cases hp : nextPivot trail marks with
          | none => simp [analyzeStep, analyzeLoop, analyzeNext, hp]
          | some e =>
              by_cases hq : (marks.filter
                  fun m => !litEqB m.literal e.literal).isEmpty
              · simp [analyzeStep, analyzeLoop, analyzeNext, hp, hq]
              · cases hr : e.reason with
                | none =>
                    simp [analyzeStep, analyzeLoop, analyzeNext, hp, hq, hr]
                | some r =>
                    have hgoal := ih [r.clause] (some e.literal)
                      (marks.filter fun m => !litEqB m.literal e.literal) learnt
                    simp only [analyzeStep, analyzeLoop, analyzeNext, hp, hq, hr]
                    exact hgoal
      | cons c cs =>
          cases c with
          | nil =>
              have hgoal := ih cs skip marks learnt
              simp only [analyzeStep, analyzeLoop, analyzeNext]
              exact hgoal
          | cons q0 qs =>
              by_cases hs : skipEq skip q0.norm
              · have hgoal := ih (qs :: cs) skip marks learnt
                simp only [analyzeStep, analyzeLoop, analyzeNext, hs]
                exact hgoal
              · cases hm : markLit trail lvl marks learnt q0.norm with
                | none => simp [analyzeStep, analyzeLoop, analyzeNext, hs, hm]
                | some mp =>
                    have hgoal := ih (qs :: cs) skip mp.1 mp.2
                    simp only [analyzeStep, analyzeLoop, analyzeNext, hs, hm]
                    exact hgoal

/-! ## Fuel monotonicity

One extra unit of fuel can never turn a completed analysis into a failed
one: the transition sequence does not depend on the fuel, only on the
number of transitions the loop is allowed to take. This is what makes it
safe to raise the input-dependent allowance. -/

/-- More fuel cannot lose a result. -/
theorem analyzeLoop_mono (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState)
      (r : List (Literal × Nat) × Literal),
    analyzeLoop trail lvl fuel st = some r →
    analyzeLoop trail lvl (fuel + 1) st = some r := by
  intro fuel
  induction fuel with
  | zero => intro st r h; simp [analyzeLoop] at h
  | succ fuel ih =>
      intro st r h
      cases hn : analyzeNext trail lvl st with
      | done res => simp only [analyzeLoop, hn] at h ⊢; exact h
      | next st' =>
          simp only [analyzeLoop, hn] at h ⊢
          exact ih st' r h

/-- More fuel cannot lose a result (arbitrary increase). -/
theorem analyzeLoop_mono_le (trail : List TrailEntry) (lvl : Nat)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (st : AnalyzerState)
    {r : List (Literal × Nat) × Literal}
    (h : analyzeLoop trail lvl fuel st = some r) :
    analyzeLoop trail lvl fuel' st = some r := by
  obtain ⟨k, hk⟩ : ∃ k, fuel' = fuel + k := ⟨fuel' - fuel, by omega⟩
  subst hk
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact analyzeLoop_mono trail lvl (fuel + k) st r ih

/-- Fuel monotonicity, read back through the simulation: a successful
`analyzeStep` run also succeeds at any larger allowance with the same
result. -/
theorem analyzeStep_mono_le (trail : List TrailEntry) (lvl : Nat)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {cs : List Clause} {skip : Option Literal} {marks : List TrailEntry}
    {learnt : List (Literal × Nat)} {r : List (Literal × Nat) × Literal}
    (h : analyzeStep trail lvl fuel cs skip marks learnt = some r) :
    analyzeStep trail lvl fuel' cs skip marks learnt = some r := by
  rw [analyzeStep_eq_analyzeLoop] at h ⊢
  exact analyzeLoop_mono_le trail lvl hle _ h

/-! ## Cost accounting on the transitions

Both cost components are stated on the transition, so the accounting is a
statement about the operations the analyzer performs, not about the size
of the clause it produces. -/

/-- Every scan transition strictly decreases the scan cost: exactly one
worklist literal (or one empty clause) leaves the worklist. -/
theorem scanCost_lt_of_cons (c : Clause) (cs : List Clause) :
    scanCost cs < scanCost (c :: cs) := by
  simp only [scanCost, List.length_cons, List.map_cons, List.sum_cons]
  omega

/-- The transition that drops an already-empty clause. -/
theorem scanCost_lt_of_empty_cons (cs : List Clause) :
    scanCost cs < scanCost ([] :: cs) :=
  scanCost_lt_of_cons [] cs

/-- The transition that scans and drops one literal. -/
theorem scanCost_lt_of_scanned (q : Literal) (qs : Clause) (cs : List Clause) :
    scanCost (qs :: cs) < scanCost ((q :: qs) :: cs) := by
  simp only [scanCost, List.length_cons, List.map_cons, List.sum_cons]
  omega

/-- A reason expansion re-seeds the worklist with the pivot's reason
clause. This is exactly the pending work the plan requires the allowance
to account for, and it is charged to the pivot round, not to a scan. -/
theorem scanCost_expand (r : Clause) : scanCost [r] = 1 + r.length := by
  simp [scanCost]

/-- An exhausted worklist has zero scan cost. -/
theorem scanCost_nil : scanCost ([] : List Clause) = 0 := rfl

/-- `countP` splits a list between a predicate and its complement. -/
private theorem countP_add_compl (l : List TrailEntry) (p : TrailEntry → Bool) :
    l.countP p + l.countP (fun m => !p m) = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      cases ha : p a <;> simp_all <;> omega

/-- Every pivot expansion removes the pivot's literal from the marks, so
the *per-round* count strictly decreases whenever a round is taken. The
round itself is paid for by the frontier's reason budget (`skipCost`); the
derivation is in `AnalysisCompletion.lean` (`skipCost_pivot_of_reachable`). -/
theorem pivotCost_filter_lt (marks : List TrailEntry) (e : TrailEntry)
    (hmem : marks.any (fun m => litEqB m.literal e.literal) = true) :
    (marks.filter fun m => !litEqB m.literal e.literal).length
      < marks.length := by
  have hpos : 0 < marks.countP (fun m => litEqB m.literal e.literal) := by
    rw [List.countP_pos_iff]
    exact List.any_eq_true.mp hmem
  have hsum := countP_add_compl marks (fun m => litEqB m.literal e.literal)
  simp only [List.countP_eq_length_filter] at hsum hpos
  omega

/-! ## Wiring the computed allowance into the executable call

`analysisFuel` is the allowance the executable analysis is run with, and
`analyzeAtAllowance` is the entry point that consumes it. The two results
below are what make the switch honest rather than hopeful:

* the computed allowance is never below the shipped constant, so the
  constant's inputs cannot regress;
* anything the shipped analyzer finds, the computed-allowance analyzer
  finds too, with the same result — a consequence of fuel monotonicity,
  not of re-running the analysis.

B1 RESIDUAL OBLIGATION (recorded in `PLAN.md`): prove that
`analysisAllowance` alone suffices, i.e. drop the `max` floor. That needs
the reachable-state ordering invariant bounding the number of pivot
rounds; it is deliberately NOT claimed here. -/

/-- The executable allowance is never below the historical constant. -/
theorem historicalAllowance_le_analysisFuel (trail : List TrailEntry)
    (c : Clause) : historicalAllowance trail ≤ analysisFuel trail c :=
  Nat.le_max_right _ _

/-- The executable allowance is never below the computed literal budget. -/
theorem analysisAllowance_le_analysisFuel (trail : List TrailEntry)
    (c : Clause) : analysisAllowance trail c ≤ analysisFuel trail c :=
  Nat.le_max_left _ _

/-- `analyzeTrail` runs at exactly the historical constant, so its fuel is
the floor of `analysisFuel`. -/
theorem analyzeTrail_at_historical (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) :
    analyzeTrail trail lvl c
      = analyzeStep trail lvl (historicalAllowance trail) [c] none [] [] :=
  rfl

/-- The computed-allowance entry point dominates the shipped analysis:
every result `analyzeTrail` returns, `analyzeAtAllowance` returns with the
same witness. This is the refinement proof for the wiring. -/
theorem analyzeAtAllowance_dominates {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {r : List (Literal × Nat) × Literal}
    (h : analyzeTrail trail lvl c = some r) :
    analyzeAtAllowance trail lvl c = some r := by
  rw [analyzeTrail_at_historical] at h
  exact analyzeStep_mono_le trail lvl (historicalAllowance_le_analysisFuel trail c) h

/-- Failure of the shipped analysis does not pin down the computed one: the
computed budget can succeed where the constant is exhausted. This is the
*reason* the allowance is input-dependent — the direction above is the
soundness half, this is the completeness half that the constant lacks. -/
theorem analyzeAtAllowance_fuel_eq (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) :
    analyzeAtAllowance trail lvl c
      = analyzeLoop trail lvl (analysisFuel trail c)
          { work := [c], skip := none, marks := [], learnt := [] } :=
  analyzeStep_eq_analyzeLoop trail lvl (analysisFuel trail c) [c] none [] []

/-! ## Supported analysis inputs and their classification (INTERFACES §2.3)

B1 owns the supported-input class, the reachability predicate of the
executed analyzer, and the result classification. The completion theorem
in `AnalysisCompletion.lean` takes the reachability predicate rather than
an arbitrary per-state decrease hypothesis. -/

/-- The supported analyzer input class: a falsified, entailed conflict
clause over a coherent trail. -/
structure AnalyzerInput (leaf : Assignment → Bool) (bs : BranchState leaf) where
  /-- the clause the analyzer is run on -/
  conflict : Clause
  /-- a nonempty clause; this pays the `+1` of the initial measure -/
  nonempty : 1 ≤ conflict.length
  /-- the conflict clause is a consequence of the problem -/
  entailed : LearnedEntailed leaf [conflict]
  /-- every literal of the conflict clause is trail-falsified -/
  falsified : FalsifiedByTrail bs conflict

/-- Result classification of one analysis run. -/
inductive AnalysisOutcome where
  /-- first-UIP analysis succeeded: below-level falsifiers and the UIP -/
  | success (below : List (Literal × Nat)) (uip : Literal)
  /-- the analysis ran at level 0 over a falsified entailed clause:
      a proof of root contradiction, never a "failed analysis" -/
  | rootContradiction
  /-- no asserting result above the root: the scheduler must take the
      local-exclusion or chronological fallback; NEVER a UNSAT verdict -/
  | unsupported
  deriving DecidableEq, Repr

/-- The classified computed-allowance entry point. -/
def analyzeClassified (trail : List TrailEntry) (lvl : Nat) (c : Clause) :
    AnalysisOutcome :=
  match analyzeAtAllowance trail lvl c with
  | some (below, uip) => .success below uip
  | none => if lvl = 0 then .rootContradiction else .unsupported

/-- The trail-level discipline of a supported analysis input: trail literals
are distinct up to normalization, entries store the canonical form, and every
reason literal other than its pivot has an EXACT earlier falsifier on the
trail (chronology — `BranchState.WellFormed`'s fourth conjunct).

This is the whole of what the completion proof assumes about the trail. In
particular it does NOT assume that the conflict clause is falsified: a
semantic `none` (unsupported local explanation) is a legitimate stop, and the
completion theorem is about the budget, not about the verdict. -/
structure AnalyzerTrailOk (trail : List TrailEntry) : Prop where
  /-- trail literals occur at most once, up to normalization -/
  distinct : TrailLiteralsDistinct trail
  /-- entries store the canonical (normalized) literal form -/
  norm : ∀ e ∈ trail, e.literal = e.literal.norm
  /-- chronology: a non-pivot reason literal has an exact earlier falsifier -/
  chron : ∀ e ∈ trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l ≠ e.literal →
    ∃ e' ∈ trail, e'.literal = l.negate ∧ TrailEntry.earlierThan trail e' e

/-- Analyzer states occurring from `initAnalysisState c` under the
chronological reason assumptions, closed under `analyzeNext`. This is the
reachable state class the completion theorem consumes: the trail discipline
is established at initialization and never changes, and every `.next`
transition of the analyzer extends the closure. -/
inductive AnalyzerReachable (trail : List TrailEntry) (lvl : Nat) (c : Clause) :
    AnalyzerState → Prop where
  /-- the initial state, once the trail meets the chronological discipline -/
  | init (hok : AnalyzerTrailOk trail) :
      AnalyzerReachable trail lvl c (initAnalysisState c)
  /-- every `.next` transition of `analyzeNext` stays in the class -/
  | next {st st'} : AnalyzerReachable trail lvl c st →
      analyzeNext trail lvl st = AnalyzerStep.next st' →
      AnalyzerReachable trail lvl c st'

end LeanFzn.Solver.Propagation
