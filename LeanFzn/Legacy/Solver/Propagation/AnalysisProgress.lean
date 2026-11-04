/-
File: LeanFzn/Solver/Propagation/AnalysisProgress.lean

Purpose:
  B1/R1a — cost components, fuel monotonicity and the supported-input
  vocabulary of the LCG analyzer (`LcgAnalyzer.lean`: `AnalyzerState`,
  `analyzeNext`, `analyzeLoop`).

  * `scanCost`/`pivotCost`: the two cost components, stated on the
    transition;
  * `analyzeLoop_mono`/`analyzeLoop_mono_le`: more fuel never loses a result;
  * the SUPPORTED-INPUT vocabulary (INTERFACES §2.3): `AnalyzerTrailOk`,
    `AnalyzerInput`, `AnalysisOutcome`, `analyzeClassified`,
    `AnalyzerReachable`.

  R1a: the analyzer the scheduler runs is no longer the historical
  `analyzeStep` (`TrailEval.lean`, kept for the reference engine), so the
  former simulation theorem `analyzeStep_eq_analyzeLoop` and the dominance
  theorem `analyzeAtAllowance_dominates` are retired (they related two
  analyzers that now differ by design). Termination no longer needs any
  trail discipline: see `AnalysisCompletion.lean`.

Dependencies:
  - LeanFzn.Solver.Propagation.ConflictResolution: `analyzeAtAllowance`,
    `analysisFuel` (via `LcgAnalyzer`).
-/

import LeanFzn.Solver.Propagation.TrailEval
import LeanFzn.Legacy.Solver.Propagation.ConflictResolution
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The two cost components -/

/-- Scan cost: the number of literals (and clauses) still to scan. -/
def scanCost (cs : List Clause) : Nat := cs.length + (cs.map List.length).sum

/-- Pivot cost: the marked current-level indices. -/
def pivotCost (st : AnalyzerState) : Nat := st.marks.length

/-! ## Fuel monotonicity -/

/-- More fuel cannot lose a result. -/
theorem analyzeLoop_mono (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState)
      (r : List (Literal × Nat) × Literal),
    analyzeLoop orig trail lvl fuel st = some r →
    analyzeLoop orig trail lvl (fuel + 1) st = some r := by
  intro fuel
  induction fuel with
  | zero => intro st r h; simp [analyzeLoop] at h
  | succ fuel ih =>
      intro st r h
      cases hn : analyzeNext orig trail lvl st with
      | done res => simp only [analyzeLoop, hn] at h ⊢; exact h
      | next st' =>
          simp only [analyzeLoop, hn] at h ⊢
          exact ih st' r h

/-- More fuel cannot lose a result (arbitrary increase). -/
theorem analyzeLoop_mono_le (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (st : AnalyzerState)
    {r : List (Literal × Nat) × Literal}
    (h : analyzeLoop orig trail lvl fuel st = some r) :
    analyzeLoop orig trail lvl fuel' st = some r := by
  obtain ⟨k, hk⟩ : ∃ k, fuel' = fuel + k := ⟨fuel' - fuel, by omega⟩
  subst hk
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Nat.add_succ]
      exact analyzeLoop_mono orig trail lvl (fuel + k) st r ih

/-! ## Cost accounting on the transitions -/

theorem scanCost_lt_of_cons (c : Clause) (cs : List Clause) :
    scanCost cs < scanCost (c :: cs) := by
  simp only [scanCost, List.length_cons, List.map_cons, List.sum_cons]
  omega

theorem scanCost_lt_of_empty_cons (cs : List Clause) :
    scanCost cs < scanCost ([] :: cs) :=
  scanCost_lt_of_cons [] cs

theorem scanCost_lt_of_scanned (q : Literal) (qs : Clause) (cs : List Clause) :
    scanCost (qs :: cs) < scanCost ((q :: qs) :: cs) := by
  simp only [scanCost, List.length_cons, List.map_cons, List.sum_cons]
  omega

theorem scanCost_expand (r : Clause) : scanCost [r] = 1 + r.length := by
  simp [scanCost]

theorem scanCost_nil : scanCost ([] : List Clause) = 0 := rfl

/-- Every pivot expansion removes the pivot index from the marks. -/
theorem pivotCost_filter_lt (marks : List Nat) (i : Nat) (hmem : i ∈ marks) :
    (marks.filter (· != i)).length < marks.length := by
  induction marks with
  | nil => cases hmem
  | cons m ms ih =>
      rw [List.filter_cons]
      by_cases hm : m = i
      · subst hm
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.length_cons]
        have := List.length_filter_le (· != m) ms
        omega
      · have hm' : (m != i) = true := by simpa using hm
        rw [if_pos hm', List.length_cons, List.length_cons]
        have hi : i ∈ ms := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hm
          · exact h
        have := ih hi
        omega

/-- The executable entry point is the loop at the computed allowance. -/
theorem analyzeAtAllowance_fuel_eq (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) (c : Clause) :
    analyzeAtAllowance orig trail lvl c
      = analyzeLoop orig trail lvl (analysisFuel trail c) (initAnalysisState c) :=
  rfl

/-- THE UIP IS A CURRENT-LEVEL TRAIL LITERAL: a successful executable
analysis returns the literal of a trail entry at the analysis level. -/
theorem analyzeAtAllowance_uip_on_trail {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl c = some (below, uip)) :
    ∃ m ∈ trail, m.literal = uip ∧ m.level = lvl := by
  obtain ⟨hm0, hl0⟩ := lcgInv_init trail lvl c
  obtain ⟨-, i, m, hmi, hmlit, hmlev⟩ := analyzeLoop_inv _ _ below uip hm0 hl0 h
  exact ⟨m, List.mem_of_getElem? hmi, hmlit, hmlev⟩

/-- Every learned below-level literal of a successful executable analysis is
the normalized negation of a trail entry at its recorded level, strictly
between the root and the analysis level. -/
theorem analyzeAtAllowance_learntOk {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl c = some (below, uip)) :
    LcgLearntOk trail lvl below := by
  obtain ⟨hm0, hl0⟩ := lcgInv_init trail lvl c
  exact (analyzeLoop_inv _ _ below uip hm0 hl0 h).1

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
def analyzeClassified (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : AnalysisOutcome :=
  match analyzeAtAllowance orig trail lvl c with
  | some (below, uip) => .success below uip
  | none => if lvl = 0 then .rootContradiction else .unsupported

/-- The trail-level discipline of a supported analysis input: trail literals
are distinct up to normalization and entries store the canonical form.

R1a: the former third field `chron` (every non-pivot reason literal has an
EXACT earlier falsifier) is removed. It was only consumed by the old
frontier-based completion proof; the LCG analyzer's termination is
unconditional (`AnalysisCompletion.lean`), and the semantic form of
chronology (an earlier entry IMPLIES the negation, or the literal is false
at the root) is what the analyzer's bounded falsifier search checks at run
time. -/
structure AnalyzerTrailOk (trail : List TrailEntry) : Prop where
  /-- trail literals occur at most once, up to normalization -/
  distinct : TrailLiteralsDistinct trail
  /-- entries store the canonical (normalized) literal form -/
  norm : ∀ e ∈ trail, e.literal = e.literal.norm

/-- Analyzer states occurring from `initAnalysisState c`, closed under
`analyzeNext`. R1a: the initial state needs no trail discipline. -/
inductive AnalyzerReachable (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : AnalyzerState → Prop where
  /-- the initial state -/
  | init : AnalyzerReachable orig trail lvl c (initAnalysisState c)
  /-- every `.next` transition of `analyzeNext` stays in the class -/
  | next {st st'} : AnalyzerReachable orig trail lvl c st →
      analyzeNext orig trail lvl st = AnalyzerStep.next st' →
      AnalyzerReachable orig trail lvl c st'

end LeanFzn.Solver.Propagation
