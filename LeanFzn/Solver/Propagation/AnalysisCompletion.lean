/-
File: LeanFzn/Solver/Propagation/AnalysisCompletion.lean

Purpose:
  B1/R1a — the analyzer's computed allowance cannot be exhausted, on EVERY
  input.

  R1a replaces the former frontier argument (which needed the reachable
  trail discipline `AnalyzerTrailOk`, including EXACT chronology of reason
  falsifiers) by the potential of `LcgAnalyzer.lean`: the worklist cost plus
  the reason budget of every trail entry before the falsifier bound. The
  bound is the index of the last expanded pivot, and the expansion guard
  makes it strictly decrease, so every `.next` transition strictly decreases
  the potential (`analyzerPotential_lt_of_next`) with no premise at all. The
  allowance `analysisFuel` is the initial potential plus one, hence:

  * `analyzeTrace_exists_of_potential` — fuel above the potential always
    observes a semantic stop;
  * `analysis_complete` / `analyzeAtAllowance_stops` — the executable entry
    point never truncates;
  * the classified verdicts are therefore semantic stops.

Dependencies:
  - LeanFzn.Solver.Propagation.RestorationCertificate (and through it
    `AnalysisProgress`, `LcgAnalyzer`).
-/

import LeanFzn.Solver.Propagation.RestorationCertificate

open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The transition trace

`analyzeTrace` records how many transitions the loop takes before it stops,
and `none` when the fuel runs out first. It is the instrument that separates
"stopped" from "cut off by the fuel". -/

/-- Number of transitions performed, and the result, when the loop stops
within `fuel`; `none` when the fuel is exhausted first. -/
def analyzeTrace (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    Nat → AnalyzerState → Option (Nat × Option (List (Literal × Nat) × Literal))
  | 0, _ => none
  | fuel + 1, st =>
      match analyzeNext orig trail lvl st with
      | .done r => some (1, r)
      | .next st' =>
          match analyzeTrace orig trail lvl fuel st' with
          | none => none
          | some (k, r) => some (k + 1, r)

/-- One step of the trace, with the recursive call's fuel exposed. -/
theorem analyzeTrace_succ (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) (fuel : Nat)
    (st : AnalyzerState) :
    analyzeTrace orig trail lvl (fuel + 1) st =
      (match analyzeNext orig trail lvl st with
       | .done res => some (1, res)
       | .next s =>
           match analyzeTrace orig trail lvl fuel s with
           | none => none
           | some (k, r) => some (k + 1, r)) := by
  simp only [analyzeTrace]

/-- The trace's result IS the loop's result. -/
theorem analyzeTrace_snd (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace orig trail lvl fuel st = some (k, r) →
    analyzeLoop orig trail lvl fuel st = r := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext orig trail lvl st with
      | done res => simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    simp [analyzeLoop, hn]
      | next st' =>
          cases ht : analyzeTrace orig trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              simp only [analyzeLoop, hn]
              exact ih st' k' r' ht

/-- The trace never overruns its fuel. -/
theorem analyzeTrace_steps_le (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace orig trail lvl fuel st = some (k, r) → k ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext orig trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          omega
      | next st' =>
          cases ht : analyzeTrace orig trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              have hk := ih st' k' r' ht
              omega

/-- The trace is monotone in the fuel, so a stopped run stays stopped. -/
theorem analyzeTrace_mono (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (st : AnalyzerState) (k : Nat)
      (r : Option (List (Literal × Nat) × Literal)),
    analyzeTrace orig trail lvl fuel st = some (k, r) →
    analyzeTrace orig trail lvl (fuel + 1) st = some (k, r) := by
  intro fuel
  induction fuel with
  | zero => intro st k r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro st k r h
      cases hn : analyzeNext orig trail lvl st with
      | done res =>
          simp only [analyzeTrace, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [analyzeTrace, hn]
      | next st' =>
          cases ht : analyzeTrace orig trail lvl fuel st' with
          | none => simp [analyzeTrace, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have ht' := ih st' k' r' ht
              rw [analyzeTrace_succ, hn]
              dsimp only
              rw [ht']

/-! ## No exhaustion -/

/-- Fuel above the potential always observes a semantic stop. -/
theorem analyzeTrace_exists_of_potential (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) : ∀ (fuel : Nat) (st : AnalyzerState),
    analyzerPotential trail st < fuel →
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace orig trail lvl fuel st = some (k, r) := by
  intro fuel
  induction fuel with
  | zero => intro st h; omega
  | succ fuel ih =>
      intro st hpot
      cases hn : analyzeNext orig trail lvl st with
      | done r => exact ⟨1, r, by simp only [analyzeTrace, hn]⟩
      | next st' =>
          have hlt := analyzerPotential_lt_of_next hn
          obtain ⟨k, r, hk⟩ := ih st' (by omega)
          exact ⟨k + 1, r, by rw [analyzeTrace_succ, hn]; dsimp only; rw [hk]⟩

/-- THE NO-EXHAUSTION THEOREM (R1a: unconditional): the executable allowance
cannot be exhausted, on any input. -/
theorem analysis_complete (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) :
    ∃ (k : Nat) (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, r) :=
  analyzeTrace_exists_of_potential orig trail lvl _ _ (Nat.lt_succ_self _)

/-- A completed trace at fuel `k` is the loop at exactly `k` fuel. -/
theorem analyzeTrace_loop_at_steps {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} :
    ∀ (fuel k : Nat) (st : AnalyzerState)
      (r : Option (List (Literal × Nat) × Literal)),
      analyzeTrace orig trail lvl fuel st = some (k, r) →
      analyzeLoop orig trail lvl k st = r := by
  intro fuel
  induction fuel with
  | zero => intro k st r h; simp [analyzeTrace] at h
  | succ fuel ih =>
      intro k st r h
      cases hn : analyzeNext orig trail lvl st with
      | done res =>
          simp only [analyzeTrace_succ, hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [analyzeLoop, hn]
      | next st' =>
          cases ht : analyzeTrace orig trail lvl fuel st' with
          | none => simp [analyzeTrace_succ, hn, ht] at h
          | some kr =>
              obtain ⟨k', r'⟩ := kr
              simp only [analyzeTrace_succ, hn, ht, Option.some.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ih k' st' r' ht
              simp only [analyzeLoop, hn]
              exact this

/-- The executable analysis STOPS on every input: its result is reached by a
completed trace of `k ≤ analysisFuel` transitions. -/
theorem analyzeAtAllowance_stops (orig : List Domain) (trail : List TrailEntry)
    (lvl : Nat) (c : Clause) :
    ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, analyzeAtAllowance orig trail lvl c) ∧
      analyzeLoop orig trail lvl k (initAnalysisState c)
        = analyzeAtAllowance orig trail lvl c := by
  obtain ⟨k, r, hk⟩ := analysis_complete orig trail lvl c
  have hle := analyzeTrace_steps_le orig trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk
  have hloop := analyzeTrace_loop_at_steps (analysisFuel trail c) k
    (initAnalysisState c) r hk
  have hsnd := analyzeTrace_snd orig trail lvl (analysisFuel trail c)
    (initAnalysisState c) k r hk
  have hres : r = analyzeAtAllowance orig trail lvl c := hsnd.symm
  subst hres
  exact ⟨k, hle, hk, hloop⟩

/-- `analyzeClassified` reports `.success` exactly when the analyzer returned
a result. -/
theorem analyzeClassified_eq_success_iff_of_allowance {orig : List Domain}
    {trail : List TrailEntry} {lvl : Nat} {c : Clause}
    {below : List (Literal × Nat)} {uip : Literal} :
    analyzeClassified orig trail lvl c = .success below uip ↔
      analyzeAtAllowance orig trail lvl c = some (below, uip) := by
  unfold analyzeClassified
  cases h : analyzeAtAllowance orig trail lvl c with
  | some p =>
      obtain ⟨b, u⟩ := p
      simp
  | none =>
      by_cases h0 : lvl = 0 <;> simp [h0]

/-- SEMANTIC `unsupported`, not truncation. -/
theorem analyzeClassified_unsupported_iff {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} :
    analyzeClassified orig trail lvl c = .unsupported ↔
      analyzeAtAllowance orig trail lvl c = none ∧ lvl ≠ 0 := by
  unfold analyzeClassified
  cases h : analyzeAtAllowance orig trail lvl c with
  | some p =>
      obtain ⟨b, u⟩ := p
      simp
  | none =>
      by_cases h0 : lvl = 0 <;> simp [h0]

/-- The `.unsupported` verdict comes with a COMPLETED trace that stops in
`none` inside the executable allowance. -/
theorem analyzeClassified_unsupported_trace {orig : List Domain} (c : Clause)
    {trail : List TrailEntry} {lvl : Nat}
    (huns : analyzeClassified orig trail lvl c = .unsupported) :
    lvl ≠ 0 ∧ ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace orig trail lvl (analysisFuel trail c) (initAnalysisState c)
        = some (k, none) := by
  obtain ⟨hnone, hlvl⟩ := analyzeClassified_unsupported_iff.mp huns
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops orig trail lvl c
  exact ⟨hlvl, k, hk, by rw [hnone] at htr; exact htr⟩

/-- The `.rootContradiction` verdict likewise comes from a completed trace
that stops in `none` at level 0. -/
theorem analyzeClassified_root_trace {orig : List Domain} (c : Clause)
    {trail : List TrailEntry}
    (hroot : analyzeClassified orig trail 0 c = .rootContradiction) :
    ∃ k, k ≤ analysisFuel trail c ∧
      analyzeTrace orig trail 0 (analysisFuel trail c) (initAnalysisState c)
        = some (k, none) := by
  obtain ⟨k, hk, htr, -⟩ := analyzeAtAllowance_stops orig trail 0 c
  have hnone : analyzeAtAllowance orig trail 0 c = none := by
    unfold analyzeClassified at hroot
    cases h : analyzeAtAllowance orig trail 0 c with
    | some p => simp [h] at hroot
    | none => rfl
  exact ⟨k, hk, by rw [hnone] at htr; exact htr⟩

/-! ### Instantiation on reachable branch states -/

/-- `ReachableState` supplies the trail discipline. -/
theorem analyzerTrailOk_of_reachable {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) : AnalyzerTrailOk bs.trail :=
  ⟨h.distinct, h.wf.2.1⟩

/-- Every initial analyzer state is in the reachable class (R1a: no premise). -/
theorem analyzerReachable_init (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : AnalyzerReachable orig trail lvl c (initAnalysisState c) :=
  AnalyzerReachable.init

/-- `ReachableState` also supplies the SUPPORTED INPUT discipline of
`AnalyzerInput`. -/
def analyzerInput_of_supported {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    (_h : ReachableState leaf orig bs) (hne : 1 ≤ c.length)
    (hent : LearnedEntailed leaf [c]) (hfals : FalsifiedByTrail bs c) :
    AnalyzerInput leaf bs :=
  ⟨c, hne, hent, hfals⟩

/-! ### Worked example: semantic weakening at the executable allowance

Four level-1 decisions `x3 ≤ 0, x3 ≤ 1, x3 ≤ 2, x3 ≤ 3` and a level-2
implication whose reason has the side literals `x3 > 0 … x3 > 3`. The
EARLIEST entry implying each `x3 ≤ k` is the decision `x3 ≤ 0`, so all four
side literals are learnt as the single weakened literal `x3 > 0`. -/

private def exDec (l : Literal) (lv : Nat) : TrailEntry :=
  { literal := l, level := lv, reason := none }

private def exImp (l : Literal) (lv : Nat) (cl : Clause) : TrailEntry :=
  { literal := l, level := lv, reason := some { clause := cl } }

private def exTrail : List TrailEntry :=
  [ exDec (posLe 3 0) 1, exDec (posLe 3 1) 1, exDec (posLe 3 2) 1,
    exDec (posLe 3 3) 1, exDec (posLe 1 5) 2,
    exImp (posLe 2 3) 2
      [posLe 2 3, negLe 3 0, negLe 3 1, negLe 3 2, negLe 3 3] ]

private def exConflict : Clause := [negLe 2 3, negLe 1 5]

/-- Four integer slots with domain `0..9`. -/
private def exOrig : List Domain :=
  List.replicate 4 ((List.range 10).map fun i => Value.int (Int.ofNat i))

/-- The analysis of the fixture: one weakened below-level literal and the
level-2 decision as the first UIP. -/
example : analyzeAtAllowance exOrig exTrail 2 exConflict
    = some ([(negLe 3 0, 1)], posLe 1 5) := by decide

/-- The same run as a completed trace: eleven transitions. -/
example : analyzeTrace exOrig exTrail 2 (analysisFuel exTrail exConflict)
    (initAnalysisState exConflict) = some (11, some ([(negLe 3 0, 1)], posLe 1 5)) := by
  decide

end LeanFzn.Solver.Propagation
