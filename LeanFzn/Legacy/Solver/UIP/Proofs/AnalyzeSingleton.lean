/-
File: LeanFzn/Solver/UIP/Proofs/AnalyzeSingleton.lean

Purpose: the N1 analyzer fact on the LCG analyzer (R1a). A UNIT conflict
clause `[q]` analyzed by `analyzeAtAllowance` can only succeed through a
CURRENT-level mark: the root-drop, level-0 and below-level outcomes of
`markLitAt` leave the mark set empty, and pivot selection on the empty mark
set stops with `none`. Consequently the analyzed `below` list is ALWAYS empty
for a singleton input, and the UIP is the literal of a current-level trail
entry that IMPLIES `¬q` (semantic falsifier, `impliesP`).

  §1 the work-empty helpers;
  §2 `analyzeAtAllowance_singleton_uip` — the shape theorem, and its
     corollary `analyzeAtAllowance_singleton_below`;
  §3 `learnedEntailed_singleton_run` — entailment transport: if `q` holds at
     every leaf solution, so does the learned singleton `[(uip.negate).norm]`
     (`impliesP_negate_sound`).

NO `sorry`, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.Propagation.AnalysisInvariants
import LeanFzn.Legacy.Solver.Propagation.AnalysisCompletion
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Work-empty helpers -/

/-- With nothing to scan and nothing marked, the analysis stops with `none`. -/
theorem analyzeLoop_workNil_noMarks {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st : AnalyzerState} (hw : st.work = []) (hm : st.marks = []) :
    ∀ fuel, analyzeLoop orig trail lvl fuel st = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f =>
      obtain ⟨work, skip, bound, marks, learnt⟩ := st
      simp only at hw hm
      subst hw hm
      simp [analyzeLoop, analyzeNext]

/-- With nothing to scan and the single mark `i`, the analysis returns the
learnt list and the literal of entry `i`. -/
theorem analyzeLoop_workNil_singleMark {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {st : AnalyzerState} {i : Nat} {e : TrailEntry}
    (hw : st.work = []) (hm : st.marks = [i]) (he : trail[i]? = some e)
    {r : List (Literal × Nat) × Literal} :
    ∀ fuel, analyzeLoop orig trail lvl fuel st = some r → r = (st.learnt, e.literal) := by
  intro fuel h
  cases fuel with
  | zero => simp [analyzeLoop] at h
  | succ f =>
      obtain ⟨work, skip, bound, marks, learnt⟩ := st
      simp only at hw hm
      subst hw hm
      simp [analyzeLoop, analyzeNext, he] at h
      exact h.symm

/-! ## §2 The singleton shape -/

/-- **THE SINGLETON ANALYSIS SHAPE**: a successful `analyzeAtAllowance` run on
`[q]` has an EMPTY below list, and its UIP is the literal of a trail entry at
the analysis level that implies the negation of the scanned literal. -/
theorem analyzeAtAllowance_singleton_uip {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {q : Literal} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl [q] = some (below, uip)) :
    below = [] ∧ ∃ e ∈ trail, e.level = lvl ∧
      impliesP orig e.literal q.norm.norm.negate.norm = true ∧ uip = e.literal := by
  unfold analyzeAtAllowance at h
  generalize analysisFuel trail [q] = fuel at h
  cases fuel with
  | zero => simp [analyzeLoop] at h
  | succ f₁ =>
      cases hmk : markLitAt orig trail lvl none [] [] q.norm with
      | none =>
          simp [analyzeLoop, analyzeNext, initAnalysisState, skipEq, hmk] at h
      | some mp =>
          obtain ⟨m', l'⟩ := mp
          have h1 : analyzeLoop orig trail lvl f₁
              { work := [[]], skip := none, bound := none, marks := m', learnt := l' }
              = some (below, uip) := by
            simpa [analyzeLoop, analyzeNext, initAnalysisState, skipEq, hmk] using h
          cases f₁ with
          | zero => simp [analyzeLoop] at h1
          | succ f₂ =>
              have h2 : analyzeLoop orig trail lvl f₂
                  { work := [], skip := none, bound := none, marks := m', learnt := l' }
                  = some (below, uip) := by
                simpa [analyzeLoop, analyzeNext] using h1
              rcases markLitAt_spec hmk with ⟨-, rfl, rfl⟩ | ⟨i, e, he, hp, -, hcase⟩
              · rw [analyzeLoop_workNil_noMarks rfl rfl] at h2; cases h2
              · rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hlv, -, hm', hi, rfl⟩ |
                  ⟨-, -, rfl, -⟩
                · rw [analyzeLoop_workNil_noMarks rfl rfl] at h2; cases h2
                · have hmi : m' = [i] := by
                    rcases hm' with rfl | rfl
                    · cases hi
                    · rfl
                  subst hmi
                  have hr := analyzeLoop_workNil_singleMark rfl rfl he f₂ h2
                  simp only [Prod.mk.injEq] at hr
                  exact ⟨hr.1, e, List.mem_of_getElem? he, hlv, hp, hr.2⟩
                · rw [analyzeLoop_workNil_noMarks rfl rfl] at h2; cases h2

/-- **N1 `analyzeAtAllowance_singleton_below`**: a singleton conflict clause's
analysis never records a below-level falsifier. -/
theorem analyzeAtAllowance_singleton_below {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {q : Literal} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl [q] = some (below, uip)) : below = [] :=
  (analyzeAtAllowance_singleton_uip h).1

/-! ## §3 Entailment transport -/

/-- THE ENTAILMENT TRANSPORT across the singleton analysis: if the scanned
literal `q` holds at every leaf solution, so does the analyzed singleton
clause `[(uip.negate).norm]` — the UIP's literal implies `¬q`, so it is FALSE
wherever `q` is true (`impliesP_negate_sound`). -/
theorem learnedEntailed_singleton_run {leaf : Assignment → Bool} {orig : List Domain}
    {q uip : Literal} (hfit : ∀ a, leaf a = true → a.Fits orig)
    (hqent : ∀ a, leaf a = true → q.eval a = some true)
    (huip : ∃ e : TrailEntry, impliesP orig e.literal q.norm.norm.negate.norm = true ∧
      uip = e.literal) :
    LearnedEntailed leaf [[(uip.negate).norm]] := by
  obtain ⟨e, hp, rfl⟩ := huip
  intro c hc a hleaf
  rw [List.mem_singleton] at hc
  rw [hc]
  refine ⟨(e.literal.negate).norm, List.mem_singleton_self _, ?_⟩
  have hq : q.norm.norm.eval a = some true := by
    rw [Literal.norm_eval, Literal.norm_eval]; exact hqent a hleaf
  rw [Literal.norm_eval, Literal.eval_negate_false_iff]
  exact impliesP_negate_sound hp (hfit a hleaf) hq

/-- The Boolean regression instance: a `boolEq` conflict's singleton analysis
over a Boolean original domain returns the empty below-list. -/
example :
    analyzeAtAllowance [Dom.ofList [.bool false, .bool true]]
      [{ literal := posBool 0 true, level := 1, reason := none }] 1
      [posBool 0 false] = some ([], posBool 0 true) := by decide

end LeanFzn.Solver.UIP
