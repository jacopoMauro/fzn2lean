/-
Purpose: Kernel-checked soundness and completeness of solution parsing against
an independent grammar, including values and complete token consumption.
Dependencies: SolutionGrammar gives the declarative language; Runtime.Solution
gives the parser. This bridge is used by checker correctness and emitter proofs.
DAG: SolutionGrammar + Runtime.Solution -> Proofs.SolutionParser -> checker proofs.
-/
import LeanFzn.Checker.Runtime.Solution

namespace LeanFzn.Checker.Solution
open LeanFzn.Parser LeanFzn.Parser.Lexer LeanFzn.Semantics

set_option linter.unusedSimpArgs false

@[simp] theorem parseSolTerminator_eq_ok_iff {t term} :
    parseSolTerminator t = .ok term ↔ t = term.token := by
  cases t <;> cases term <;> simp [parseSolTerminator, SolTerminator.token]

 theorem parseSolSetTail_sound {toks is out}
    (h : parseSolSetTail toks = .ok (is, out)) : GrSolSetTail toks is out := by
  fun_induction parseSolSetTail toks generalizing is out
  all_goals try contradiction
  case case1 rest =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .empty
  case case2 i rest =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .singleton
  case case3 i j rest js out hp ih =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .cons (ih hp)

 theorem parseSolSetTail_complete {toks is out}
    (h : GrSolSetTail toks is out) : parseSolSetTail toks = .ok (is, out) := by
  induction h with
  | empty => rfl
  | singleton => rfl
  | cons h ih => simp [parseSolSetTail, ih]

 theorem parseSolLiteral_complete {toks l term out}
    (h : GrSolLiteral toks l term out) : parseSolLiteral toks = .ok (l, term, out) := by
  cases h with
  | bool => cases term <;> rfl
  | int => cases term <;> rfl
  | range => cases term <;> rfl
  | set h =>
      simp only [parseSolLiteral, parseSolSetTail_complete h, Bind.bind, Except.bind]
      cases term <;> rfl

 theorem parseSolLiteral_sound {toks l term out}
    (h : parseSolLiteral toks = .ok (l, term, out)) : GrSolLiteral toks l term out := by
  unfold parseSolLiteral at h
  split at h
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
  all_goals try contradiction
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  all_goals
    have ht := parseSolTerminator_eq_ok_iff.mp (by assumption)
    cases ht
  all_goals first | exact .bool | exact .range | exact .int | skip
  apply GrSolLiteral.set
  have hs := parseSolSetTail_sound (by assumption)
  simpa only [*] using hs

 theorem parseSolArrayItems_sound {toks ls out}
    (h : parseSolArrayItems toks = .ok (ls, out)) : GrSolArrayItems toks ls out := by
  fun_induction parseSolArrayItems toks generalizing ls out
  all_goals try contradiction
  case case1 toks l rest hp =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .last (parseSolLiteral_sound hp)
  case case2 toks l rest hp ls' out' hparse ih =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .cons (parseSolLiteral_sound hp) (ih hparse)

 theorem parseSolArrayItems_complete {toks ls out}
    (h : GrSolArrayItems toks ls out) : parseSolArrayItems toks = .ok (ls, out) := by
  induction h with
  | last hl => rw [parseSolArrayItems, parseSolLiteral_complete hl]
  | cons hl _ ih => rw [parseSolArrayItems, parseSolLiteral_complete hl]; simp only [ih]

 theorem GrSolLiteral.ne_rBrack {toks l term out rest}
    (h : GrSolLiteral toks l term out) : toks ≠ .rBrack :: rest := by
  cases h <;> simp

 theorem GrSolArrayItems.ne_rBrack {toks ls out rest}
    (h : GrSolArrayItems toks ls out) : toks ≠ .rBrack :: rest := by
  cases h with
  | last hl => exact hl.ne_rBrack
  | cons hl _ => exact hl.ne_rBrack

 theorem parseSolArray_sound {toks ls out}
    (h : parseSolArray toks = .ok (ls, out)) : GrSolArray toks ls out := by
  unfold parseSolArray at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .empty
  · exact .items (parseSolArrayItems_sound h)

 theorem parseSolArray_complete {toks ls out}
    (h : GrSolArray toks ls out) : parseSolArray toks = .ok (ls, out) := by
  cases h with
  | empty => rfl
  | items h =>
      unfold parseSolArray
      split
      · exact False.elim (h.ne_rBrack rfl)
      · exact parseSolArrayItems_complete h

 theorem parseSolEntry_complete {toks e out}
    (h : GrSolEntry toks e out) : parseSolEntry toks = .ok (e, out) := by
  cases h with
  | scalar hl =>
      cases hl with
      | bool => rfl
      | int => rfl
      | range => rfl
      | set hs => simp [parseSolEntry, parseSolLiteral, parseSolSetTail_complete hs,
          parseSolTerminator, SolTerminator.token, Bind.bind, Except.bind]
  | array ha => simp [parseSolEntry, parseSolArray_complete ha, Bind.bind, Except.bind]
  | array1d ha hh => simp [parseSolEntry, parseSolArray_complete ha, hh, Bind.bind, Except.bind]

 theorem parseSolEntry_sound {toks e out}
    (h : parseSolEntry toks = .ok (e, out)) : GrSolEntry toks e out := by
  unfold parseSolEntry at h
  split at h
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
  all_goals try contradiction
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals try simp_all
  all_goals
    first
    | (apply GrSolEntry.array
       have hg := parseSolArray_sound (by assumption)
       simpa only [*] using hg)
    | (apply GrSolEntry.scalar
       have hg := parseSolLiteral_sound (by assumption)
       simpa only [*] using hg)
    | skip
  apply GrSolEntry.array1d
  · have hg := parseSolArray_sound (by assumption)
    simpa only [*] using hg
  · rfl

 theorem parseSolutionTokens_sound {toks es}
    (h : parseSolutionTokens toks = .ok es) : GrSolution toks es := by
  fun_induction parseSolutionTokens toks generalizing es
  all_goals try contradiction
  case case1 =>
    simp only [Except.ok.injEq] at h
    subst es
    exact .nil
  case case2 toks _ e rest he es' hp ih =>
    simp only [Except.ok.injEq] at h
    subst es
    exact .cons (parseSolEntry_sound he) (ih hp)

 theorem GrSolEntry.ne_nil {toks e rest} (h : GrSolEntry toks e rest) : toks ≠ [] := by
  cases h <;> simp

 theorem parseSolutionTokens_complete {toks es}
    (h : GrSolution toks es) : parseSolutionTokens toks = .ok es := by
  induction h with
  | nil => rw [parseSolutionTokens]
  | cons he hs ih =>
      have hne := he.ne_nil
      rw [parseSolutionTokens]
      · rw [parseSolEntry_complete he]
        simp only [ih]
      · exact hne

 theorem parseSolutionTokens_eq_ok_iff_grammar {toks es} :
    parseSolutionTokens toks = .ok es ↔ GrSolution toks es :=
  ⟨parseSolutionTokens_sound, parseSolutionTokens_complete⟩

/-- Value-sensitive solution parser characterization. The right-hand side
uses only tokenization and independent grammar derivations. -/
theorem parseSolution_eq_ok_iff_grammar {s es} :
    parseSolution s = .ok es ↔ SolutionGrammar s es := by
  cases ht : tokenize s with
  | error e => simp [parseSolution, SolutionGrammar, ht, Bind.bind, Except.bind]
  | ok toks => simp [parseSolution, SolutionGrammar, ht, Bind.bind, Except.bind,
      parseSolutionTokens_eq_ok_iff_grammar]

/-- Solution parsing succeeds exactly for the independently specified language. -/
theorem parseSolution_ok_iff_valid (s : String) :
    (∃ es, parseSolution s = .ok es) ↔ ValidSolution s := by
  simp only [parseSolution_eq_ok_iff_grammar, ValidSolution]

end LeanFzn.Checker.Solution
