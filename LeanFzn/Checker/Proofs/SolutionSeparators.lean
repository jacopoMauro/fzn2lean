/-
Purpose: Prove that removing FlatZinc status separators preserves every emitted
assignment line; legal identifiers cannot be mistaken for a status marker.
Dependencies: Runtime.Solution for stripping, SolutionRender for token spelling,
and standard string splitting lemmas. The emitter round-trip proof uses these
lemmas without changing the runtime parser dependency graph.
DAG: solution runtime + token renderer -> this proof -> Emit.RoundTrip.
-/
import LeanFzn.Checker.Runtime.Solution
import LeanFzn.Parser.SolutionRender
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

namespace LeanFzn.Checker.Solution
open LeanFzn.Parser.Lexer

theorem stripSeparators_intercalate (lines : List String)
    (hn : ∀ l ∈ lines, '\n' ∉ l.toList)
    (hk : ∀ l ∈ lines,
      (l.startsWith "----------" || l.startsWith "==========") = false) :
    stripSeparators (String.intercalate "\n" (lines ++ ["----------"])) =
      String.intercalate "\n" lines := by
  have hsplit := String.toList_split_intercalate (c := '\n')
    (l := lines ++ ["----------"]) (by
      intro s hs
      rcases List.mem_append.mp hs with h | h
      · exact hn s h
      · simp only [List.mem_singleton] at h
        subst s
        decide)
  have hne : lines ++ ["----------"] ≠ [] := by simp
  simp only [hne, ite_false] at hsplit
  change ((String.intercalate "\n" (lines ++ ["----------"])).split '\n').toList.map
    String.Slice.copy = lines ++ ["----------"] at hsplit
  unfold stripSeparators
  rw [hsplit, List.filter_append]
  have hfilter : lines.filter (fun l =>
      !(l.startsWith "----------" || l.startsWith "==========")) = lines := by
    apply List.filter_eq_self.mpr
    intro l hl
    simp [hk l hl]
  rw [hfilter]
  simp

/-- The exact newline/separator layout used by `emitCertifiedSolution`. -/
theorem stripSeparators_terminated (lines : List String)
    (hn : ∀ l ∈ lines, '\n' ∉ l.toList)
    (hk : ∀ l ∈ lines,
      (l.startsWith "----------" || l.startsWith "==========") = false) :
    stripSeparators (String.intercalate "\n" lines ++
      (if lines.isEmpty then "" else "\n") ++ "----------") =
      String.intercalate "\n" lines := by
  have h := stripSeparators_intercalate lines hn hk
  cases lines with
  | nil => simpa using h
  | cons l ls =>
      have heq := String.intercalate_append_of_ne_nil
        (s := "\n") (l := l :: ls) (m := ["----------"]) (by simp) (by simp)
      rw [heq] at h
      simpa using h

theorem renderSolutionTokens_ident_notStatus {name : String} {ts : List Token}
    (hn : PrintableSolutionName name) :
    ((renderSolutionTokens (.ident name :: ts)).startsWith "----------" ||
      (renderSolutionTokens (.ident name :: ts)).startsWith "==========") = false := by
  obtain ⟨⟨c, cs, hc, hstart, _⟩, _⟩ := hn
  have hminus : c ≠ '-' := by
    intro h
    subst c
    simp [isAlpha] at hstart
  have hequals : c ≠ '=' := by
    intro h
    subst c
    simp [isAlpha] at hstart
  apply Bool.or_eq_false_iff.mpr
  constructor
  · apply String.startsWith_string_eq_false_iff.mpr
    rintro ⟨tail, ht⟩
    have hh := congrArg List.head? ht
    simp [renderSolutionTokens, renderSolutionToken, String.toList_append, hc] at hh
    exact hminus hh.symm
  · apply String.startsWith_string_eq_false_iff.mpr
    rintro ⟨tail, ht⟩
    have hh := congrArg List.head? ht
    simp [renderSolutionTokens, renderSolutionToken, String.toList_append, hc] at hh
    exact hequals hh.symm

end LeanFzn.Checker.Solution
