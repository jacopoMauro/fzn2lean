/-
Purpose: Prove that removing FlatZinc status separators preserves every emitted
assignment line; legal identifiers cannot be mistaken for a status marker.
Dependencies: Runtime.Solution for stripping and the exact line classifier,
SolutionRender for token spelling, and standard string splitting lemmas. The
emitter round-trip proof uses these lemmas without changing the runtime parser
dependency graph.
DAG: solution runtime + token renderer -> this proof -> Emit.RoundTrip.
-/
import LeanFzn.Checker.Runtime.Solution
import LeanFzn.Parser.SolutionRender
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

namespace LeanFzn.Checker.Solution
open LeanFzn.Parser.Lexer

/-! ## Trimming and head preservation

The classifier trims ASCII spaces/tabs on both ends and one trailing `\r`.
A rendered assignment line starts with an identifier character, which is
none of those, so trimming preserves its head.  The four lemmas below
carry that head through `trimStatusEnds`, `dropOneTrailingCR`, and
`trimStatusLine`. -/

theorem getLast?_dropWhile_append_singleton {α : Type} {p : α → Bool}
    {xs : List α} {c : α} (hc : p c = false) :
    (List.dropWhile p (xs ++ [c])).getLast? = some c := by
  induction xs with
  | nil =>
      simp only [List.nil_append, List.dropWhile_cons, hc, Bool.false_eq_true, ite_false]
      rfl
  | cons x xs ih =>
      rw [List.cons_append, List.dropWhile_cons]
      split
      · exact ih
      · have hlast : (xs ++ [c]).getLast? = some c := by simp
        simp only [List.getLast?_cons, hlast]
        rfl

theorem head?_trimStatusEnds_cons (c : Char) (cs : List Char)
    (h1 : c ≠ ' ') (h2 : c ≠ '\t') :
    (trimStatusEnds (c :: cs)).head? = some c := by
  unfold trimStatusEnds
  rw [List.dropWhile_cons_of_neg (by simp [isStatusSpace, h1, h2])]
  rw [List.head?_reverse, List.reverse_cons]
  exact getLast?_dropWhile_append_singleton (by simp [isStatusSpace, h1, h2])

theorem head?_dropOneTrailingCR_cons (c : Char) (cs : List Char)
    (h : c ≠ '\r') :
    (dropOneTrailingCR (c :: cs)).head? = some c := by
  unfold dropOneTrailingCR
  split
  · rename_i hlast
    rw [List.head?_dropLast]
    split
    · rfl
    · rename_i hlen
      have hcs : cs = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hlen
      subst hcs
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact (h hlast).elim
  · rfl

theorem head?_trimStatusLine_cons (c : Char) (cs : List Char)
    (h1 : c ≠ ' ') (h2 : c ≠ '\t') (h3 : c ≠ '\r') :
    (trimStatusLine (String.ofList (c :: cs))).toList.head? = some c := by
  unfold trimStatusLine
  simp only [String.toList_ofList]
  have hdrop := head?_dropOneTrailingCR_cons c cs h3
  cases hd : dropOneTrailingCR (c :: cs) with
  | nil => simp [hd] at hdrop
  | cons d ds =>
      have hdc : d = c := by simpa [hd] using hdrop
      rw [hdc]
      exact head?_trimStatusEnds_cons c ds h1 h2

theorem startsWith_percent_eq_false {t : String} {c : Char}
    (hhead : t.toList.head? = some c) (hc : c ≠ '%') :
    t.startsWith "%" = false := by
  apply String.startsWith_string_eq_false_iff.mpr
  rintro ⟨tail, htail⟩
  have hh := congrArg List.head? htail
  simp [hhead] at hh
  exact hc hh.symm

theorem startsWith_eq_eq_false {t : String} {c : Char}
    (hhead : t.toList.head? = some c) (hc : c ≠ '=') :
    t.startsWith "=" = false := by
  apply String.startsWith_string_eq_false_iff.mpr
  rintro ⟨tail, htail⟩
  have hh := congrArg List.head? htail
  simp [hhead] at hh
  exact hc hh.symm

theorem ne_separator_of_head {t : String} {c : Char}
    (hhead : t.toList.head? = some c) (hc : c ≠ '-') :
    t ≠ "----------" := by
  intro h
  have := congrArg String.toList h
  have hh := congrArg List.head? this
  simp [hhead] at hh
  exact hc hh

theorem isEmpty_eq_false_of_head {t : String} {c : Char}
    (hhead : t.toList.head? = some c) : t.isEmpty = false := by
  cases h : t.isEmpty with
  | false => rfl
  | true =>
      have hempty : t = "" := String.isEmpty_iff.mp h
      subst hempty
      simp at hhead

theorem alpha_or_underscore_ne_special (c : Char)
    (h : (isAlpha c || c == '_') = true) :
    c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\r' ∧ c ≠ '-' ∧ c ≠ '=' ∧ c ≠ '%' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro hc <;> subst hc <;> simp [isAlpha] at h

/-- A canonically rendered assignment line (starting with an identifier)
    is `content`: it is nonempty, is not a comment, and cannot equal or
    start a status marker. -/
theorem classify_renderSolutionTokens_ident {name : String} {ts : List Token}
    (hn : PrintableSolutionName name) :
    classifySolutionLine (renderSolutionTokens (.ident name :: ts)) = .content := by
  obtain ⟨⟨c, cs, hname, halpha, _⟩, _⟩ := hn
  obtain ⟨hspace, htab, hcr, hminus, heq, hpercent⟩ :=
    alpha_or_underscore_ne_special c halpha
  have hrender : (renderSolutionTokens (.ident name :: ts)).toList =
      c :: (cs ++ ' ' :: (renderSolutionTokens ts).toList) := by
    simp [renderSolutionTokens, renderSolutionToken, hname, String.toList_append]
  have hstr : renderSolutionTokens (.ident name :: ts) =
      String.ofList (c :: (cs ++ ' ' :: (renderSolutionTokens ts).toList)) :=
    String.toList_injective (by simpa using hrender)
  have hhead : (trimStatusLine (renderSolutionTokens (.ident name :: ts))).toList.head? =
      some c := by
    rw [hstr]
    exact head?_trimStatusLine_cons c (cs ++ ' ' :: (renderSolutionTokens ts).toList)
      hspace htab hcr
  have hnonempty := isEmpty_eq_false_of_head hhead
  have hp := startsWith_percent_eq_false hhead hpercent
  have hsep := ne_separator_of_head hhead hminus
  have heqs := startsWith_eq_eq_false hhead heq
  unfold classifySolutionLine
  simp [hnonempty, hp, hsep, heqs]

/-- A rendered assignment line is never stripped as a separator or
    optimum marker. -/
theorem renderSolutionTokens_ident_notStatus {name : String} {ts : List Token}
    (hn : PrintableSolutionName name) :
    isStrippableSeparator (renderSolutionTokens (.ident name :: ts)) = false := by
  have hcontent := classify_renderSolutionTokens_ident (name := name) (ts := ts) hn
  simp [isStrippableSeparator, hcontent]

/-! ## Stripping a rendered block -/

theorem stripSeparators_intercalate (lines : List String)
    (hn : ∀ l ∈ lines, '\n' ∉ l.toList)
    (hk : ∀ l ∈ lines, isStrippableSeparator l = false) :
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
  have hfilter : lines.filter (fun l => !isStrippableSeparator l) = lines := by
    apply List.filter_eq_self.mpr
    intro l hl
    simp [hk l hl]
  rw [hfilter]
  have hsep : isStrippableSeparator "----------" = true := by
    have htrim : trimStatusLine "----------" = "----------" := by
      apply String.toList_injective
      simp [trimStatusLine, trimStatusEnds, dropOneTrailingCR, isStatusSpace]
    have hclass : classifySolutionLine "----------" = .solutionSeparator := by
      simp [classifySolutionLine, htrim, String.isEmpty_iff]
    simp [isStrippableSeparator, hclass]
  simp [hsep]

/-- The exact newline/separator layout used by `emitCertifiedSolution`. -/
theorem stripSeparators_terminated (lines : List String)
    (hn : ∀ l ∈ lines, '\n' ∉ l.toList)
    (hk : ∀ l ∈ lines, isStrippableSeparator l = false) :
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

end LeanFzn.Checker.Solution
