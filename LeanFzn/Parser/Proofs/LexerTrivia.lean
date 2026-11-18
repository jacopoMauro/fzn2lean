/-
Purpose: Exact comment/whitespace correspondence and canonical trivia skipping.
Dependencies: LexerScan's character classes and array suffix bridge.
DAG: LexerScan -> LexerTrivia -> whole-input lexical soundness/completeness.
-/
import LeanFzn.Parser.Proofs.LexerScan

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

/-- The remaining suffix is empty or begins with a significant character. -/
def SignificantOrEnd : List Char → Prop
  | [] => True
  | c :: _ => ¬ Space c ∧ c ≠ '%'

theorem skipToNewline_le (s : Array Char) (pos : Nat) (hp : pos ≤ s.size) :
    skipToNewline s pos ≤ s.size := by
  induction pos using skipToNewline.induct (s := s) with
  | case1 pos hi hn =>
    rw [skipToNewline.eq_def]
    simp only [hi, dite_true, hn, ite_true]
    omega
  | case2 pos hi hn ih =>
    rw [skipToNewline.eq_def]
    simp only [hi, dite_true, hn, Bool.false_eq_true, ite_false]
    exact ih (by omega)
  | case3 pos hi =>
    rw [skipToNewline.eq_def]
    simp only [hi, dite_false]
    exact hp

/-- A comment body ends either at EOF or immediately after its first LF. -/
theorem skipToNewline_spec (s : Array Char) (pos : Nat) (hp : pos ≤ s.size) :
    ∃ body : List Char, (∀ c ∈ body, c ≠ '\n') ∧
      ((Suffix.toList s pos = body ∧ skipToNewline s pos = s.size) ∨
       Suffix.toList s pos = body ++ '\n' :: Suffix.toList s (skipToNewline s pos)) := by
  induction pos using skipToNewline.induct (s := s) with
  | case1 pos hi hn =>
    have hc : s[pos] = '\n' := by simpa using hn
    have he : skipToNewline s pos = pos + 1 := by
      rw [skipToNewline.eq_def]
      simp only [hi, dite_true, hn, ite_true]
    refine ⟨[], by simp, Or.inr ?_⟩
    simpa [he, hc] using Suffix.toList_getElem s pos hi
  | case2 pos hi hn ih =>
    have hc : s[pos] ≠ '\n' := by simpa using hn
    have he : skipToNewline s pos = skipToNewline s (pos + 1) := by
      rw [skipToNewline.eq_def]
      simp only [hi, dite_true, hn, Bool.false_eq_true, ite_false]
    obtain ⟨body, hbody, hshape⟩ := ih (by omega)
    refine ⟨s[pos] :: body, ?_, ?_⟩
    · intro c hc'
      rcases List.mem_cons.mp hc' with rfl | hm
      · exact hc
      · exact hbody c hm
    · rcases hshape with ⟨hs, hq⟩ | hs
      · left
        exact ⟨by rw [Suffix.toList_getElem s pos hi, hs], by rw [he, hq]⟩
      · right
        rw [Suffix.toList_getElem s pos hi, hs, he]
        rfl
  | case3 pos hi =>
    have heq : pos = s.size := by omega
    refine ⟨[], by simp, Or.inl ?_⟩
    constructor
    · exact (Suffix.toList_eq_nil_iff s pos).mpr (by omega)
    · rw [skipToNewline.eq_def]
      simp [hi, heq]

/-- First-LF completeness, preserving the exact suffix after the LF. -/
theorem skipToNewline_complete_line (s : Array Char) (pos : Nat)
    (body tail : List Char) (hs : Suffix.toList s pos = body ++ '\n' :: tail)
    (hb : ∀ c ∈ body, c ≠ '\n') :
    skipToNewline s pos = pos + body.length + 1 ∧
      Suffix.toList s (pos + body.length + 1) = tail := by
  induction body generalizing pos with
  | nil =>
    obtain ⟨hi, hc, ht⟩ := Suffix.cons_inv hs
    constructor
    · rw [skipToNewline.eq_def]
      simp [hi, hc]
    · simpa using ht
  | cons c body ih =>
    obtain ⟨hi, hc, ht⟩ := Suffix.cons_inv hs
    obtain ⟨hq, hsuf⟩ := ih (pos + 1) ht (fun d hd => hb d (List.mem_cons_of_mem c hd))
    constructor
    · rw [skipToNewline.eq_def]
      simp only [hi, dite_true, hc, show (c == '\n') = false by simpa using hb c List.mem_cons_self,
        Bool.false_eq_true, ite_false]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsuf

/-- A final comment with no LF consumes exactly to EOF. -/
theorem skipToNewline_complete_eof (s : Array Char) (pos : Nat)
    (body : List Char) (hs : Suffix.toList s pos = body)
    (hb : ∀ c ∈ body, c ≠ '\n') (hp : pos ≤ s.size) :
    skipToNewline s pos = s.size := by
  induction body generalizing pos with
  | nil =>
    have heq : pos = s.size := by
      have := (Suffix.toList_eq_nil_iff s pos).mp hs
      omega
    rw [skipToNewline.eq_def]
    simp [heq]
  | cons c body ih =>
    obtain ⟨hi, hc, ht⟩ := Suffix.cons_inv hs
    have hq := ih (pos + 1) ht (fun d hd => hb d (List.mem_cons_of_mem c hd)) (by omega)
    rw [skipToNewline.eq_def]
    simpa only [hi, dite_true, hc,
      show (c == '\n') = false by simpa using hb c List.mem_cons_self,
      Bool.false_eq_true, ite_false] using hq

/-- The actual scanner returns a canonical independent trivia suffix. -/
theorem skipTrivia_spec (s : Array Char) (pos : Nat) (hp : pos ≤ s.size) :
    skipTrivia s pos ≤ s.size ∧
      Trivia (Suffix.toList s pos) (Suffix.toList s (skipTrivia s pos)) ∧
      SignificantOrEnd (Suffix.toList s (skipTrivia s pos)) := by
  induction pos using skipTrivia.induct (s := s) with
  | case1 pos hi c hw ih =>
    simp only [c] at hw
    have he : skipTrivia s pos = skipTrivia s (pos + 1) := by
      rw [skipTrivia.eq_def]
      simp only [hi, dite_true, hw, ite_true]
    obtain ⟨hq, ht, hc⟩ := ih (by omega)
    refine ⟨by simpa [he] using hq, ?_, by simpa [he] using hc⟩
    rw [he, Suffix.toList_getElem s pos hi]
    exact .space (space_of_whitespace c hw) ht
  | case2 pos hi c hw hc ih =>
    simp only [c] at hw hc
    have he : skipTrivia s pos = skipTrivia s (skipToNewline s (pos + 1)) := by
      rw [skipTrivia.eq_def]
      simp only [hi, dite_true, hw, Bool.false_eq_true, ite_false, hc, ite_true]
    have hbound := skipToNewline_le s (pos+1) (by omega)
    obtain ⟨hq, ht, hcan⟩ := ih hbound
    refine ⟨by simpa [he] using hq, ?_, by simpa [he] using hcan⟩
    have hchar : s[pos] = '%' := by simpa [c] using hc
    rw [he, Suffix.toList_getElem s pos hi, hchar]
    obtain ⟨body, hbody, hshape⟩ := skipToNewline_spec s (pos+1) (by omega)
    rcases hshape with ⟨hs, hsiz⟩ | hs
    · have hend : skipTrivia s (skipToNewline s (pos+1)) = s.size := by
        have hg := skipTrivia_ge s (skipToNewline s (pos+1))
        omega
      rw [hs, hend, (Suffix.toList_eq_nil_iff s s.size).mpr (by omega)]
      exact .commentEOF hbody
    · rw [hs]
      exact .commentLine hbody ht
  | case3 pos hi c hw hc =>
    simp only [c] at hw hc
    have he : skipTrivia s pos = pos := by
      rw [skipTrivia.eq_def]
      simp only [hi, dite_true, hw, Bool.false_eq_true, ite_false, hc, ite_false]
    refine ⟨by simpa [he] using hp, by rw [he]; exact .refl, ?_⟩
    rw [he, Suffix.toList_getElem s pos hi]
    exact ⟨fun hs => hw (whitespace_of_space _ hs), by simpa using hc⟩
  | case4 pos hi =>
    have he : skipTrivia s pos = pos := by
      rw [skipTrivia.eq_def]
      simp [hi]
    refine ⟨by simpa [he] using hp, by rw [he]; exact .refl, ?_⟩
    rw [he, (Suffix.toList_eq_nil_iff s pos).mpr (by omega)]
    trivial

/-- Every independent trivia derivation ending at a significant suffix is
recognized by the scanner; partial trivia witnesses are intentionally excluded. -/
theorem skipTrivia_complete {cs rest : List Char} (ht : Trivia cs rest)
    (hcan : SignificantOrEnd rest) (s : Array Char) (pos : Nat)
    (hp : pos ≤ s.size) (hs : Suffix.toList s pos = cs) :
    Suffix.toList s (skipTrivia s pos) = rest := by
  induction ht generalizing pos with
  | refl =>
    have he : skipTrivia s pos = pos := by
      by_cases hi : pos < s.size
      · have hc := hcan
        rw [← hs, Suffix.toList_getElem s pos hi] at hc
        have hw : isWhitespace s[pos] = false := by
          simpa [space_iff_whitespace] using hc.1
        have hpct : (s[pos] == '%') = false := by simpa using hc.2
        rw [skipTrivia.eq_def]
        simp [hi, hw, hpct]
      · rw [skipTrivia.eq_def]
        simp [hi]
    simpa [he] using hs
  | space hc ht ih =>
    obtain ⟨hi, hhead, htail⟩ := Suffix.cons_inv hs
    have hrec := ih hcan (pos + 1) (by omega) htail
    have hw : isWhitespace s[pos] = true := by rw [hhead]; exact whitespace_of_space _ hc
    rw [skipTrivia.eq_def]
    simpa only [hi, dite_true, hw, ite_true] using hrec
  | commentLine hb ht ih =>
    obtain ⟨hi, hhead, htail⟩ := Suffix.cons_inv hs
    obtain ⟨hq, hqtail⟩ := skipToNewline_complete_line s (pos+1) _ _ htail hb
    have hbound := skipToNewline_le s (pos+1) (by omega)
    have hrec := ih hcan (skipToNewline s (pos+1)) hbound (by simpa [hq] using hqtail)
    rw [skipTrivia.eq_def]
    simpa [hi, hhead, isWhitespace] using hrec
  | commentEOF hb =>
    obtain ⟨hi, hhead, htail⟩ := Suffix.cons_inv hs
    have hq := skipToNewline_complete_eof s (pos+1) _ htail hb (by omega)
    have hend : skipTrivia s s.size = s.size := by rw [skipTrivia.eq_def]; simp
    rw [skipTrivia.eq_def]
    simp only [hi, dite_true, hhead, isWhitespace, beq_self_eq_true,
      Bool.false_or, Bool.false_eq_true, ite_false, ite_true, hq, hend]
    exact (Suffix.toList_eq_nil_iff s s.size).mpr (by omega)

private theorem wordStart_significant {c : Char} (h : WordStart c) (rest : List Char) :
    SignificantOrEnd (c :: rest) := by
  constructor
  · intro hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp_all [WordStart, Letter]
  · intro hc
    subst c
    simp_all [WordStart, Letter]

private theorem decimal_significant {c : Char} (h : Decimal c) (rest : List Char) :
    SignificantOrEnd (c :: rest) := by
  constructor
  · intro hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp_all [Decimal]
  · intro hc
    subst c
    simp_all [Decimal]

private theorem digit10_decimal {c : Char} {d : Nat} (h : Digit 10 c d) : Decimal c := by
  rcases h.2 with hdec | hupper | hlower
  · exact hdec.1
  · have := h.1; omega
  · have := h.1; omega

private theorem magnitude_significant {cs rest : List Char} {n : Nat}
    (h : Magnitude cs n rest) : SignificantOrEnd cs := by
  cases h with
  | decimal hne hd hstop hp =>
    cases hd with
    | nil => contradiction
    | cons hc ht => exact decimal_significant (digit10_decimal hc) _
  | hex => exact decimal_significant (by unfold Decimal; decide) _
  | octal => exact decimal_significant (by unfold Decimal; decide) _

/-- Significant lexical units cannot leave whitespace or '%' as their head.
This is independent of all implementation-success assumptions. -/
theorem lexeme_significant {cs rest : List Char} {tok : Token}
    (h : Lexeme cs tok rest) : SignificantOrEnd cs := by
  cases h with
  | punctuation hp =>
    have hm : _ ∈ Punctuation.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hp
    simp [Punctuation] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp [SignificantOrEnd, Space])
  | colon => simp [SignificantOrEnd, Space]
  | colonColon => simp [SignificantOrEnd, Space]
  | dotDot => simp [SignificantOrEnd, Space]
  | word hstart => exact wordStart_significant hstart _
  | natural hm => exact magnitude_significant hm
  | negative => simp [SignificantOrEnd, Space]
  | string => simp [SignificantOrEnd, Space]

theorem magnitude_nonempty {cs rest : List Char} {n : Nat}
    (h : Magnitude cs n rest) : cs ≠ [] := by
  cases h with
  | decimal hne =>
    intro hnil
    exact hne (List.append_eq_nil_iff.mp hnil).1
  | hex => simp
  | octal => simp

theorem lexeme_nonempty {cs rest : List Char} {tok : Token}
    (h : Lexeme cs tok rest) : cs ≠ [] := by
  cases h with
  | natural hm => exact magnitude_nonempty hm
  | word => simp
  | punctuation => simp
  | colon => simp
  | colonColon => simp
  | dotDot => simp
  | negative => simp
  | string => simp

end LeanFzn.Parser.Lexer
