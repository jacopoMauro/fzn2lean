/-
Purpose: Character-class and maximal-run correspondence for the executable lexer.
Dependencies: Independent Lexical classes and the array character-suffix view.
DAG: Lexical + LexerSuffix -> scans -> numeral, word and trivia proofs.
-/
import LeanFzn.Parser.Lexical
import LeanFzn.Parser.Proofs.LexerSuffix

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

theorem space_iff_whitespace (c : Char) : Space c ↔ isWhitespace c = true := by
  simp [Space, isWhitespace, or_assoc]

theorem space_of_whitespace (c : Char) (h : isWhitespace c = true) : Space c :=
  (space_iff_whitespace c).mpr h

theorem whitespace_of_space (c : Char) (h : Space c) : isWhitespace c = true :=
  (space_iff_whitespace c).mp h

theorem decimal_iff_digit (c : Char) : Decimal c ↔ isDigit c = true := by
  simp [Decimal, isDigit]

theorem decimal_raw (c : Char) (h : isDigit c = true) : Decimal c :=
  (decimal_iff_digit c).mpr h

theorem isDigit_of_decimal (c : Char) (h : Decimal c) : isDigit c = true :=
  (decimal_iff_digit c).mp h

theorem letter_iff_alpha (c : Char) : Letter c ↔ isAlpha c = true := by
  simp [Letter, isAlpha]

theorem letter_raw (c : Char) (h : isAlpha c = true) : Letter c :=
  (letter_iff_alpha c).mpr h

theorem isAlpha_of_letter (c : Char) (h : Letter c) : isAlpha c = true :=
  (letter_iff_alpha c).mp h

theorem wordStart_iff_identStart (c : Char) : WordStart c ↔ (isAlpha c || c == '_') = true := by
  simp [WordStart, ← letter_iff_alpha]

theorem wordStart_of_identStart (c : Char) (h : (isAlpha c || c == '_') = true) : WordStart c :=
  (wordStart_iff_identStart c).mpr h

theorem identStart_of_wordStart (c : Char) (h : WordStart c) : (isAlpha c || c == '_') = true :=
  (wordStart_iff_identStart c).mp h

theorem wordContinue_iff_identChar (c : Char) : WordContinue c ↔ isIdentChar c = true := by
  simp [WordContinue, WordStart, isIdentChar, ← letter_iff_alpha, ← decimal_iff_digit,
    or_assoc, or_left_comm, or_comm]

/-- A successful maximal run consumes exactly a prefix of the input suffix. -/
theorem takeWhile_spec (p : Char → Bool) (s : Array Char) (pos : Nat) (acc : String)
    (hpos : pos ≤ s.size) :
    ∃ ds : List Char,
      (takeWhile p s pos acc).1.toList = acc.toList ++ ds ∧
      Suffix.toList s pos = ds ++ Suffix.toList s (takeWhile p s pos acc).2 ∧
      (∀ c ∈ ds, p c = true) ∧
      Boundary (fun c => p c = true) (Suffix.toList s (takeWhile p s pos acc).2) ∧
      (takeWhile p s pos acc).2 ≤ s.size := by
  induction pos, acc using takeWhile.induct (p := p) (s := s) with
  | case1 pos acc hi c hp ih =>
    have he : takeWhile p s pos acc = takeWhile p s (pos+1) (acc.push c) := by
      rw [takeWhile.eq_def]
      simp only [c] at hp
      simp only [hi, dite_true, hp, ite_true]
      rfl
    obtain ⟨ds, hstr, hsuffix, hall, hboundary, hbound⟩ := ih (by omega)
    refine ⟨c :: ds, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]
      simpa [String.toList_push, List.append_assoc] using hstr
    · rw [he, Suffix.toList_getElem s pos hi, hsuffix]
      rfl
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact hall x hx
    · simpa only [he] using hboundary
    · simpa only [he] using hbound
  | case2 pos acc hi c hp =>
    have he : takeWhile p s pos acc = (acc,pos) := by
      rw [takeWhile.eq_def]
      simp only [c] at hp
      simp only [hi, dite_true, hp, Bool.false_eq_true, ite_false]
    rw [he]
    refine ⟨[], by simp, by simp, by simp, ?_, hpos⟩
    simpa [Suffix.toList_getElem s pos hi, Boundary] using hp
  | case3 pos acc hi =>
    have he : takeWhile p s pos acc = (acc,pos) := by
      rw [takeWhile.eq_def]
      simp only [hi, dite_false]
    rw [he]
    refine ⟨[], by simp, by simp, by simp, ?_, hpos⟩
    rw [(Suffix.toList_eq_nil_iff s pos).mpr (by omega)]
    trivial

/-- Scanner completeness for a supplied maximal prefix. -/
theorem takeWhile_complete (p : Char → Bool) (s : Array Char) (pos : Nat) (acc : String)
    (ds rest : List Char) (hs : Suffix.toList s pos = ds ++ rest)
    (hall : ∀ c ∈ ds, p c = true)
    (hb : Boundary (fun c => p c = true) rest) (hpos : pos ≤ s.size) :
    takeWhile p s pos acc = (acc ++ String.ofList ds, pos + ds.length) ∧
      Suffix.toList s (pos + ds.length) = rest := by
  induction ds generalizing pos acc with
  | nil =>
    have hs : Suffix.toList s pos = rest := by simpa using hs
    by_cases hi : pos < s.size
    · have hp : p s[pos] ≠ true := by
        simpa [← hs, Suffix.toList_getElem s pos hi, Boundary] using hb
      constructor
      · rw [takeWhile.eq_def]
        simp [hi, hp]
      · simpa using hs
    · constructor
      · rw [takeWhile.eq_def]
        simp [hi]
      · simpa using hs
  | cons c ds ih =>
    have hi : pos < s.size := by
      have hl := congrArg List.length hs
      rw [Suffix.toList_size] at hl
      simp only [List.length_cons, List.length_append] at hl
      omega
    have hhead : s[pos] = c := by
      have hx := hs
      rw [Suffix.toList_getElem s pos hi] at hx
      exact (List.cons.inj hx).1
    have htail : Suffix.toList s (pos + 1) = ds ++ rest := by
      have hx := hs
      rw [Suffix.toList_getElem s pos hi, hhead] at hx
      exact (List.cons.inj hx).2
    obtain ⟨hrun, hrest⟩ := ih (pos + 1) (acc.push c) htail
      (fun d hd => hall d (List.mem_cons_of_mem c hd)) (by omega)
    constructor
    · rw [takeWhile.eq_def]
      simp only [hi, dite_true, hhead, hall c List.mem_cons_self, ite_true]
      rw [hrun]
      simp only [String.ofList_cons, String.push_eq_append, String.append_assoc,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

end LeanFzn.Parser.Lexer
