/-
Purpose: Lift arbitrary-accumulator string correspondence to the actual
quote branch of lexToken, preserving the parent-position subtype and suffix.
Dependencies: LexerStrings and the frozen significant-token interface.
DAG: Strings -> this local dispatch branch -> LexerStep -> whole stream.
-/
import LeanFzn.Parser.Proofs.LexerStrings
import LeanFzn.Parser.Proofs.LexerStepTarget

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

theorem lexToken_string_sound {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {tok : Token} {q : Nat} {hq : pos < q} (hc : s[pos] = '"')
    (h : lexToken s pos hi = .ok (tok, ⟨q,hq⟩)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size := by
  unfold lexToken at h
  simp only [hc] at h
  cases hs : lexString s (pos + 1) .empty with
  | error err => simp [hs] at h
  | ok result =>
    rcases result with ⟨value, ⟨p,hp⟩⟩
    simp only [hs] at h
    cases h
    obtain ⟨hb, bytes, hbody, hu⟩ := lexString_sound s (pos + 1) .empty value q hp hs
    refine ⟨?_, hb⟩
    rw [Suffix.toList_getElem s pos hi, hc]
    exact .string hbody (by simpa using hu)

theorem lexToken_string_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {input : List Char} {bytes : List UInt8} {rest : List Char} {value : String}
    (hs : Suffix.toList s pos = '"' :: input)
    (hbody : StringBody input bytes rest) (hu : EncodesUTF8 bytes value) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (.stringLit value, ⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨_, hc, ht⟩ := Suffix.cons_inv hs
  have hbody' : StringBody (Suffix.toList s (pos + 1)) bytes rest := ht ▸ hbody
  have hu' : EncodesUTF8 (ByteArray.empty.data.toList ++ bytes) value := by simpa using hu
  obtain ⟨q, hq, hr, hb, htail⟩ := lexString_complete hbody' hu'
  refine ⟨q, by omega, ?_, htail, hb⟩
  unfold lexToken
  simp only [hc, hr]

end LeanFzn.Parser.Lexer
