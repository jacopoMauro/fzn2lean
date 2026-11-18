/-
Purpose: Quoted-string soundness and completeness with arbitrary accumulated
byte prefixes; validity is required only for the final decoded byte sequence.
Dependencies: Exact escape and UTF-8 correspondence, independent StringBody.
DAG: Escapes + UTF8 -> Strings -> significant-token and stream correctness.
-/
import LeanFzn.Parser.Proofs.LexerEscapes
import LeanFzn.Parser.Proofs.LexerUTF8

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

/-- Soundness generalized to arbitrary byte accumulators, including partial
multibyte prefixes which are not themselves valid UTF-8. -/
theorem lexString_sound (s : Array Char) (pos : Nat) (acc : ByteArray) :
    ∀ (value : String) (q : Nat) (hq : pos < q),
    lexString s pos acc = .ok (value, ⟨q, hq⟩) →
    q ≤ s.size ∧ ∃ bytes,
      StringBody (Suffix.toList s pos) bytes (Suffix.toList s q) ∧
      EncodesUTF8 (acc.data.toList ++ bytes) value := by
  induction pos, acc using lexString.induct (s := s) with
  | case1 pos acc hp c hc str hu =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp only [hp, dif_pos, hc, ite_true, hu] at hr
    cases hr
    refine ⟨by omega, [], ?_, ?_⟩
    · rw [Suffix.toList_getElem s pos hp, show s[pos] = '"' from beq_iff_eq.mp hc]
      exact .close
    · simpa using (fromUTF8?_eq_some_iff_encodes acc str).mp hu
  | case2 pos acc hp c hc hu =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp [hp, hc, hu] at hr
  | case3 pos acc hp c hn hc b p hps he str out hpo hs ih =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp only [hp, dif_pos, hn, ite_false, hc, ite_true, he, hs] at hr
    cases hr
    obtain ⟨hbound, bytes, hbody, hutf⟩ := ih str out hpo hs
    obtain ⟨_, hescape⟩ := lexEscape_sound he
    refine ⟨hbound, b :: bytes, ?_, ?_⟩
    · rw [Suffix.toList_getElem s pos hp, show s[pos] = '\\' from beq_iff_eq.mp hc]
      exact .escape hescape hbody
    · simpa [ByteArray.data_push, Array.toList_push, List.append_assoc] using hutf
  | case4 pos acc hp c hn hc b p hps he err hs ih =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp [hp, hn, hc, he, hs] at hr
  | case5 pos acc hp c hn hc he =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp [hp, hn, hc, he] at hr
  | case6 pos acc hp c hn hc hbr =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp [hp, hn, hc, hbr] at hr
  | case7 pos acc hp c hn hc hbr str out hpo hs ih =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp only [hp, dif_pos, hn, ite_false, hc, hbr, hs] at hr
    cases hr
    obtain ⟨hbound, bytes, hbody, hutf⟩ := ih str out hpo hs
    have hquote : s[pos] ≠ '"' := by simpa only [beq_iff_eq] using hn
    have hslash : s[pos] ≠ '\\' := by simpa only [beq_iff_eq] using hc
    have hline : s[pos] ≠ '\n' ∧ s[pos] ≠ '\r' := by
      simpa only [Bool.or_eq_true, beq_iff_eq, not_or] using hbr
    refine ⟨hbound, (String.singleton s[pos]).toUTF8.data.toList ++ bytes, ?_, ?_⟩
    · rw [Suffix.toList_getElem s pos hp]
      exact .plain hquote hslash hline.1 hline.2 hbody
    · simpa [ByteArray.toList_data_append, List.append_assoc] using hutf
  | case8 pos acc hp c hn hc hbr err hs ih =>
    dsimp only [c] at *
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp only [hp, dif_pos, hn, ite_false, hc, hbr, hs] at hr
    cases hr
  | case9 pos acc hp =>
    intro value q hq hr
    rw [lexString.eq_def] at hr
    simp [hp] at hr

/-- Completeness by a string-body derivation; accumulators may end in an
unfinished multibyte sequence. Only the complete bytes must encode value. -/
theorem lexString_complete_body {input : List Char} {bytes : List UInt8} {rest : List Char}
    (hbody : StringBody input bytes rest) :
    ∀ (s : Array Char) (pos : Nat) (acc : ByteArray),
    Suffix.toList s pos = input → ∀ (value : String),
    EncodesUTF8 (acc.data.toList ++ bytes) value →
    ∃ (q : Nat) (hq : pos < q), lexString s pos acc = .ok (value, ⟨q, hq⟩) ∧
      q ≤ s.size ∧ Suffix.toList s q = rest := by
  induction hbody with
  | close =>
    intro s pos acc he value hu
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    have hdecode : String.fromUTF8? acc = some value :=
      (fromUTF8?_eq_some_iff_encodes acc value).mpr (by simpa using hu)
    refine ⟨pos + 1, by omega, ?_, by omega, ht⟩
    rw [lexString.eq_def]
    simp [hp, hc, hdecode]
  | @plain c cs bytes rest hquote hslash hlf hcr hbody ih =>
    intro s pos acc he value hu
    obtain ⟨hp, hc, ht⟩ := suffix_cons he
    have hu' : EncodesUTF8 ((acc ++ (String.singleton c).toUTF8).data.toList ++ bytes) value := by
      simpa only [ByteArray.toList_data_append, List.append_assoc] using hu
    obtain ⟨q, hq, hr, hb, htail⟩ := ih s (pos + 1) (acc ++ (String.singleton c).toUTF8) ht value hu'
    have hnq : ¬ (c == '\"') = true := by simpa only [beq_iff_eq] using hquote
    have hns : ¬ (c == '\\') = true := by simpa only [beq_iff_eq] using hslash
    have hnl : ¬ (c == '\n' || c == '\r') = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq, not_or] using And.intro hlf hcr
    refine ⟨q, by omega, ?_, hb, htail⟩
    rw [lexString.eq_def]
    simp only [hp, dif_pos, hc, hnq, Bool.false_eq_true, ite_false, hns, hnl, hr]
  | @escape cs b tail bytes rest he hbody ih =>
    intro s pos acc hs value hu
    obtain ⟨hp, hc, ht⟩ := suffix_cons hs
    have he' : Escape (Suffix.toList s (pos + 1)) b tail := ht ▸ he
    obtain ⟨p, hpp, hescape, hpbound, hptail⟩ := lexEscape_complete he'
    have hu' : EncodesUTF8 ((acc.push b).data.toList ++ bytes) value := by
      simpa only [ByteArray.data_push, Array.toList_push, List.append_assoc, List.singleton_append] using hu
    obtain ⟨q, hq, hr, hb, htail⟩ := ih s p (acc.push b) hptail value hu'
    refine ⟨q, by omega, ?_, hb, htail⟩
    rw [lexString.eq_def]
    simp only [hp, dif_pos, hc, Char.reduceBEq, Bool.false_eq_true, ite_false, ite_true, hescape, hr]

theorem lexString_complete {s : Array Char} {pos : Nat} {acc : ByteArray}
    {bytes : List UInt8} {rest : List Char} {value : String}
    (hbody : StringBody (Suffix.toList s pos) bytes rest)
    (hu : EncodesUTF8 (acc.data.toList ++ bytes) value) :
    ∃ (q : Nat) (hq : pos < q), lexString s pos acc = .ok (value, ⟨q, hq⟩) ∧
      q ≤ s.size ∧ Suffix.toList s q = rest :=
  lexString_complete_body hbody s pos acc rfl value hu

end LeanFzn.Parser.Lexer
