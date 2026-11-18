/-
Purpose: Prove numeral values and numeric scanner correspondence with the
independent positional Digits/Magnitude relations.
Dependencies: Lexical and the executable lexer, with character suffix bridges.
DAG: scans + positional numeral arithmetic -> numeric lexing -> token dispatch.
-/
import LeanFzn.Parser.Lexical
import LeanFzn.Parser.Proofs.LexerSuffix
import Init.Data.String.Lemmas.Iterate

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

macro "digit_omega" : tactic => `(tactic| (simp only [
  show ('0' : Char).toNat = 48 from rfl, show ('7' : Char).toNat = 55 from rfl,
  show ('9' : Char).toNat = 57 from rfl, show ('A' : Char).toNat = 65 from rfl,
  show ('F' : Char).toNat = 70 from rfl, show ('a' : Char).toNat = 97 from rfl,
  show ('f' : Char).toNat = 102 from rfl] at *; omega))

private theorem char_le_nat (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl

/-- Independent digit values uniquely agree with the executable decoder. -/
theorem digitValue_of_digit {base : Nat} {c : Char} {d : Nat} (h : Digit base c d) :
    digitValue c = d := by
  rcases h with ⟨_, h | h | h⟩
  · rcases h with ⟨⟨hl, hu⟩, rfl⟩
    simp [digitValue, isDigit, hl, hu]
  · rcases h with ⟨hl, hu, rfl⟩
    have hn : isDigit c = false := by
      simp only [isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      intro he
      have := char_le_nat 'A' c |>.mp hl
      have := char_le_nat c '9' |>.mp he
      digit_omega
    simp [digitValue, hn, hl, hu]
  · rcases h with ⟨hl, hu, rfl⟩
    have hn : isDigit c = false := by
      simp only [isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      intro he
      have := char_le_nat 'a' c |>.mp hl
      have := char_le_nat c '9' |>.mp he
      digit_omega
    have hA : ¬ c ≤ 'F' := by
      intro he
      have := char_le_nat 'a' c |>.mp hl
      have := char_le_nat c 'F' |>.mp he
      digit_omega
    simp [digitValue, hn, hA]

/-- A digit's code-point windows identify the corresponding scanner class. -/
theorem baseDigit10_iff (c : Char) : BaseDigit 10 c ↔ isDigit c = true := by
  constructor
  · rintro ⟨d, hd, h | h | h⟩
    · exact by simpa [isDigit, Decimal, Bool.and_eq_true, decide_eq_true_iff] using h.1
    · rcases h with ⟨hl, hu, hv⟩
      have := (char_le_nat 'A' c).mp hl
      digit_omega
    · rcases h with ⟨hl, hu, hv⟩
      have := (char_le_nat 'a' c).mp hl
      digit_omega
  · intro h
    have hc : Decimal c := by simpa [isDigit, Decimal, Bool.and_eq_true, decide_eq_true_iff] using h
    refine ⟨c.toNat - '0'.toNat, ?_, Or.inl ⟨hc, rfl⟩⟩
    have hl := (char_le_nat '0' c).mp hc.1
    have hu := (char_le_nat c '9').mp hc.2
    digit_omega

theorem baseDigit16_iff (c : Char) : BaseDigit 16 c ↔ isHexDigit c = true := by
  constructor
  · rintro ⟨d, _, h | h | h⟩
    · simp [isHexDigit, isDigit, h.1.1, h.1.2]
    · simp [isHexDigit, h.1, h.2.1]
    · simp [isHexDigit, h.1, h.2.1]
  · intro h
    simp only [isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
    rcases h with (h | ⟨hl, hu⟩) | ⟨hl, hu⟩
    · obtain ⟨d, hd, hv⟩ := (baseDigit10_iff c).mpr h
      exact ⟨d, Nat.lt_trans hd (by decide), hv⟩
    · refine ⟨c.toNat - 'A'.toNat + 10, ?_, Or.inr (Or.inl ⟨hl, hu, rfl⟩)⟩
      have := (char_le_nat 'A' c).mp hl
      have := (char_le_nat c 'F').mp hu
      digit_omega
    · refine ⟨c.toNat - 'a'.toNat + 10, ?_, Or.inr (Or.inr ⟨hl, hu, rfl⟩)⟩
      have := (char_le_nat 'a' c).mp hl
      have := (char_le_nat c 'f').mp hu
      digit_omega

theorem baseDigit8_iff (c : Char) : BaseDigit 8 c ↔ isOctDigit c = true := by
  constructor
  · rintro ⟨d, hd, h | h | h⟩
    · rcases h with ⟨⟨hl, hu⟩, hv⟩
      have hn := (char_le_nat '0' c).mp hl
      have h7 : c ≤ '7' := by
        apply (char_le_nat c '7').mpr
        digit_omega
      simp [isOctDigit, hl, h7]
    · have := (char_le_nat 'A' c).mp h.1
      have := h.2.2
      digit_omega
    · have := (char_le_nat 'a' c).mp h.1
      have := h.2.2
      digit_omega
  · intro h
    simp only [isOctDigit, Bool.and_eq_true, decide_eq_true_iff] at h
    have hn := (char_le_nat '0' c).mp h.1
    have hn' := (char_le_nat c '7').mp h.2
    refine ⟨c.toNat - '0'.toNat, ?_, Or.inl ⟨⟨h.1, ?_⟩, rfl⟩⟩
    · digit_omega
    · apply (char_le_nat c '9').mpr
      digit_omega

theorem digits_foldl {base : Nat} {cs : List Char} {n : Nat}
    (h : Digits base cs n) (acc : Nat) :
    cs.foldl (fun k c => k * base + digitValue c) acc = acc * base ^ cs.length + n := by
  induction h generalizing acc with
  | nil => simp
  | @cons c d cs n hd ht ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [digitValue_of_digit hd, ih]
      simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem parseNatBase_of_digits {base : Nat} {cs : List Char} {n : Nat}
    (h : Digits base cs n) : parseNatBase base (String.ofList cs) = n := by
  unfold parseNatBase
  rw [String.foldl_eq_foldl_toList, String.toList_ofList, digits_foldl h]
  simp

/-- Every finite list of valid base digits has a positional numeral value. -/
theorem digits_of_all {base : Nat} {cs : List Char}
    (h : ∀ c ∈ cs, BaseDigit base c) : ∃ n, Digits base cs n := by
  induction cs with
  | nil => exact ⟨0, .nil⟩
  | cons c cs ih =>
      obtain ⟨d, hd⟩ := h c (by simp)
      obtain ⟨n, hn⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨_, .cons hd hn⟩

end LeanFzn.Parser.Lexer
