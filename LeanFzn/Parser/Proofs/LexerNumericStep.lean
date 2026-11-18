/-
Purpose: Numeric lexeme branches of significant-token correspondence.
Dependencies: Numeric scanner proofs and the character-suffix adapter.
DAG: LexerNumbers -> numeric token-step helpers -> LexerStep.
-/
import LeanFzn.Parser.Proofs.LexerNumbers

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

theorem lexToken_number_sound {s : Array Char} {pos : Nat} (hi : pos < s.size)
    (hnum : (isDigit s[pos] || s[pos] == '-') = true)
    {tok : Token} {q : Nat} {hq : pos < q}
    (hres : lexToken s pos hi = .ok (tok,⟨q,hq⟩)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size := by
  rw [lexToken_of_numeric s pos hi hnum] at hres
  exact lexInt_sound (by omega) hres

theorem lexToken_natural_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {input rest : List Char} {n : Nat} (hs : Suffix.toList s pos = input)
    (hm : Magnitude input n rest) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (.intLit (n : Int),⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨c,cs,hc,hdigit⟩ := magnitude_starts_digit hm
  obtain ⟨_,hhead,_⟩ := Suffix.cons_inv (hs.trans hc)
  have hd : isDigit s[pos] = true := by simpa only [hhead] using hdigit
  obtain ⟨q,hq,ht,hb⟩ := lexInt_natural_complete hs hm (by omega)
  refine ⟨q.val,q.property,?_,ht,hb⟩
  rw [lexToken_of_numeric s pos hi (by simp only [hd,Bool.true_or])]
  exact hq

theorem lexToken_negative_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {input rest : List Char} {n : Nat} (hs : Suffix.toList s pos = '-' :: input)
    (hm : Magnitude input n rest) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (.intLit (-(n : Int)),⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨_,hhead,_⟩ := Suffix.cons_inv hs
  obtain ⟨q,hq,ht,hb⟩ := lexInt_negative_complete hs hm (by omega)
  refine ⟨q.val,q.property,?_,ht,hb⟩
  rw [lexToken_of_numeric s pos hi (by simp [hhead])]
  exact hq

end LeanFzn.Parser.Lexer
