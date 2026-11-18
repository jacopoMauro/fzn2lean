/-
Purpose: Significant-token correspondence with the independent lexical relation.
Dependencies: Proved scan, numeral, word and string correspondence branches.
DAG: Primitive scanner correctness -> this step certificate -> stream assembly.
-/
import LeanFzn.Parser.Proofs.LexerStepTarget
import LeanFzn.Parser.Proofs.LexerWords
import LeanFzn.Parser.Proofs.LexerNumericStep
import LeanFzn.Parser.Proofs.LexerStringStep

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

private theorem punc_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {c : Char} {tok : Token} {rest : List Char}
    (hs : Suffix.toList s pos = c::rest) (hp : (c,tok) ∈ Punctuation) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (tok,⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨hi',hhead,htail⟩ := Suffix.cons_inv hs
  simp only [Punctuation, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    refine ⟨pos+1, by omega, ?_, htail, by omega⟩ <;>
    (unfold lexToken; simp only [hhead]; rfl)

private theorem colon_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {rest : List Char} (hs : Suffix.toList s pos = ':'::rest)
    (hb : Boundary (fun c => c = ':') rest) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (.colon,⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨hi',hhead,htail⟩ := Suffix.cons_inv hs
  have hn : (decide (pos+1<s.size) && s[pos+1]! == ':') = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h
    obtain ⟨hj,hc⟩ := h
    have hb' : s[pos+1] ≠ ':' := by
      simpa [← htail, Suffix.toList_getElem s (pos+1) hj, Boundary] using hb
    rw [getElem!_pos s (pos+1) hj] at hc
    exact hb' hc
  refine ⟨pos+1, by omega, ?_, htail, by omega⟩
  unfold lexToken
  simp only [hhead, hn, Bool.false_eq_true, ite_false]
  rfl

private theorem double_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {c : Char} {rest : List Char} (hs : Suffix.toList s pos = c::c::rest)
    (hc : c = ':' ∨ c = '.') :
    ∃ (q : Nat) (hq : pos < q),
      lexToken s pos hi = .ok ((if c = ':' then .colonColon else .dotDot),⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  obtain ⟨hi',hhead,htail⟩ := Suffix.cons_inv hs
  obtain ⟨hj,hhead2,htail2⟩ := Suffix.cons_inv htail
  have hg : s[pos+1]! = c := by rw [getElem!_pos s (pos+1) hj]; exact hhead2
  refine ⟨pos+2, by omega, ?_, ?_, by omega⟩
  · rcases hc with rfl | rfl <;>
      (unfold lexToken; simp only [hhead, hg, hj, decide_true, beq_self_eq_true,
        Bool.true_and, ite_true]; rfl)
  · simpa [Nat.add_assoc] using htail2

/-- Every independent significant lexeme is recognized at the exact position. -/
theorem lexToken_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {tok : Token} {rest : List Char}
    (hl : Lexeme (Suffix.toList s pos) tok rest) :
    ∃ (q : Nat) (hq : pos < q), lexToken s pos hi = .ok (tok,⟨q,hq⟩) ∧
      Suffix.toList s q = rest ∧ q ≤ s.size := by
  generalize hs : Suffix.toList s pos = input at hl
  cases hl with
  | punctuation hp => exact punc_complete hi hs hp
  | colon hb => exact colon_complete hi hs hb
  | colonColon => simpa using double_complete hi hs (Or.inl rfl)
  | dotDot => simpa using double_complete hi hs (Or.inr rfl)
  | word hstart hall hb ht =>
    obtain ⟨hp, he, hr, hbound⟩ := lexToken_word_complete hi hs hstart hall hb ht
    exact ⟨_,hp,he,hr,hbound⟩
  | natural hm => exact lexToken_natural_complete hi hs hm
  | negative hm => exact lexToken_negative_complete hi hs hm
  | string hbody hu => exact lexToken_string_complete hi hs hbody hu

private theorem result_eq {pos p q : Nat} {hp : pos < p} {hq : pos < q}
    {t tok : Token}
    (h : (Except.ok (t,⟨p,hp⟩) : Except String (Token × {r : Nat // pos < r})) =
      .ok (tok,⟨q,hq⟩)) : tok = t ∧ q = p := by
  have he := Except.ok.inj h
  exact ⟨(congrArg Prod.fst he).symm, (congrArg (fun r => r.2.val) he).symm⟩

private theorem single_sound {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {t tok : Token} {q : Nat} {hq : pos < q}
    (hp : (s[pos],t) ∈ Punctuation)
    (h : (Except.ok (t,⟨pos+1,by omega⟩) : Except String (Token × {r : Nat // pos < r})) =
      .ok (tok,⟨q,hq⟩)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size := by
  obtain ⟨rfl,rfl⟩ := result_eq h
  refine ⟨?_, by omega⟩
  rw [Suffix.toList_getElem s pos hi]
  exact .punctuation hp

/-- Actual successful significant-token dispatch realizes the independent
lexeme and consumes no character beyond the input. -/
theorem lexToken_sound {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {tok : Token} {q : Nat} {hq : pos < q}
    (hres : lexToken s pos hi = .ok (tok,⟨q,hq⟩)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size := by
  by_cases hw : WordStart s[pos]
  · exact lexToken_word_sound hi rfl hw hres
  by_cases hn : (isDigit s[pos] || s[pos] == '-') = true
  · exact lexToken_number_sound hi hn hres
  by_cases hqchar : s[pos] = '"'
  · exact lexToken_string_sound hi hqchar hres
  have hw' : (isAlpha s[pos] || s[pos] == '_') = false :=
    Bool.eq_false_iff.mpr (fun h => hw ((wordStart_iff_identStart _).mpr h))
  have hn' : (isDigit s[pos] || s[pos] == '-') = false := Bool.eq_false_iff.mpr hn
  unfold lexToken at hres
  dsimp only at hres
  split at hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc => exact single_sound hi (by simp [hc,Punctuation]) hres
  next hc =>
    split at hres
    next hlook =>
      obtain ⟨rfl,rfl⟩ := result_eq hres
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hlook
      obtain ⟨hj,hnext⟩ := hlook
      rw [getElem!_pos s (pos+1) hj] at hnext
      refine ⟨?_,by omega⟩
      rw [Suffix.toList_getElem s pos hi, hc, Suffix.toList_getElem s (pos+1) hj, hnext]
      simpa [Nat.add_assoc] using (Lexeme.colonColon (rest := Suffix.toList s (pos+2)))
    next hlook =>
      obtain ⟨rfl,rfl⟩ := result_eq hres
      refine ⟨?_,by omega⟩
      rw [Suffix.toList_getElem s pos hi, hc]
      apply Lexeme.colon
      by_cases hj : pos+1<s.size
      · rw [Suffix.toList_getElem s (pos+1) hj]
        intro hnxt
        apply hlook
        simp [hj,getElem!_pos s (pos+1) hj,hnxt]
      · rw [(Suffix.toList_eq_nil_iff s (pos+1)).mpr (by omega)]
        trivial
  next hc =>
    split at hres
    next hlook =>
      obtain ⟨rfl,rfl⟩ := result_eq hres
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at hlook
      obtain ⟨hj,hnext⟩ := hlook
      rw [getElem!_pos s (pos+1) hj] at hnext
      refine ⟨?_,by omega⟩
      rw [Suffix.toList_getElem s pos hi, hc, Suffix.toList_getElem s (pos+1) hj, hnext]
      simpa [Nat.add_assoc] using (Lexeme.dotDot (rest := Suffix.toList s (pos+2)))
    next => cases hres
  next hc => exact (hqchar hc).elim
  next =>
    simp only [hw',hn',Bool.false_eq_true,ite_false] at hres
    cases hres

end LeanFzn.Parser.Lexer

namespace LeanFzn.Parser.Lexical
/-- The concrete, proved local certificate; no caller assumption is used. -/
theorem lexerStepCertification : LexerStepCertification :=
  ⟨fun _ _ hi _ _ _ h => Lexer.lexToken_sound hi h,
   fun _ _ hi _ _ h => Lexer.lexToken_complete hi h⟩
end LeanFzn.Parser.Lexical
