/-
Purpose: Independent keyword/reserved inventories agree with word dispatch.
Dependencies: Lexical's word relation and executable Lexer via LexerSuffix.
DAG: Token/spec + lexer -> word dispatch facts -> lexical step correctness.
-/
import LeanFzn.Parser.Lexical
import LeanFzn.Parser.Proofs.LexerSuffix
import LeanFzn.Parser.Proofs.LexerScan

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

theorem keywordToken_some_iff (w : String) (t : Token) :
    keywordToken w = some t ↔ (w, t) ∈ Keywords := by
  unfold keywordToken
  split <;> simp_all [Keywords, eq_comm]

theorem keywordToken_none_iff (w : String) :
    keywordToken w = none ↔ ∀ t, (w, t) ∉ Keywords := by
  cases hk : keywordToken w with
  | none =>
    constructor
    · intro _ t ht
      have hh := (keywordToken_some_iff w t).mpr ht
      rw [hk] at hh
      cases hh
    · intro _; rfl
  | some t =>
    constructor
    · intro h; cases h
    · intro h
      exact (h t ((keywordToken_some_iff w t).mp hk)).elim

theorem reserved_contains_iff (w : String) :
    reservedNonFzn.contains w = true ↔ w ∈ Reserved := by
  change Reserved.contains w = true ↔ w ∈ Reserved
  simp

theorem wordToken_keyword {cs : List Char} {t : Token}
    (h : keywordToken (String.ofList cs) = some t) : WordToken cs t :=
  .keyword ((keywordToken_some_iff _ _).mp h)

theorem wordToken_identifier {cs : List Char}
    (hk : keywordToken (String.ofList cs) = none)
    (hr : reservedNonFzn.contains (String.ofList cs) = false) :
    WordToken cs (.ident (String.ofList cs)) := by
  apply WordToken.identifier ((keywordToken_none_iff _).mp hk)
  intro hmem
  have hh := (reserved_contains_iff _).mpr hmem
  exact Bool.noConfusion (hr.symm.trans hh)

theorem wordToken_cases {cs : List Char} {t : Token} (h : WordToken cs t) :
    keywordToken (String.ofList cs) = some t ∨
      (t = .ident (String.ofList cs) ∧ keywordToken (String.ofList cs) = none ∧
        reservedNonFzn.contains (String.ofList cs) = false) := by
  cases h with
  | keyword hk => exact .inl ((keywordToken_some_iff _ _).mpr hk)
  | identifier hk hr =>
    apply Or.inr
    refine ⟨rfl, (keywordToken_none_iff _).mpr hk, ?_⟩
    cases hh : reservedNonFzn.contains (String.ofList cs) with
    | false => rfl
    | true => exact (hr ((reserved_contains_iff _).mp hh)).elim

end LeanFzn.Parser.Lexer

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

private theorem suffix_cons_inv {s : Array Char} {pos : Nat} {c : Char} {cs : List Char}
    (hs : Suffix.toList s pos = c :: cs) :
    ∃ hi : pos < s.size, s[pos] = c ∧ Suffix.toList s (pos+1) = cs := by
  have hi : pos < s.size := by
    have hl := congrArg List.length hs
    rw [Suffix.toList_size] at hl
    simp only [List.length_cons] at hl
    omega
  refine ⟨hi, ?_⟩
  rw [Suffix.toList_getElem s pos hi] at hs
  exact List.cons.inj hs

/-- A maximal word spelling is consumed with its specified keyword/identifier
value. This proof preserves the original scanner's exact character position. -/
theorem lexToken_word_complete {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {c : Char} {cs rest : List Char} {tok : Token}
    (hs : Suffix.toList s pos = (c :: cs) ++ rest)
    (hstart : WordStart c) (hall : ∀ d ∈ cs, WordContinue d)
    (hb : Boundary WordContinue rest) (ht : WordToken (c :: cs) tok) :
    ∃ hp : pos < pos+1+cs.length,
      lexToken s pos hi = .ok (tok, ⟨pos+1+cs.length, hp⟩) ∧
      Suffix.toList s (pos+1+cs.length) = rest ∧ pos+1+cs.length ≤ s.size := by
  obtain ⟨hi', hhead, htail⟩ := suffix_cons_inv hs
  have hboundary : Boundary (fun c => isIdentChar c = true) rest := by
    cases rest with
    | nil => trivial
    | cons x xs =>
      intro h
      exact hb ((wordContinue_iff_identChar x).mpr h)
  obtain ⟨hrun, hrest⟩ := takeWhile_complete isIdentChar s (pos+1) (String.singleton c)
    cs rest htail (fun d hd => (wordContinue_iff_identChar d).mp (hall d hd))
    hboundary (by omega)
  have hword : String.singleton c ++ String.ofList cs = String.ofList (c::cs) := by
    rw [String.ofList_cons]
  have hbound : pos+1+cs.length ≤ s.size := by
    have hl := congrArg List.length hs
    rw [Suffix.toList_size] at hl
    simp only [List.length_append, List.length_cons] at hl
    omega
  refine ⟨by omega, ?_, hrest, hbound⟩
  have hid := identStart_of_wordStart c hstart
  have hw := wordToken_cases ht
  unfold lexToken
  simp only [hhead]
  split <;> try {
    have hf : False := by simpa [isAlpha] using hid
    exact hf.elim }
  simp only [hid, ite_true, hrun, hword]
  rcases hw with hk | ⟨rfl, hk, hr⟩
  · simp only [hk]
    rfl
  · simp only [hk, hr, Bool.false_eq_true, ite_false]
    rfl

end LeanFzn.Parser.Lexer

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

/-- Successful executable word scanning gives a maximal independent word
lexeme, preserving the actual returned value and end position. -/
theorem lexToken_word_sound {s : Array Char} {pos : Nat} (hi : pos < s.size)
    {c : Char} (hhead : s[pos] = c) (hstart : WordStart c)
    {tok : Token} {q : Nat} {hq : pos < q}
    (hres : lexToken s pos hi = .ok (tok,⟨q,hq⟩)) :
    Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size := by
  obtain ⟨ds, hw, hs, hall, hb, hbound⟩ :=
    takeWhile_spec isIdentChar s (pos+1) (String.singleton c) (by omega)
  let p := (takeWhile isIdentChar s (pos+1) (String.singleton c)).2
  let w := String.ofList (c::ds)
  have hscan : takeWhile isIdentChar s (pos+1) (String.singleton c) = (w,p) := by
    apply Prod.ext
    · apply String.toList_inj.mp
      simpa [w, String.toList_singleton] using hw
    · rfl
  have hs' : Suffix.toList s pos = (c::ds) ++ Suffix.toList s p := by
    rw [Suffix.toList_getElem s pos hi, hhead, hs]
    rfl
  have hall' : ∀ x ∈ ds, WordContinue x := fun x hx =>
    (wordContinue_iff_identChar x).mpr (hall x hx)
  have hb' : Boundary WordContinue (Suffix.toList s p) := by
    cases hh : Suffix.toList s p with
    | nil => trivial
    | cons x xs =>
      intro h
      have hh' : ¬ isIdentChar x = true := by simpa [p, hh, Boundary] using hb
      exact hh' ((wordContinue_iff_identChar x).mp h)
  have hcand : ∃ t, WordToken (c::ds) t := by
    cases hk : keywordToken w with
    | some t => exact ⟨t, wordToken_keyword hk⟩
    | none =>
      by_cases hr : reservedNonFzn.contains w = true
      · have hid := identStart_of_wordStart c hstart
        unfold lexToken at hres
        simp only [hhead] at hres
        split at hres <;> try {
          have hf : False := by simpa [isAlpha] using hid
          exact hf.elim }
        simp only [hid, ite_true, hscan, hk, hr] at hres
        cases hres
      · have hr' : reservedNonFzn.contains w = false := Bool.eq_false_iff.mpr hr
        exact ⟨.ident w, wordToken_identifier hk hr'⟩
  obtain ⟨t, ht⟩ := hcand
  obtain ⟨hp, hc, hrest, hlimit⟩ := lexToken_word_complete hi hs' hstart hall' hb' ht
  have he := Except.ok.inj (hres.symm.trans hc)
  have htq := congrArg Prod.fst he
  have hqq := congrArg (fun x => x.2.val) he
  dsimp at htq hqq
  subst tok
  subst q
  refine ⟨?_, hlimit⟩
  rw [hrest, hs']
  exact .word hstart hall' hb' ht

end LeanFzn.Parser.Lexer
