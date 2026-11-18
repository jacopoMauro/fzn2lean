/-
Purpose: Assemble whole-stream lexical correctness from the local token proof.
Dependencies: Independent lexical target, local step target and exact trivia.
DAG: Actual primitive proofs -> step certificate -> this stream assembly.
Intermediate theorems expose their step assumption; the final project witness
must instantiate it with the independently proved actual lexer step.
-/
import LeanFzn.Parser.Proofs.LexicalTarget
import LeanFzn.Parser.Proofs.LexerStepTarget
import LeanFzn.Parser.Proofs.LexerTrivia

namespace LeanFzn.Parser.Lexical
open LeanFzn.Parser.Lexer

theorem tokenizeAux_sound_of_step (step : LexerStepCertification)
    (s : Array Char) (pos : Nat) (acc out : Array Token)
    (hp : pos ≤ s.size) (hrun : tokenizeAux s pos acc = .ok out) :
    ∃ ts : List Token, out.toList = acc.toList ++ ts ∧
      LexesChars (Suffix.toList s pos) ts := by
  induction pos, acc using tokenizeAux.induct (s := s) generalizing out with
  | case1 pos acc p hi ih =>
    change skipTrivia s pos < s.size at hi
    obtain ⟨hb, ht, hcan⟩ := skipTrivia_spec s pos hp
    cases he : lexToken s (skipTrivia s pos) hi with
    | error e =>
      rw [tokenizeAux.eq_def] at hrun
      simp only [hi, dite_true, he] at hrun
      change Except.error e = Except.ok out at hrun
      cases hrun
    | ok result =>
      obtain ⟨tok, q, hq⟩ := result
      have hrec : tokenizeAux s q (acc.push tok) = .ok out := by
        rw [tokenizeAux.eq_def] at hrun
        simp only [hi, dite_true, he] at hrun
        exact hrun
      obtain ⟨hl, hbound⟩ := step.sound s (skipTrivia s pos) hi tok q hq he
      obtain ⟨ts, hout, htail⟩ := ih tok q hq out hbound hrec
      refine ⟨tok :: ts, ?_, .next ht hl htail⟩
      simpa [Array.toList_push, List.append_assoc] using hout
  | case2 pos acc p hi =>
    change ¬ skipTrivia s pos < s.size at hi
    obtain ⟨hb, ht, hcan⟩ := skipTrivia_spec s pos hp
    have heq : skipTrivia s pos = s.size := by omega
    have ho : acc = out := by
      simpa only [tokenizeAux.eq_def s pos acc, hi, dite_false, pure, Except.pure,
        Except.ok.injEq] using hrun
    subst out
    refine ⟨[], by simp, .done ?_⟩
    rw [heq, (Suffix.toList_eq_nil_iff s s.size).mpr (by omega)] at ht
    exact ht

theorem tokenizeAux_complete_of_step (step : LexerStepCertification)
    {cs : List Char} {ts : List Token} (hlex : LexesChars cs ts)
    (s : Array Char) (pos : Nat) (acc : Array Token)
    (hp : pos ≤ s.size) (hs : Suffix.toList s pos = cs) :
    tokenizeAux s pos acc = .ok (acc ++ ts.toArray) := by
  induction hlex generalizing pos acc with
  | done ht =>
    have hskip := skipTrivia_complete ht True.intro s pos hp hs
    have hn : ¬ skipTrivia s pos < s.size := by
      have := (Suffix.toList_eq_nil_iff s (skipTrivia s pos)).mp hskip
      omega
    rw [tokenizeAux.eq_def]
    simp only [hn, dite_false]
    change Except.ok acc = Except.ok (acc ++ #[])
    simp
  | @next cs0 significant tok tail toks ht hl htail ih =>
    have hskip := skipTrivia_complete ht (lexeme_significant hl) s pos hp hs
    obtain ⟨hb, _, _⟩ := skipTrivia_spec s pos hp
    have hi : skipTrivia s pos < s.size := by
      have hn := lexeme_nonempty hl
      by_cases h : skipTrivia s pos < s.size
      · exact h
      have hz := (Suffix.toList_eq_nil_iff s (skipTrivia s pos)).mpr (by omega)
      rw [hskip] at hz
      exact (hn hz).elim
    obtain ⟨q, hq, he, hrest, hbound⟩ :=
      step.complete s (skipTrivia s pos) hi _ _ (by rw [hskip]; exact hl)
    have hrec := ih q (acc.push tok) hbound hrest
    rw [tokenizeAux.eq_def]
    simp only [hi, dite_true, he, Except.bind]
    change tokenizeAux s q (acc.push tok) = .ok (acc ++ (tok :: toks).toArray)
    rw [hrec]
    congr 1
    apply Array.toList_inj.mp
    simp [Array.toList_append, Array.toList_push, List.append_assoc]

/-- Conditional assembly only; callers must provide the actual local proof. -/
theorem certification_of_step (step : LexerStepCertification) : LexerCertification := by
  constructor
  · intro text tokens ht
    obtain ⟨ts, hout, hlex⟩ := tokenizeAux_sound_of_step step
      (String.Internal.toArray text) 0 #[] tokens (by omega) ht
    have heq : ts = tokens.toList := by simpa using hout.symm
    rw [heq] at hlex
    simpa [Lexes, Suffix.toList, String.toList] using hlex
  · intro text tokens ht
    have hlex : LexesChars (Suffix.toList (String.Internal.toArray text) 0) tokens.toList := by
      simpa [Lexes, Suffix.toList, String.toList] using ht
    have he := tokenizeAux_complete_of_step step hlex
      (String.Internal.toArray text) 0 #[] (by omega) rfl
    simpa [tokenize] using he

end LeanFzn.Parser.Lexical
