/-
Purpose: Unconditional soundness and completeness of the actual tokenizer
against the independent, value-sensitive whole-character lexical relation.
Dependencies: Concrete token-step proofs and generic stream induction.
DAG: Primitive proofs -> LexerStep + LexerStream -> this public certificate.
-/
import LeanFzn.Parser.Proofs.LexerStep
import LeanFzn.Parser.Proofs.LexerStream

namespace LeanFzn.Parser.Lexical
open LeanFzn.Parser.Lexer (Token)

/-- The actual lexer realizes the declared independent lexical specification. -/
theorem lexerCertification : LexerCertification :=
  certification_of_step lexerStepCertification

theorem tokenize_sound (text : String) (tokens : Array Token)
    (h : Lexer.tokenize text = .ok tokens) : Lexes text tokens :=
  lexerCertification.sound text tokens h

theorem tokenize_complete (text : String) (tokens : Array Token)
    (h : Lexes text tokens) : Lexer.tokenize text = .ok tokens :=
  lexerCertification.complete text tokens h

theorem tokenize_correct (text : String) (tokens : Array Token) :
    Lexer.tokenize text = .ok tokens ↔ Lexes text tokens :=
  ⟨tokenize_sound text tokens, tokenize_complete text tokens⟩

theorem lexes_unique {text : String} {tokens other : Array Token}
    (h : Lexes text tokens) (hother : Lexes text other) : tokens = other :=
  Except.ok.inj ((tokenize_complete text tokens h).symm.trans
    (tokenize_complete text other hother))

/-- Rejection is characterized semantically, without specifying diagnostics. -/
theorem tokenize_error_iff (text : String) :
    (∃ error, Lexer.tokenize text = .error error) ↔ ¬ ∃ tokens, Lexes text tokens := by
  constructor
  · rintro ⟨error,he⟩ ⟨tokens,ht⟩
    have hok := tokenize_complete text tokens ht
    rw [he] at hok
    cases hok
  · intro hn
    cases he : Lexer.tokenize text with
    | error error => exact ⟨error,rfl⟩
    | ok tokens => exact (hn ⟨tokens,tokenize_sound text tokens he⟩).elim

end LeanFzn.Parser.Lexical
