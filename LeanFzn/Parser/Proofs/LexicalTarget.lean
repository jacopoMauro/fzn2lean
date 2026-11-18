/-
Purpose: Type-checked proof obligations for complete lexical certification,
plus the exact downstream character-to-AST contract.
Dependencies: Independent Lexical, executable Lexer and existing Grammar.
DAG: Specification + implementation -> future proof branches -> this interface.
This interface supplies no witness itself; LexerCorrectness constructs the
unconditional LexerCertification from concrete primitive and stream proofs.
-/
import LeanFzn.Parser.Lexical
import LeanFzn.Parser.Lexer
import LeanFzn.Parser.Grammar

namespace LeanFzn.Parser.Lexical
open LeanFzn.Parser.Lexer (Token)

/-- Unconditional, value-sensitive soundness and completeness on all Lean
strings. There is no lexer-success premise in completeness, no fuel bound,
no rendered-text restriction, and no well-formed-model/admission assumption. -/
structure LexerCertification : Prop where
  sound : ∀ (text : String) (tokens : Array Token),
    Lexer.tokenize text = .ok tokens → Lexes text tokens
  complete : ∀ (text : String) (tokens : Array Token),
    Lexes text tokens → Lexer.tokenize text = .ok tokens

/-- The intended independent character-level model grammar. It uses the
existing token grammar, but never calls the executable tokenizer/parser. -/
def SourceGrammar (text : String) (model : LeanFzn.Model) : Prop :=
  ∃ tokens : Array Token, Lexes text tokens ∧ GrModel tokens.toList model []

/-- Packaging two actual proofs yields the desired complete characterization.
This conditional lemma is not a completed lexer certificate. -/
theorem tokenize_iff_of_certification (cert : LexerCertification)
    (text : String) (tokens : Array Token) :
    Lexer.tokenize text = .ok tokens ↔ Lexes text tokens :=
  ⟨cert.sound text tokens, cert.complete text tokens⟩

/-- A lexical certificate connects the old lexer-relative model grammar
to the independent character relation, preserving the exact AST witness. -/
theorem grammar_iff_sourceGrammar (cert : LexerCertification)
    (text : String) (model : LeanFzn.Model) :
    Grammar text model ↔ SourceGrammar text model := by
  unfold Grammar SourceGrammar
  constructor
  · rintro ⟨tokens, hlex, hmodel⟩
    exact ⟨tokens, cert.sound text tokens hlex, hmodel⟩
  · rintro ⟨tokens, hlex, hmodel⟩
    exact ⟨tokens, cert.complete text tokens hlex, hmodel⟩

end LeanFzn.Parser.Lexical
