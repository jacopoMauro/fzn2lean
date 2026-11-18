/-
Purpose: Stable local interface for assembling whole-stream lexer proofs.
Dependencies: Independent Lexical and executable Lexer via suffix adapter.
DAG: Primitive scanner proofs -> local step certificate -> stream induction.
The record is an interface, not a supplied correctness assumption at top level.
-/
import LeanFzn.Parser.Lexical
import LeanFzn.Parser.Proofs.LexerSuffix

namespace LeanFzn.Parser.Lexical
open LeanFzn.Parser.Lexer

structure LexerStepCertification : Prop where
  sound : ∀ (s : Array Char) (pos : Nat) (hi : pos < s.size)
    (tok : Token) (q : Nat) (hq : pos < q),
    Lexer.lexToken s pos hi = .ok (tok, ⟨q,hq⟩) →
      Lexeme (Suffix.toList s pos) tok (Suffix.toList s q) ∧ q ≤ s.size
  complete : ∀ (s : Array Char) (pos : Nat) (hi : pos < s.size)
    (tok : Token) (rest : List Char),
    Lexeme (Suffix.toList s pos) tok rest →
      ∃ (q : Nat) (hq : pos < q), Lexer.lexToken s pos hi = .ok (tok, ⟨q,hq⟩) ∧
        Suffix.toList s q = rest ∧ q ≤ s.size

end LeanFzn.Parser.Lexical
