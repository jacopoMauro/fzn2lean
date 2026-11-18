/-
Purpose: Compose independent character-level lexical correctness with the
existing token-grammar parser proofs, preserving the exact produced AST.
Dependencies: LexerCorrectness and the proved parser soundness/completeness.
DAG: lexical certificate + token parser proofs -> source recognition theorem.
-/
import LeanFzn.Parser.Proofs.LexerCorrectness
import LeanFzn.Parser.Proofs.Assembled

namespace LeanFzn.Parser.Lexical

theorem parseModel_iff_sourceGrammar (text : String) (model : LeanFzn.Model) :
    Parser.parseModel text = .ok model ↔ SourceGrammar text model := by
  rw [← grammar_iff_sourceGrammar lexerCertification text model]
  exact ⟨parseModel_sound,parseModel_complete⟩

theorem parseModel_ok_iff_sourceValid (text : String) :
    (∃ model, Parser.parseModel text = .ok model) ↔ ∃ model, SourceGrammar text model :=
  exists_congr (fun model => parseModel_iff_sourceGrammar text model)

end LeanFzn.Parser.Lexical
