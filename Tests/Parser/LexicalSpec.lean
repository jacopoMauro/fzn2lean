/-
Purpose: Sanity-check the independent lexical relation and expose the known
raw-CR discrepancy without falsely declaring a lexer certificate complete.
Dependencies: LexicalTarget and executable Lexer; never imported by the spec.
DAG: Specification + implementation -> these specification-review examples.
-/
import LeanFzn.Parser.Proofs.SourceCorrectness

open LeanFzn.Parser.Lexer LeanFzn.Parser.Lexical
namespace Tests.Parser.LexicalSpec

example : Lexes "" #[] := .done .refl

example : Lexes " % a final comment" #[] := by
  exact .done (.space (Or.inl rfl) (.commentEOF (by decide)))

example : Lexes "::" #[.colonColon] := by
  exact .next .refl .colonColon (.done .refl)

example : Lexes ".." #[.dotDot] := by
  exact .next .refl .dotDot (.done .refl)

example : Lexes "true" #[.boolLit true] := by
  apply LexesChars.next Trivia.refl
  · apply Lexeme.word (c := 't') (cs := ['r', 'u', 'e'])
    · left; right; decide
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> (left; left; right; decide)
    · trivial
    · exact .keyword (by simp [Keywords])
  · exact .done .refl

/-- UTF-8 is specified by encoding, not by invoking the implementation decoder. -/
example : EncodesUTF8 [195, 169] "é" := by rfl

/-- Incomplete prefixes cannot be reinterpreted as a decimal prefix. -/
example : RadixPrefix "0x".toList := trivial
example : RadixPrefix "0o8".toList := trivial

private def quoted (s : String) : String := "\"" ++ s ++ "\""

/-- Executable boundary regressions supplement the unconditional kernel proofs;
they are not substituted for soundness or completeness. -/
def checkBoundaries : IO Unit := do
  let good : List (String × List Token) :=
    [("", []), (" \t\n\r", []), ("% final comment", []),
     ("% quotes \" and percent % are inert", []),
     ("var% comment with CR\r continues\nint", [.kwVar,.kwInt]),
     ("()[]{},;=", [.lParen,.rParen,.lBrack,.rBrack,.lBrace,.rBrace,.comma,.semi,.eq]),
     (":", [.colon]), ("::", [.colonColon]), (":::..", [.colonColon,.colon,.dotDot]),
     ("1..2", [.intLit 1,.dotDot,.intLit 2]),
     ("true false", [.boolLit true,.boolLit false]),
     ("truex false_ _ Var", [.ident "truex",.ident "false_",.ident "_",.ident "Var"]),
     ("123abc", [.intLit 123,.ident "abc"]), ("1e3", [.intLit 1,.ident "e3"]),
     ("0 -0 00012 -000", [.intLit 0,.intLit 0,.intLit 12,.intLit 0]),
     ("0xAF -0xff 0o77 -0o10", [.intLit 175,.intLit (-255),.intLit 63,.intLit (-8)]),
     ("0x1g", [.intLit 1,.ident "g"]), ("0o78", [.intLit 7,.intLit 8]),
     ("0X1 0O7", [.intLit 0,.ident "X1",.intLit 0,.ident "O7"]),
     ("1234567890123456789012345678901234567890", [.intLit 1234567890123456789012345678901234567890]),
     (quoted "", [.stringLit ""]), (quoted "%", [.stringLit "%"]),
     (quoted "é😺", [.stringLit "é😺"]),
     (quoted "\\n", [.stringLit "\n"]), (quoted "\\t", [.stringLit "\t"]),
     (quoted "\\\"", [.stringLit "\""]), (quoted "\\\\", [.stringLit "\\"]),
     (quoted "\\x41f", [.stringLit "Af"]),
     (quoted "\\x4G", [.stringLit (String.singleton (Char.ofNat 4) ++ "G")]),
     (quoted "\\101", [.stringLit "A"]), (quoted "\\12", [.stringLit "\n"]),
     (quoted "\\x0D", [.stringLit (String.singleton '\r')]),
     (quoted "\\303\\251", [.stringLit "é"]),
     (quoted "\\xC3\\xA9", [.stringLit "é"]),
     (quoted "\\0", [.stringLit (String.singleton (Char.ofNat 0))])]
  let bad : List String :=
    [".", "1.0", "0x", "-0x", "0xG", "0o8", "-0o9", "--1", "- 1", "+1",
     "float", "if", "α", "\"unterminated", "\"\\", quoted "\\q", quoted "\\(",
     quoted "\\400", quoted "\\777", quoted "\\377", quoted "\\xFF",
     quoted "\\xC0\\x80", quoted "\\x", quoted "\\",
     quoted (String.singleton '\r'), quoted (String.singleton '\n'),
     quoted ("\\" ++ String.singleton '\n')]
  for (source,expected) in good do
    match tokenize source with
    | .error error => throw (IO.userError s!"unexpected lexical rejection: {repr source}: {error}")
    | .ok tokens =>
      unless tokens.toList == expected do
        throw (IO.userError s!"wrong tokens for {repr source}: {repr tokens}; expected {repr expected}")
  for source in bad do
    match tokenize source with
    | .error _ => pure ()
    | .ok tokens => throw (IO.userError s!"unexpected lexical acceptance: {repr source}: {repr tokens}")
  IO.println s!"lexer boundaries: {good.length} accepted and {bad.length} rejected cases passed"

#eval checkBoundaries

end Tests.Parser.LexicalSpec
