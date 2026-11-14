/-
Purpose: Canonical whitespace-separated rendering of solution-format tokens.
Dependencies: Parser.Lexer supplies token constructors and identifier classes.
DAG: Lexer -> SolutionRender -> Integration.Emit.Basic; its lexical round-trip
proof lives separately in Parser.Proofs.LexerRender.
-/
import LeanFzn.Parser.Lexer

namespace LeanFzn.Parser.Lexer

/-- Identifier spellings printable as a single solution identifier token.
This is a character-class and reserved-word condition, not a lexer-success
assumption. -/
def PrintableSolutionName (s : String) : Prop :=
  (∃ c cs, s.toList = c :: cs ∧ (isAlpha c || c == '_') = true ∧
    ∀ d ∈ cs, isIdentChar d = true) ∧
  keywordToken s = none ∧ reservedNonFzn.contains s = false

/-- Tokens used by non-float scalar and one-dimensional array solutions. -/
def PrintableSolutionToken : Token → Prop
  | .ident s => PrintableSolutionName s
  | .intLit _ | .boolLit _ | .lParen | .rParen | .lBrack | .rBrack
  | .lBrace | .rBrace | .comma | .semi | .eq | .dotDot => True
  | _ => False

/-- A token's canonical FlatZinc spelling. Unsupported constructors are excluded
by `PrintableSolutionToken` in the round-trip theorem. -/
def renderSolutionToken : Token → String
  | .ident s => s
  | .intLit i => toString i
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .lParen => "("
  | .rParen => ")"
  | .lBrack => "["
  | .rBrack => "]"
  | .lBrace => "{"
  | .rBrace => "}"
  | .comma => ","
  | .semi => ";"
  | .eq => "="
  | .dotDot => ".."
  | _ => ""

/-- Always place a space after each token, including the last. This makes
lexical boundaries explicit even for negative numbers and identifiers. -/
def renderSolutionTokens : List Token → String
  | [] => ""
  | t :: ts => renderSolutionToken t ++ " " ++ renderSolutionTokens ts

end LeanFzn.Parser.Lexer
