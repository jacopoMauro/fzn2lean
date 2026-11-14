/-
Purpose: Independent, value-indexed grammar of non-float FlatZinc solution text.
Dependencies: The shared lexer fixes lexical conventions; syntax and evaluation
provide literal values. This module imports no solution parser or checker.
DAG: SolutionGrammar -> Runtime.Solution -> Proofs.SolutionParser.
-/
import LeanFzn.Parser.Lexer
import LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker.Solution
open LeanFzn.Parser LeanFzn.Parser.Lexer LeanFzn.Semantics

/-- A scalar or flat array solution value. -/
inductive SolValue where
  | scalar (l : BasicLiteral)
  | array (elems : List BasicLiteral)
  deriving Repr, Inhabited

/-- One solution assignment, before model-specific name/type validation. -/
structure Entry where
  name : String
  value : SolValue
  deriving Repr, Inhabited

/-- A punctuation token following a literal in a solution assignment. -/
inductive SolTerminator where
  | comma | rBrack | semi
  deriving DecidableEq, Repr

def SolTerminator.token : SolTerminator → Token
  | .comma => .comma
  | .rBrack => .rBrack
  | .semi => .semi

/-- Integer enumeration ending at and consuming `}`. The recursive production
requires a next integer, so a trailing comma is not a grammar production. -/
inductive GrSolSetTail : List Token → List Int → List Token → Prop where
  | empty : GrSolSetTail (.rBrace :: rest) [] rest
  | singleton : GrSolSetTail (.intLit i :: .rBrace :: rest) [i] rest
  | cons : GrSolSetTail (.intLit j :: toks) is rest →
      GrSolSetTail (.intLit i :: .comma :: .intLit j :: toks) (i :: is) rest

/-- Literal followed by a context delimiter. This is the usual BNF literal
production with its FOLLOW token explicit; the delimiter is consumed. -/
inductive GrSolLiteral : List Token → BasicLiteral → SolTerminator → List Token → Prop where
  | bool : GrSolLiteral (.boolLit b :: term.token :: rest) (.bool b) term rest
  | int : GrSolLiteral (.intLit i :: term.token :: rest) (.int i) term rest
  | range : GrSolLiteral (.intLit lo :: .dotDot :: .intLit hi :: term.token :: rest)
      (.set (.intRange lo hi)) term rest
  | set : GrSolSetTail toks is (term.token :: rest) →
      GrSolLiteral (.lBrace :: toks) (.set (.intSet is)) term rest

/-- Nonempty comma-separated array elements, consuming the closing `]`. -/
inductive GrSolArrayItems : List Token → List BasicLiteral → List Token → Prop where
  | last : GrSolLiteral toks l .rBrack rest → GrSolArrayItems toks [l] rest
  | cons : GrSolLiteral toks l .comma mid → GrSolArrayItems mid ls rest →
      GrSolArrayItems toks (l :: ls) rest

/-- Array contents (possibly empty), consuming the closing `]`. -/
inductive GrSolArray : List Token → List BasicLiteral → List Token → Prop where
  | empty : GrSolArray (.rBrack :: rest) [] rest
  | items : GrSolArrayItems toks ls rest → GrSolArray toks ls rest

/-- Handbook §4.3.3.1 assignment syntax for the non-float fragment. Bare arrays
are the current format. The historical `array1d` wrapper is also supported,
with its one-based index set and element count checked explicitly. -/
inductive GrSolEntry : List Token → Entry → List Token → Prop where
  | scalar : GrSolLiteral toks l .semi rest →
      GrSolEntry (.ident x :: .eq :: toks) ⟨x, .scalar l⟩ rest
  | array : GrSolArray toks ls (.semi :: rest) →
      GrSolEntry (.ident x :: .eq :: .lBrack :: toks) ⟨x, .array ls⟩ rest
  | array1d : GrSolArray toks ls (.rParen :: .semi :: rest) →
      hi = (ls.length : Int) →
      GrSolEntry (.ident x :: .eq :: .ident "array1d" :: .lParen ::
        .intLit 1 :: .dotDot :: .intLit hi :: .comma :: .lBrack :: toks)
        ⟨x, .array ls⟩ rest

/-- A complete sequence of semicolon-terminated assignments. -/
inductive GrSolution : List Token → List Entry → Prop where
  | nil : GrSolution [] []
  | cons : GrSolEntry toks e rest → GrSolution rest es → GrSolution toks (e :: es)

/-- Lexical conventions are shared with the model grammar; syntactic validity
and the assigned values are specified by the independent relations above. -/
def SolutionGrammar (s : String) (es : List Entry) : Prop :=
  ∃ toks, tokenize s = .ok toks ∧ GrSolution toks.toList es

/-- Membership of the supported non-float FlatZinc solution language. -/
def ValidSolution (s : String) : Prop := ∃ es, SolutionGrammar s es

end LeanFzn.Checker.Solution
