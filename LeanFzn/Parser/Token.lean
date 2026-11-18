/-
Purpose: Shared token datatype for implementation and independent lexical spec.
Dependencies: Lean core only; no scanner, parser or lexical recognizer.
DAG: Token -> Lexer and Lexical -> parser grammar / correctness proof leaves.
Declaration namespaces are preserved when extracting this datatype from Lexer.
-/
namespace LeanFzn.Parser.Lexer

/-- Token type for the non-float FlatZinc fragment. -/
inductive Token where
  -- punctuation
  | lParen | rParen          -- ( )
  | lBrack | rBrack          -- [ ]
  | lBrace | rBrace          -- { }
  | comma                    -- ,
  | colon                    -- :
  | semi                     -- ;
  | colonColon               -- ::
  | dotDot                   -- ..
  | eq                       -- =
  -- keywords used by FlatZinc
  | kwPredicate | kwArray | kwOf | kwVar | kwSet | kwConstraint
  | kwSolve | kwSatisfy | kwMinimize | kwMaximize
  | kwBool | kwInt | kwPar | kwString | kwAnnotation
  -- literals / identifiers
  | boolLit (b : Bool)       -- true / false
  | intLit (i : Int)
  | stringLit (s : String)   -- decoded contents
  | ident (s : String)       -- includes var-par identifiers (may start with _)
  deriving Repr, Inhabited, BEq, DecidableEq

end LeanFzn.Parser.Lexer
