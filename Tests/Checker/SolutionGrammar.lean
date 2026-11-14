/-
Purpose: Kernel-checked solution-format regressions, independent of executable
parser definitions. Positive examples construct declarative grammar derivations
and obtain parser acceptance from completeness; negative examples evaluate the literal delimiter and set parsers through
their proved defining equations.
Dependencies: Checker.Proofs.SolutionParser supplies the grammar/parser bridge.
DAG: SolutionGrammar + SolutionParser -> this proof-only regression module.
-/
import LeanFzn.Checker.Proofs.SolutionParser

namespace LeanFzn.Tests.SolutionGrammar
open LeanFzn.Parser.Lexer LeanFzn.Semantics LeanFzn.Checker.Solution

private def expected : List Entry :=
  [⟨"ss", .array [.set (.intSet [1, 2]), .set (.intSet [1])]⟩]

/-- The two-element set is followed by another array element. These are
independent grammar constructors, not facts obtained from parser evaluation. -/
private theorem setArray (rest : List Token) :
    GrSolArray
      (.lBrace :: .intLit 1 :: .comma :: .intLit 2 :: .rBrace :: .comma ::
       .lBrace :: .intLit 1 :: .rBrace :: .rBrack :: rest)
      [.set (.intSet [1, 2]), .set (.intSet [1])] rest :=
  .items (.cons (.set (.cons .singleton)) (.last (.set .singleton)))

private def bareTokens : List Token :=
  [.ident "ss", .eq, .lBrack, .lBrace, .intLit 1, .comma,
   .intLit 2, .rBrace, .comma, .lBrace, .intLit 1, .rBrace, .rBrack, .semi]

private def wrappedTokens : List Token :=
  [.ident "ss", .eq, .ident "array1d", .lParen, .intLit 1,
   .dotDot, .intLit 2, .comma, .lBrack, .lBrace, .intLit 1, .comma,
   .intLit 2, .rBrace, .comma, .lBrace, .intLit 1, .rBrace, .rBrack,
   .rParen, .semi]

/-- Handbook bare-array production with exact expected values. -/
theorem bareArray_grammar : GrSolution bareTokens expected :=
  .cons (.array (setArray [.semi])) .nil

/-- Historical array1d production with its checked one-based index set. -/
theorem wrappedArray_grammar : GrSolution wrappedTokens expected :=
  .cons (.array1d (setArray [.rParen, .semi]) rfl) .nil

example : parseSolutionTokens bareTokens = .ok expected :=
  parseSolutionTokens_eq_ok_iff_grammar.mpr bareArray_grammar

example : parseSolutionTokens wrappedTokens = .ok expected :=
  parseSolutionTokens_eq_ok_iff_grammar.mpr wrappedArray_grammar

/-- Missing array comma is rejected by the literal/delimiter parser. -/
example : parseSolLiteral
    [.lBrace, .intLit 1, .comma, .intLit 2, .rBrace,
     .lBrace, .intLit 1, .rBrace, .rBrack, .semi] =
    .error "expected literal delimiter" := by
  simp [parseSolLiteral, parseSolSetTail, parseSolTerminator, Bind.bind, Except.bind]

/-- An enumerated set cannot end with a comma. -/
example : parseSolSetTail [.intLit 1, .comma, .intLit 2, .comma, .rBrace] =
    .error "expected integer or '}' in set literal" := by
  simp [parseSolSetTail]

end LeanFzn.Tests.SolutionGrammar
