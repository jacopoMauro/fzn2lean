/-
File: LeanFzn/Integration/Emit/Basic.lean

Purpose:
  Defines the stable executable API for rendering LeanFzn.Solver assignments as
  FlatZinc solution text, together with the verified accumulator twin.

Dependencies:
  - LeanFzn.Compiler.Domain: scalar `Value` and the solver's assignment vocabulary.
  - LeanFzn.Parser.SolutionRender: canonical token spelling with lexical boundaries.

Why:
  Emission is an output concern after direct LeanFzn.Solver correctness is proved; it
  is not part of the solver's semantic correctness argument.

DAG:
  Compiler.Domain + Parser.SolutionRender -> Emit.Basic -> Emit.Model -> CLI output
-/

import Lean
import LeanFzn.Compiler.Domain
import LeanFzn.Parser.SolutionRender
open LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler


namespace LeanFzn.Integration
open LeanFzn.Semantics
open LeanFzn
open LeanFzn.Parser.Lexer

/-- The FlatZinc text of one integer: decimal form, negative numbers
    with a leading `-` (the lexer's `<int-literal>` shape). -/
def emitInt (i : Int) : String :=
  toString i

/-- The FlatZinc text of one integer set: an ascending, duplicate-free
    enumeration `{...}`, with `{}` for the empty set. -/
def emitSet (s : IntSetValue) : String :=
  "{" ++ ", ".intercalate (IntSetValue.sortElems s |>.map emitInt) ++ "}"

/-- The FlatZinc text of one scalar solution value: `true`/`false`
    for Booleans, the decimal form for integers, `{...}` for sets. An
    array value never occurs as a slot value (arrays are emitted by
    `emitDeclValue`); treating one as scalar is an internal error, not
    output. -/
def emitScalar : Value → String
  | .bool true => "true"
  | .bool false => "false"
  | .int i => emitInt i
  | .setOfInt s => emitSet s
  | .array _ => panic! "internal error: scalar emission of an array value"

/-- Separate already-tokenized literal values with array/set commas. -/
def commaSeparatedTokens : List (List Token) → List Token
  | [] => []
  | ts :: tss => ts ++ tss.foldr (fun xs acc => .comma :: xs ++ acc) []

/-- Canonical scalar tokens. Arrays are excluded by the typed output contract;
this fallback remains an explicit internal error rather than silently emitting
an array as a scalar. -/
def scalarSolutionTokens : Value → List Token
  | .bool b => [.boolLit b]
  | .int i => [.intLit i]
  | .setOfInt s =>
      .lBrace :: commaSeparatedTokens (s.sortElems.map (fun i => [.intLit i])) ++ [.rBrace]
  | .array _ => panic! "internal error: scalar emission of an array value"

/-- Tokens of a declared value, with a canonical array upper bound equal to
the number of emitted elements. This also prints every empty array as 1..0,
including declarations whose original upper bound is negative. -/
def declSolutionTokens (d : VarDeclItem) (v : Value) : List Token :=
  match d, v with
  | .array _ _ _ _, .array vs =>
      [.ident "array1d", .lParen, .intLit 1, .dotDot, .intLit (vs.length : Int),
       .comma, .lBrack] ++
      commaSeparatedTokens (vs.map scalarSolutionTokens) ++ [.rBrack, .rParen]
  | _, v => scalarSolutionTokens v

/-- The exact tokens printed for a declaration assignment. -/
def declEntryTokens (d : VarDeclItem) (v : Value) : List Token :=
  [.ident d.name.name, .eq] ++ declSolutionTokens d v ++ [.semi]

/-- One scalar solution assignment. The canonical renderer places whitespace
between every pair of tokens, so set commas cannot be mistaken for array commas. -/
def emitEntry (name : String) (v : Value) : String :=
  renderSolutionTokens ([.ident name, .eq] ++ scalarSolutionTokens v ++ [.semi])

/-- Canonical FlatZinc rendering of a declared scalar or flat array value. -/
def emitDeclValue (d : VarDeclItem) (v : Value) : String :=
  renderSolutionTokens (declSolutionTokens d v)

/-- One solution line for a declaration, using the proved token renderer. -/
def emitDeclEntry (d : VarDeclItem) (v : Value) : String :=
  renderSolutionTokens (declEntryTokens d v)

/-- FlatZinc solution separator (ends every solution; O1 prints one per
    intermediate solution). -/
def solutionSeparator : String := "----------"

/-- FlatZinc optimum marker, printed once after the last solution when an
    optimisation run proves optimality (reserved for task O1; unused by
    satisfaction runs). -/
def optimumMarker : String := "=========="

/-- A list of assignment lines followed by the FlatZinc solution separator. -/
def emitSolution : List (String × Value) → String
  | [] => "----------"
  | p :: rest => emitEntry p.1 p.2 ++ "\n" ++ emitSolution rest

/-! ## Accumulator implementation -/

/-- Append one emitted entry to the accumulator. -/
private def emitAccStep (acc : String) (p : String × Value) : String :=
  acc ++ emitEntry p.1 p.2 ++ "\n"

/-- Accumulate entry lines left-to-right, then append the separator. -/
private def emitSolutionGo : String → List (String × Value) → String
  | acc, [] => acc ++ "----------"
  | acc, p :: rest => emitSolutionGo (emitAccStep acc p) rest

/-- Linear accumulator twin of `emitSolution`. -/
def emitSolutionFast (ps : List (String × Value)) : String :=
  emitSolutionGo "" ps

private theorem emitSolutionGo_acc : ∀ (acc : String) (p : String × Value)
    (rest : List (String × Value)),
    emitSolutionGo (emitAccStep acc p) rest
      = acc ++ (emitEntry p.1 p.2 ++ "\n" ++ emitSolutionGo "" rest) := by
  intro acc p rest
  induction rest generalizing acc p with
  | nil =>
      show (acc ++ emitEntry p.1 p.2 ++ "\n") ++ "----------"
        = acc ++ (emitEntry p.1 p.2 ++ "\n" ++ ("" ++ "----------"))
      simp only [String.empty_append, String.append_assoc]
  | cons q rest' ih =>
      show emitSolutionGo (emitAccStep (emitAccStep acc p) q) rest'
        = acc ++ (emitEntry p.1 p.2 ++ "\n"
            ++ emitSolutionGo (emitAccStep "" q) rest')
      rw [ih (emitAccStep acc p) q, ih "" q]
      simp only [emitAccStep, String.empty_append, String.append_assoc]

/-- The accumulator implementation produces exactly the reference text. -/
theorem emitSolutionFast_eq (ps : List (String × Value)) :
    emitSolutionFast ps = emitSolution ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hstep : emitSolutionGo "" (p :: rest)
          = emitEntry p.1 p.2 ++ "\n" ++ emitSolutionGo "" rest :=
        emitSolutionGo_acc "" p rest
      show emitSolutionGo "" (p :: rest)
        = emitEntry p.1 p.2 ++ "\n" ++ emitSolution rest
      rw [hstep, show emitSolutionGo "" rest = emitSolutionFast rest from rfl, ih]

/- The compiled emitter uses the accumulator twin. -/
attribute [implemented_by emitSolutionFast] emitSolution

end LeanFzn.Integration
