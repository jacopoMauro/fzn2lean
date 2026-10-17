/-
File: LeanFzn/Integration/Emit/Basic.lean

Purpose:
  Defines the stable executable API for rendering LeanFzn.Solver assignments as
  FlatZinc solution text, together with the verified accumulator twin.

Dependencies:
  - LeanFzn.Compiler.Domain: scalar `Value` and the solver's assignment vocabulary.

Why:
  Emission is an output concern after direct LeanFzn.Solver correctness is proved; it
  is not part of the solver's semantic correctness argument.

DAG:
  LeanFzn.Compiler.Domain -> LeanFzn.Integration.Emit.Basic -> LeanFzn.Integration.Emit -> CLI output
-/

import Lean
import LeanFzn.Compiler.Domain
open LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler


namespace LeanFzn.Integration
open LeanFzn.Semantics
open LeanFzn

/-- The FlatZinc text of one integer: decimal form, negative numbers
    with a leading `-` (the lexer's `<int-literal>` shape). -/
def emitInt (i : Int) : String :=
  toString i

/-- The FlatZinc text of one scalar solution value: `true`/`false`
    for Booleans, the decimal form for integers. Set and array values never
    occur as slot values; the placeholders keep the function total. -/
def emitScalar : Value → String
  | .bool true => "true"
  | .bool false => "false"
  | .int i => emitInt i
  | .setOfInt _ => "<unemittable set value>"
  | .array _ => "<unemittable array value>"

/-- One solution line `name = value;`. -/
def emitEntry (name : String) (v : Value) : String :=
  s!"{name} = {emitScalar v};"

/-- The FlatZinc text of a declared variable's value: scalars as
    `emitScalar`; an array as `array1d(1..n, [..])` with the declared
    index set `1..n` (FlatZinc index sets always start at 1) and
    scalar elements. -/
def emitDeclValue (d : VarDeclItem) (v : Value) : String :=
  match d, v with
  | .array ty _ _ _, .array vs =>
      s!"array1d(1..{ty.idx.hi}, [{", ".intercalate (vs.map emitScalar)}])"
  | _, v => emitScalar v

/-- One solution line for a declaration: `name = value;`. -/
def emitDeclEntry (d : VarDeclItem) (v : Value) : String :=
  s!"{(VarDeclItem.name d).name} = {emitDeclValue d v};"

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
