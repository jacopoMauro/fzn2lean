/-
File: Tests/Parser/Smoke.lean

Purpose:
  Parser smoke tests: valid FlatZinc snippets that must parse, and
  invalid snippets that must be rejected.

Dependencies:
  LeanFzn.Parser.Parser (parseModel).

Why:
  Guards the parser contract that `parsePosition`/`parseModel` accepts
  exactly the non-float fragment; cheap, fast, and run by the CI smoke
  target `tests_smoke`.

DAG:
  FznParser -> Tests/Smoke.lean -> tests_smoke executable
-/

import LeanFzn.Parser.Parser

open LeanFzn.Parser


open LeanFzn

private def validCases : List (String × String) :=
  [ ("minimal model", "solve satisfy;")
  , ("comments and integer parameter", "% heading\nint: answer = 0x2a;\nsolve satisfy;")
  , ("variable and constraint", "var 0..10: x;\nconstraint int_eq(x, 3);\nsolve satisfy;")
  , ("array parameter", "array [1..3] of int: xs = [1, 2, 3];\nsolve satisfy;")
  , ("annotation call with var identifier", "var int: _x;\nsolve :: foo(_x) satisfy;")
  , ("empty set-of-int domain", "var set of {}: s;\nsolve satisfy;")
  , ("empty predicate parameter list", "predicate p();\nsolve satisfy;")
  , ("open predicate array index", "predicate p(array [int] of var int: xs);\nsolve satisfy;")
  , ("fixed predicate array index", "predicate p(array [1..2] of int: xs);\nsolve satisfy;")
  , ("empty parameter array", "array [1..0] of bool: xs = [];\nsolve satisfy;")
  , ("variable array lookahead", "array [1..1] of var int: xs = [1];\nsolve satisfy;")
  , ("empty constraint arguments", "constraint p();\nsolve satisfy;")
  , ("nested annotations", "solve :: outer(inner(1), [true, _x]) satisfy;")
  , ("integer set domains", "var {1, 2}: x;\nvar set of {1, 2}: s;\nsolve satisfy;")
  , ("optimization objectives", "int: objective = 1;\nsolve maximize objective;")
  , ("string escapes (R11)", "solve :: a(\"row\\t\\x41\\101\\\"\\\\\") satisfy;")
  , ("UTF-8 from hex escapes", "solve :: a(\"\\xC3\\xA9\") satisfy;")
  ]

private def invalidCases : List (String × String) :=
  [ ("missing semicolon", "solve satisfy")
  , ("trailing item", "solve satisfy; constraint int_eq(1, 1);")
  , ("float syntax", "float: x = 1.5; solve satisfy;")
  , ("wrong section order", "constraint int_eq(x, 1); var int: x; solve satisfy;")
  , ("restricted annotation name", "solve :: _bad satisfy;")
  , ("empty annotation call", "solve :: foo() satisfy;")
  , ("empty variable integer domain", "var {}: x; solve satisfy;")
  , ("empty predicate integer domain", "predicate p({}: x); solve satisfy;")
  , ("trailing constraint comma", "constraint p(1,); solve satisfy;")
  , ("trailing predicate parameter comma", "predicate p(int: x,); solve satisfy;")
  , ("trailing array comma", "array [1..1] of int: xs = [1,]; solve satisfy;")
  , ("trailing annotation comma", "solve :: foo(1,) satisfy;")
  , ("variable array without initializer", "array [1..1] of var int: xs; solve satisfy;")
  , ("non-one-based array", "array [0..1] of int: xs = [1, 2]; solve satisfy;")
  , ("restricted predicate parameter name", "predicate p(int: _x); solve satisfy;")
  , ("unknown string escape", "solve :: a(\"\\q\") satisfy;")
  , ("string interpolation escape", "solve :: a(\"\\(x)\") satisfy;")
  , ("backslash before newline", "solve :: a(\"a\\\nb\") satisfy;")
  , ("escape decoding to invalid UTF-8", "solve :: a(\"\\xFF\") satisfy;")
  , ("octal escape above 255", "solve :: a(\"\\777\") satisfy;")
  ]

/-- Decoded annotation strings: the source of the single annotation
    argument and the string it must decode to (R11). -/
private def decodeCases : List (String × String) :=
  [ ("\"row\\t\\x41\"", "row\tA")
  , ("\"\\101\\x4a\\n\"", "AJ\n")
  , ("\"\\\"\\\\\"", "\"\\")
  , ("\"\\xC3\\xA9\"", "é")
  ]

private def checkDecode (case : String × String) : IO Bool := do
  match Parser.parseModel s!"solve :: a({case.1}) satisfy;" with
  | .ok { solve := .satisfy [.call _ [.string got]], .. } =>
      if got == case.2 then return true
      IO.eprintln s!"FAIL (decoding): {case.1} gave {repr got}, expected {repr case.2}"
      return false
  | _ =>
      IO.eprintln s!"FAIL (decoding): {case.1} did not parse to one string argument"
      return false

private def checkValid (case : String × String) : IO Bool := do
  match Parser.parseModel case.2 with
  | .ok _ => return true
  | .error e =>
      IO.eprintln s!"FAIL (expected valid): {case.1}: {e}"
      return false

private def checkInvalid (case : String × String) : IO Bool := do
  match Parser.parseModel case.2 with
  | .error _ => return true
  | .ok model =>
      IO.eprintln s!"FAIL (expected invalid): {case.1}: {repr model}"
      return false

def main : IO UInt32 := do
  let validResults ← validCases.mapM checkValid
  let invalidResults ← invalidCases.mapM checkInvalid
  let decodeResults ← decodeCases.mapM checkDecode
  if (validResults ++ invalidResults ++ decodeResults).all id then
    IO.println s!"passed {validCases.length + invalidCases.length + decodeCases.length} parser smoke tests"
    return 0
  else
    return 1
