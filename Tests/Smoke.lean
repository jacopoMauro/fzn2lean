import LeanFzn.FznParser

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
  ]

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
  if (validResults ++ invalidResults).all id then
    IO.println s!"passed {validCases.length + invalidCases.length} parser smoke tests"
    return 0
  else
    return 1
