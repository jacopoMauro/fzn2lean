import LeanFzn.Parser.Pretty
import LeanFzn.Parser.Parser

open LeanFzn.Parser


open LeanFzn

/-!
# Pretty-printer round-trip tests

Each case is a FlatZinc source string.  A case passes when:

1. the source parses (`Parser.parseModel`);
2. pretty-printing the parsed model yields text that re-parses to a model
   equal to the first one (compared via the derived `Repr`, since `Model`
   has no `DecidableEq` here);
3. printing is idempotent: printing the re-parsed model gives the same
   text again (`pretty (parse (pretty (parse src))) = pretty (parse src)`).
-/

private def roundTripCases : List (String × String) :=
  [ ("minimal model", "solve satisfy;")
  , ("parameter and variable", "int: n = 3;\nvar 0..9: x;\nsolve satisfy;")
  , ("reversed range domain", "var 5..1: x;\nsolve satisfy;")
  , ("empty set domain", "var set of {}: s;\nsolve satisfy;")
  , ("array parameter", "array [1..3] of int: xs = [1, 2, 3];\nsolve satisfy;")
  , ("empty array parameter", "array [1..0] of int: xs = [];\nsolve satisfy;")
  , ("variable array with initializer",
      "array [1..3] of var 0..9: xs = [1, 2, 3];\nsolve satisfy;")
  , ("alias variable", "var int: x;\nvar int: y = x;\nsolve satisfy;")
  , ("integer objective", "var int: x;\nsolve minimize x;")
  , ("declared predicate and constraint call",
      "predicate p(var int: x);\nvar int: x;\nconstraint p(x);\nsolve satisfy;")
  , ("builtin constraint call", "int: n = 3;\nvar int: x;\nconstraint int_eq(n, x);\nsolve satisfy;")
  , ("forward reference",
      "var int: x;\nvar int: y;\nconstraint int_eq(x, y);\nsolve satisfy;")
  , ("set constraint", "var set of int: s;\nvar int: x;\nconstraint set_in(x, s);\nsolve satisfy;")
  , ("variable annotation", "var 0..9: x :: my_ann;\nsolve satisfy;")
  , ("constraint annotation", "var int: x;\nconstraint int_eq(x, x) :: domain;\nsolve satisfy;")
  , ("solve annotation with ident arguments",
      "var int: x;\nsolve :: seq_search([int_search(x, input_order, indomain_min, complete)]) satisfy;")
  , ("string annotation with escaped quotes",
      "var 0..9: x :: note(\"hello \\\"world\\\"\");\nsolve satisfy;")
  , ("nested annotation", "var 0..9: x :: outer(inner(3));\nsolve satisfy;")
  , ("empty annotation array", "solve :: foo([]) satisfy;")
  , ("bool parameter and set literal", "bool: b = true;\nvar {1, 2}: x;\nsolve satisfy;")
  , ("var set of range domain", "var set of 1..5: s;\nsolve satisfy;")
  , ("var set of set domain", "var set of {1, 2, 3}: s;\nsolve satisfy;")
  , ("maximize objective", "var int: x;\nsolve maximize x;")
  , ("predicate with array parameter",
      "predicate p(array [1..2] of var int: xs);\nvar int: x;\nconstraint p([x, x]);\nsolve satisfy;")
  , ("predicate with open array index",
      "predicate p(array [int] of var int: xs);\nsolve satisfy;")
  , ("predicate with set parameter",
      "predicate p(set of int: s, var 1..3: x);\nsolve satisfy;")
  , ("multiple annotations", "var 0..9: x :: a :: b(1, 2);\nsolve satisfy;")
  , ("annotation with array of literals",
      "var 0..9: x :: foo([1, 2, 3]);\nsolve satisfy;")
  , ("annotation with nested annotation argument",
      "solve :: outer(inner(1), [true, _x]) satisfy;")
  , ("variable with annotation and initializer",
      "var 0..9: x :: my_ann = 3;\nsolve satisfy;")
  , ("constraint with array argument",
      "array [1..2] of var int: xs = [1, 2];\nconstraint int_lin_le([1, 1], xs, 3);\nsolve satisfy;")
  , ("empty predicate parameter list", "predicate p();\nsolve satisfy;")
  , ("string annotation with backslash",
      "var 0..9: x :: note(\"a\\\\b\");\nsolve satisfy;")
  , ("bool variable", "var bool: b;\nconstraint bool_eq(b, true);\nsolve satisfy;")
  , ("set parameter", "set of int: s = {1, 2, 3};\nsolve satisfy;")
  , ("range set parameter", "set of int: s = 1..5;\nsolve satisfy;")
  , ("empty set parameter", "set of int: s = {};\nsolve satisfy;")
  , ("annotation on array variable",
      "array [1..2] of var int: xs :: my_ann = [1, 2];\nsolve satisfy;")
  , ("annotation with string argument",
      "solve :: foo(\"bar\") satisfy;")
  ]

/-- Run one round-trip case; report failures to stderr. -/
private def checkRoundTrip (case : String × String) : IO Bool := do
  let (label, src) := case
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"FAIL {label}: source does not parse: {e}"
      return false
  | .ok m₁ =>
      let printed := pretty m₁
      match Parser.parseModel printed with
      | .error e =>
          IO.eprintln s!"FAIL {label}: printed model does not re-parse: {e}"
          IO.eprintln s!"  printed: {printed}"
          return false
      | .ok m₂ =>
          if reprStr m₁ != reprStr m₂ then
            IO.eprintln s!"FAIL {label}: round-trip mismatch"
            IO.eprintln s!"  printed: {printed}"
            IO.eprintln s!"  first:  {reprStr m₁}"
            IO.eprintln s!"  second: {reprStr m₂}"
            return false
          else
            match Parser.parseModel (pretty m₂) with
            | .error e =>
                IO.eprintln s!"FAIL {label}: second print does not re-parse: {e}"
                return false
            | .ok m₃ =>
                if pretty m₂ != pretty m₃ then
                  IO.eprintln s!"FAIL {label}: printing is not idempotent"
                  IO.eprintln s!"  first print:  {pretty m₂}"
                  IO.eprintln s!"  second print: {pretty m₃}"
                  return false
                else
                  return true

def main : IO UInt32 := do
  let results ← roundTripCases.mapM checkRoundTrip
  if results.all id then
    IO.println s!"passed {roundTripCases.length} pretty-printer round-trip tests"
    return 0
  else
    return 1
