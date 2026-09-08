import LeanFzn

/-!
# Well-Formedness Smoke Tests

Checks the static semantics (`WellFormed`) of `FznSemantics.lean` against
the rules resolved in `specification/flatzinc_specification_assumptions.md`
(R1-R8, A3, A5).  Each case is a model that parses, so only the static
rules decide acceptance.
-/

open LeanFzn

/-- The external signature environment used by the tests: the standard
    FlatZinc builtins used below, with their MiniZinc signatures. -/
def testSig : SigEnv := fun x =>
  match x.name with
  | "int_eq" => some [.basic (.par .int), .basic (.var (.par .int))]
  | "bool_eq" => some [.basic (.par .bool), .basic (.var (.par .bool))]
  | "set_in" => some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))]
  | "all_different" => some [.array (.range ⟨3⟩) (.var (.par .int))]
  | _ => none

/-- Parse a source string, or panic on failure (all cases are syntactically
    valid). -/
def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- Check that a source is well-formed under `testSig`. -/
def checkWF (src : String) : Bool :=
  wellFormedB testSig (parseOrPanic src)

/-- Well-formed cases. -/
def wfCases : List (String × String) :=
  [ ("minimal model", "solve satisfy;")
  , ("parameter and variable", "int: n = 3;\nvar 0..10: x;\nsolve satisfy;")
  , ("reversed range is empty, not ill-formed (R1)", "var 5..1: x;\nsolve satisfy;")
  , ("empty set domain", "var set of {}: s;\nsolve satisfy;")
  , ("array lengths match (R3)", "array [1..3] of int: xs = [1, 2, 3];\nsolve satisfy;")
  , ("empty array with empty index set (R1/R3)", "array [1..0] of int: xs = [];\nsolve satisfy;")
  , ("variable array with initializer", "array [1..2] of var 0..9: ys = [1, 2];\nsolve satisfy;")
  , ("alias to a variable (R6)", "var 0..10: x;\nvar int: y = x;\nsolve satisfy;")
  , ("alias to a parameter (par-to-var coercion)", "int: n = 3;\nvar int: y = n;\nsolve satisfy;")
  , ("int objective (R7)", "var 0..10: x;\nsolve minimize x;")
  , ("constant int objective (R7)", "int: n = 1;\nsolve maximize n;")
  , ("declared predicate used with matching args (R8)", "predicate p(var int: x);\nvar 0..9: x;\nconstraint p(x);\nsolve satisfy;")
  , ("builtin with par-to-var coercion (R8)", "int: n = 3;\nvar 0..9: x;\nconstraint int_eq(n, x);\nsolve satisfy;")
  , ("builtin array constraint (R8)", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint all_different(xs);\nsolve satisfy;")
  , ("forward reference (R5)", "var int: y = x;\nvar 0..10: x;\nsolve satisfy;")
  , ("set constraint", "var set of {1, 2}: s;\nvar 1..2: x;\nconstraint set_in(x, s);\nsolve satisfy;")
  , ("var argument in var position of declared predicate (R15)",
    "predicate p(var int: x);\nvar 0..9: x;\nconstraint p(x);\nsolve satisfy;")
  , ("par-to-var coercion in declared predicate call (R15)",
    "predicate p(var int: x);\nint: n = 3;\nconstraint p(n);\nsolve satisfy;")
  , ("fixed initializer (R6)", "var 0..9: x;\nvar int: y = 5;\nsolve satisfy;")
  , ("set parameter (R18)", "set of int: s = {1, 2};\nsolve satisfy;")
  , ("bool parameter (R18)", "bool: b = true;\nsolve satisfy;")
  , ("open array parameter accepts any length (R3)",
    "predicate p(array [int] of int: xs);\narray [1..2] of int: ys = [1, 2];\nconstraint p(ys);\nsolve satisfy;")
  , ("model declaration shadows builtin signature (R8)",
    "predicate int_eq(var int: x);\nvar 0..9: x;\nconstraint int_eq(x);\nsolve satisfy;")
  ]

/-- Ill-formed cases, each violating exactly one static rule. -/
def illFormedCases : List (String × String) :=
  [ ("duplicate parameter (R4)", "int: n = 1;\nint: n = 2;\nsolve satisfy;")
  , ("duplicate variable (R4)", "var 0..9: x;\nvar 0..9: x;\nsolve satisfy;")
  , ("parameter and variable share a name (R4)", "int: x = 1;\nvar 0..9: x;\nsolve satisfy;")
  , ("duplicate predicate (R4)", "predicate p(int: x);\npredicate p(int: y);\nsolve satisfy;")
  , ("duplicate predicate formals (R4)", "predicate p(int: x, int: x);\nsolve satisfy;")
  , ("wrong parameter type (R18)", "int: n = true;\nsolve satisfy;")
  , ("wrong parameter array element type (R18)", "array [1..2] of int: xs = [1, true];\nsolve satisfy;")
  , ("parameter array length mismatch (R20)", "array [1..3] of int: xs = [1, 2];\nsolve satisfy;")
  , ("variable array length mismatch (R22)", "array [1..3] of var 0..9: xs = [1, 2];\nsolve satisfy;")
  , ("bool objective (R7)", "var bool: b;\nsolve minimize b;")
  , ("set objective (R7)", "var set of {1}: s;\nsolve maximize s;")
  , ("undeclared constraint predicate (R13)", "var 0..9: x;\nconstraint no_such_pred(x);\nsolve satisfy;")
  , ("wrong constraint arity (R14)", "int: n = 3;\nvar 0..9: x;\nconstraint int_eq(n);\nsolve satisfy;")
  , ("wrong constraint argument type (R15)", "var bool: b;\nconstraint int_eq(b, b);\nsolve satisfy;")
  , ("var argument in par position (R15)", "var 0..9: x;\nconstraint int_eq(x, x);\nsolve satisfy;")
  , ("undeclared initializer reference (R5/R12)", "var int: y = no_such_var;\nsolve satisfy;")
  , ("undeclared objective reference (R5/R12)", "solve minimize no_such_var;")
  , ("scalar fills array parameter (R15)", "predicate p(array [1..2] of int: xs);\nint: n = 1;\nconstraint p(n);\nsolve satisfy;")
  , ("array fills scalar parameter (R15)", "predicate p(int: x);\narray [1..2] of int: xs = [1, 2];\nconstraint p(xs);\nsolve satisfy;")
  , ("array length mismatch in constraint (R3/R14)", "array [1..2] of int: xs = [1, 2];\nconstraint all_different(xs);\nsolve satisfy;")
  , ("var argument in par position of declared predicate (R15)",
    "predicate p(int: x);\nvar 0..9: x;\nconstraint p(x);\nsolve satisfy;")
  , ("arity mismatch in declared predicate call (R14)",
    "predicate p(var int: x);\nvar 0..9: x;\nconstraint p(x, x);\nsolve satisfy;")
  , ("array identifier as scalar initializer (R26)",
    "array [1..2] of var 0..9: xs = [1, 2];\nvar int: y = xs;\nsolve satisfy;")
  , ("set initializer for int variable (R26)",
    "var set of {1, 2}: s;\nvar int: y = s;\nsolve satisfy;")
  , ("initializer type mismatch (R26)", "var 0..9: x;\nvar bool: b = x;\nsolve satisfy;")
  , ("set parameter with wrong element type (R18)", "set of int: s = true;\nsolve satisfy;")
  ]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, src) in wfCases do
    if !checkWF src then
      IO.eprintln s!"FAIL (expected well-formed): {name}"
      failures := failures + 1
  for (name, src) in illFormedCases do
    if checkWF src then
      IO.eprintln s!"FAIL (expected ill-formed): {name}"
      failures := failures + 1
  if failures == 0 then
    IO.println s!"passed {wfCases.length + illFormedCases.length} well-formedness tests"
    return 0
  else
    IO.eprintln s!"{failures} well-formedness test(s) failed"
    return 1
