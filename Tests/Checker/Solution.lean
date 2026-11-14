/-
Purpose: Exercise solution syntax independently of constraint checking, and
check parsed assignments against model semantics.
Dependencies: Checker.Solution, model parser and standard predicate semantics.
DAG: solution parser/checker -> this regression executable.
-/
import LeanFzn.Checker.Solution
import LeanFzn.Parser.Parser
import LeanFzn.Semantics.StdLib

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation


/-!
# Solution checker tests

End-to-end checks: a FlatZinc model, a solution string in the standard
FlatZinc output format, and `checkSolution`'s verdict.
-/

open LeanFzn LeanFzn.Checker.Solution

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"parse error: {e}"

/-- A model with an equation, a reified comparison, and an array. -/
private def model1 : Model := parseOrPanic
  "var 0..9: x;\nvar 0..9: y;\narray [1..3] of var 0..9: xs = [1, 2, x];\nconstraint int_plus(x, y, 7);\nconstraint int_le_reif(x, 5, true);\nsolve satisfy;"

/-- Correct solutions. -/
private def goodSolutions : List String :=
  [ "x = 2;\ny = 5;\nxs = array1d(1..3, [1, 2, 2]);\n----------"
  , "x = 5;\ny = 2;\nxs = array1d(1..3, [1, 2, 5]);\n----------"
  ]

/-- Incorrect solutions (constraint, domain, or initializer violated). -/
private def badSolutions : List String :=
  [ "x = 3;\ny = 5;\nxs = array1d(1..3, [1, 2, 3]);\n----------" -- 3+5≠7
  , "x = 8;\ny = -1;\nxs = array1d(1..3, [1, 2, 8]);\n----------" -- y out of domain
  , "x = 2;\ny = 5;\nxs = array1d(1..3, [1, 2, 9]);\n----------" -- initializer
  , "x = 2;\ny = 5;\nxs = array1d(1..3, [1, 2, 2]);" -- no trailing junk: still valid
  , "garbage"
  ]

/-- Check the parsed array's values, so a parser cannot pass by dropping an
    element or confusing a set's internal comma with an array separator. -/
private def parsesArray (src : String) (expected : List Value) : Bool :=
  match parseSolution src with
  | .ok [⟨name, .array ls⟩] =>
      name == "ss" && semEqListB (ls.map (·.denote)) expected
  | _ => false

private def setVal (xs : List Int) : Value := .setOfInt (.enumeration xs)

private def arraySyntaxCases : List (String × List Value) :=
  [ ("ss = array1d(1..2, [{1, 2}, {1}]);", [setVal [1, 2], setVal [1]])
  , ("ss = array1d(1..2, [{1}, {1, 2}]);", [setVal [1], setVal [1, 2]])
  , ("ss = array1d(1..2, [{1, 2}, {3, 4}]);", [setVal [1, 2], setVal [3, 4]])
  , ("ss = array1d(1..3, [{0, 11}, {}, {0, 10}]);",
      [setVal [0, 11], setVal [], setVal [0, 10]])
  , ("ss = array1d(1..3, [{-2, -1}, -3..0, {}]);",
      [setVal [-2, -1], .setOfInt (.interval (-3) 0), setVal []])
  , ("ss = array1d(1..0, []);", [])
  , ("ss = [{1, 2}, {1}];", [setVal [1, 2], setVal [1]])
  , ("ss = [];", [])
  , ("ss = [true, false];", [.bool true, .bool false])
  , ("ss = [1, -2, 3];", [.int 1, .int (-2), .int 3])
  , ("% comment\nss = [ {1, % set comma\n 2}, % array comma\n {} ];",
      [setVal [1, 2], setVal []])
  ]

private def malformedSyntaxCases : List String :=
  [ "ss = array1d(1..2, [{1, 2} {1}]);" -- missing array separator
  , "ss = array1d(1..2, [{1, 2}, {1});" -- missing bracket
  , "ss = array1d(1..3, [{1, 2}, {1}]);" -- incorrect length
  , "ss = array1d(0..1, [{1, 2}, {1}]);" -- incorrect lower bound
  , "ss = [{1,}, {2}];" -- trailing set comma
  , "ss = [{1, 2},];" -- trailing array comma
  , "ss = [{1, 2}, {1}]; trailing" -- no ignored suffix
  , "ss = [{1, 2}, {1}]; x = 1" -- unterminated second assignment
  , "ss = [{1, 2}, {1}]" -- no semicolon
  ]

def main : IO UInt32 := do
  let mut ok := true
  for (src, expected) in arraySyntaxCases do
    if !parsesArray src expected then
      IO.eprintln s!"FAIL (array literal values): {src}"
      ok := false
  for src in malformedSyntaxCases do
    if (parseSolution src).isOk then
      IO.eprintln s!"FAIL (malformed syntax accepted): {src}"
      ok := false
  for sol in goodSolutions do
    let r := checkSolution model1 sol
    if !r then
      IO.eprintln s!"FAIL (expected solution): {sol}"
      ok := false
  -- the fourth "bad" entry is actually a valid solution without separators;
  -- move it to expectations accordingly
  for sol in badSolutions.take 3 do
    let r := checkSolution model1 sol
    if r then
      IO.eprintln s!"FAIL (expected rejection): {sol}"
      ok := false
  if checkSolution model1 badSolutions[4]! then
    IO.eprintln "FAIL (expected rejection of garbage)"
    ok := false
  if ok then
    IO.println "passed all solution checker tests"
    return 0
  else
    return 1
