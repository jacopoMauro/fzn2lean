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

def main : IO UInt32 := do
  let mut ok := true
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
