import LeanFzn.Parser
import LeanFzn.Checker

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation


/-!
# Tests for the verified fast paths (PLAN item 4)

Differential tests of the hash-dispatched front door
(`checkModelSolutionFast`), the prepared checker (`prepareModel` +
`checkPreparedSolution`), and the hash-set name gate
(`firstUnsupportedFast`): each must return exactly the verified
`checkModelSolution` outcome on accepting, rejecting, and
error-classifying inputs.
-/

open LeanFzn LeanFzn.Checker LeanFzn.Semantics.Globals LeanFzn.Checker.Globals LeanFzn.Checker.Solution

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"parse error: {e}"

/-- The reference model: parameters, arrays, several global
    predicates, standard predicates. -/
private def goodModelSrc : String :=
  "int: k = 3;\n\
   var 1..9: x;\n\
   var 1..9: y;\n\
   array [1..2] of var 1..9: xs = [x, y];\n\
   constraint int_le(x, y);\n\
   constraint fzn_all_different_int(xs);\n\
   constraint fzn_at_least_int(1, xs, k);\n\
   solve satisfy;\n"

private def goodModel : Model := parseOrPanic goodModelSrc

/-- A model with an unsupported predicate. -/
private def badPredModel : Model := parseOrPanic
  "var 1..9: x;\nconstraint fzn_span([x]);\nsolve satisfy;\n"

/-- A statically ill-formed model (duplicate variable). -/
private def malformedModel : Model := parseOrPanic
  "var 1..9: x;\nvar 1..9: x;\nsolve satisfy;\n"

/-- Cases: (label, model, solution, expected outcome). -/
private def cases : List (String × Model × String × Outcome) :=
  [ ("accept globals", goodModel, "x = 3;\ny = 5;\nxs = array1d(1..2, [3, 5]);\n----------",
      .accepted)
  , ("reject constraint", goodModel, "x = 5;\ny = 4;\nxs = array1d(1..2, [5, 4]);\n----------",
      .unsatisfied)
  , ("reject domain", goodModel, "x = 10;\ny = 4;\nxs = array1d(1..2, [10, 4]);\n----------",
      .unsatisfied)
  , ("reject parameter cheat", goodModel, "k = 9;\nx = 2;\ny = 2;\nxs = array1d(1..2, [2, 2]);\n----------",
      .malformedSolution "assigns a parameter, an unknown name, or a name twice")
  , ("malformed solution", goodModel, "garbage\n----------",
      .malformedSolution "expected solution line 'name = value;'")
  , ("unsupported predicate", badPredModel, "x = 1;\n----------",
      .unsupportedPredicate "fzn_span")
  , ("malformed model", malformedModel, "x = 1;\n----------",
      .malformedModel "static well-formedness failed")
  ]

def main : IO UInt32 := do
  let mut ok := true
  for (label, m, sol, expected) in cases do
    let p := prepareModel m
    let rSlow := checkModelSolution m sol
    let rFast := checkModelSolutionFast m sol
    let rPrep := checkPreparedSolution p sol
    if rSlow != expected then
      IO.eprintln s!"FAIL {label}: slow front door returned {rSlow}, expected {expected}"
      ok := false
    if rFast != expected then
      IO.eprintln s!"FAIL {label}: fast front door returned {rFast}, expected {expected}"
      ok := false
    if rPrep != expected then
      IO.eprintln s!"FAIL {label}: prepared checker returned {rPrep}, expected {expected}"
      ok := false
    if rSlow == expected && rFast == expected && rPrep == expected then
      IO.println s!"ok {label}: {expected}"
  -- the fast name gate agrees with the slow gate on both models
  if firstUnsupportedFast goodModel != firstUnsupported goodModel then
    IO.eprintln "FAIL: firstUnsupportedFast disagrees on the good model"
    ok := false
  if firstUnsupportedFast badPredModel != firstUnsupported badPredModel then
    IO.eprintln "FAIL: firstUnsupportedFast disagrees on the unsupported-predicate model"
    ok := false
  -- the dispatcher agrees with fullInterpB on all 218 names
  let mut dispatchOk := true
  for n in fullCheckableNames do
    if preparedInterpB (Ident.mk n) [] != fullInterpB (Ident.mk n) [] then
      dispatchOk := false
  if !dispatchOk then
    IO.eprintln "FAIL: preparedInterpB disagrees with fullInterpB on some checkable name"
    ok := false
  else
    IO.println s!"ok preparedInterpB agrees on {fullCheckableNames.length} names"
  -- unknown names yield false on both
  if preparedInterpB (Ident.mk "no_such_pred") [] != fullInterpB (Ident.mk "no_such_pred") [] then
    IO.eprintln "FAIL: preparedInterpB disagrees on an unknown name"
    ok := false
  if ok then
    IO.println s!"passed {cases.length} fast-path differential tests"
    return 0
  else
    return 1
