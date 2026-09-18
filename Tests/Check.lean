import LeanFzn

open LeanFzn

/-!
# CLI tests for the `check` subcommand

End-to-end tests of the front door `checkModelSolution` (via the CLI's
`check` path): each failure mode must be classified, and the exit
codes must match the documented contract:

* 0 — accepted;
* 1 — unsatisfied (well-formed model, well-formed solution string, but
  a domain/initializer/constraint condition fails);
* 2 — malformed model (static well-formedness fails);
* 3 — unsupported predicate (a constraint uses a name outside
  `fullCheckableNames`);
* 4 — malformed solution string (parse failure, parameter or unknown
  reassignment, duplicate assignment).

The tests exercise `checkModelSolution` directly (the same function
`main` calls), plus one compiled CLI round-trip via process spawn.
-/

open LeanFzn.Check LeanFzn.Globals LeanFzn.Solution

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"parse error: {e}"

/-- A well-formed model with parameters, an array, and several
    standard and global constraints. -/
private def goodModel : String :=
  "int: k = 3;\n\
   array [1..3] of int: ks = [1, 2, 3];\n\
   var 0..9: x;\n\
   var 0..9: y;\n\
   array [1..2] of var 0..9: xs = [x, y];\n\
   constraint int_plus(x, k, 7);\n\
   constraint int_le(y, x);\n\
   constraint fzn_all_different_int(xs);\n\
   solve satisfy;"

/-- A model that is statically ill-formed: duplicate variable
    declaration. -/
private def dupModel : String :=
  "var 0..9: x;\n\
   var 0..9: x;\n\
   solve satisfy;"

/-- A model that is statically ill-formed: constraint uses an
    unresolvable predicate. -/
private def unknownPredModel : String :=
  "var 0..9: x;\n\
   constraint notapred(x);\n\
   solve satisfy;"

/-- A model using an intentionally unsupported global (`fzn_span`
    needs optional variables, outside the fragment). -/
private def unsupportedModel : String :=
  "var 1..4: u;\n\
   var 1..4: v;\n\
   constraint fzn_span([u, v]);\n\
   solve satisfy;"

/-- A model declaring a predicate and using it: statically
    well-formed, but the fragment gives it no dynamic meaning. -/
private def declaredPredModel : String :=
  "predicate p(var int: a);\n\
   var 0..9: x;\n\
   constraint p(x);\n\
   solve satisfy;"

/-- Expected outcome and the check that produced it. -/
structure Case where
  name : String
  model : String
  sol : String
  expected : Outcome

private def cases : List Case :=
  [ { name := "accepted"
    , model := goodModel
    , sol := "x = 4;\ny = 3;\nxs = array1d(1..2, [4, 3]);\n----------"
    , expected := .accepted }
  , { name := "constraint violated (4 + 3 ≠ 7)"
    , model := goodModel
    , sol := "x = 5;\ny = 3;\nxs = array1d(1..2, [5, 3]);\n----------"
    , expected := .unsatisfied }
  , { name := "domain violated (y = 10 out of 0..9)"
    , model := goodModel
    , sol := "x = 4;\ny = 10;\nxs = array1d(1..2, [4, 10]);\n----------"
    , expected := .unsatisfied }
  , { name := "global violated (xs not all-different)"
    , model := goodModel
    , sol := "x = 4;\ny = 4;\nxs = array1d(1..2, [4, 4]);\n----------"
    , expected := .unsatisfied }
  , { name := "duplicate model (static)"
    , model := dupModel
    , sol := "x = 1;\n----------"
    , expected := .malformedModel "static well-formedness failed" }
  , { name := "unknown predicate (reported as unsupported)"
    , model := unknownPredModel
    , sol := "x = 1;\n----------"
    , expected := .unsupportedPredicate "notapred" }
  , { name := "unsupported global"
    , model := unsupportedModel
    , sol := "u = 1;\nv = 2;\n----------"
    , expected := .unsupportedPredicate "fzn_span" }
  , { name := "declared predicate has no dynamic meaning"
    , model := declaredPredModel
    , sol := "x = 1;\n----------"
    , expected := .unsupportedPredicate "p" }
  , { name := "solution reassigns a parameter"
    , model := goodModel
    , sol := "k = 5;\nx = 2;\ny = 2;\nxs = array1d(1..2, [2, 2]);\n----------"
    , expected := .malformedSolution
        "assigns a parameter, an unknown name, or a name twice" }
  , { name := "solution assigns an unknown name"
    , model := goodModel
    , sol := "x = 4;\ny = 3;\nz = 1;\nxs = array1d(1..2, [4, 3]);\n----------"
    , expected := .malformedSolution
        "assigns a parameter, an unknown name, or a name twice" }
  , { name := "solution assigns a name twice"
    , model := goodModel
    , sol := "x = 4;\nx = 3;\ny = 3;\nxs = array1d(1..2, [4, 3]);\n----------"
    , expected := .malformedSolution
        "assigns a parameter, an unknown name, or a name twice" }
  , { name := "solution is garbage"
    , model := goodModel
    , sol := "garbage\n----------"
    , expected := .malformedSolution "no solution assignment found" }
  ]

/-- The exit code the CLI assigns to each outcome. -/
def Outcome.exitCode : Outcome → UInt32
  | .accepted => 0
  | .unsatisfied => 1
  | .malformedModel _ => 2
  | .unsupportedPredicate _ => 3
  | .malformedSolution _ => 4

def main : IO UInt32 := do
  let mut ok := true
  for c in cases do
    let m := parseOrPanic c.model
    let outcome := checkModelSolution m c.sol
    if outcome != c.expected then
      IO.eprintln s!"FAIL {c.name}: expected {c.expected}, got {outcome}"
      ok := false
    else
      IO.println s!"ok {c.name}: {outcome}"
  -- the wrapper must agree with the old checker on accepting solutions
  -- (regression: the CLI used to call checkSolutionFull directly)
  let m := parseOrPanic goodModel
  let goodSol := "x = 4;\ny = 3;\nxs = array1d(1..2, [4, 3]);\n----------"
  if (checkModelSolution m goodSol != .accepted) then
    IO.eprintln "FAIL: wrapper rejects a valid solution"
    ok := false
  -- the parameter-cheating string the old checker wrongly accepted
  let cheat := "k = 5;\nx = 2;\ny = 2;\nxs = array1d(1..2, [2, 2]);\n----------"
  if !(checkModelSolution m cheat).toString.startsWith "malformed solution" then
    IO.eprintln "FAIL: wrapper should classify the cheating string as malformed"
    ok := false
  if ok then
    IO.println s!"passed {cases.length} CLI check tests"
    return 0
  else
    return 1
