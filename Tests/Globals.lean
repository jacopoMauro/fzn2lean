import LeanFzn.FznGlobals
import LeanFzn.FznParser

/-!
# Global-constraint tests

Three suites:

* **Static** — models that use `fzn_*` global-constraint predicates must be
  well-formed under `fullSig` (and malformed variants must be rejected).
* **Dynamic** — the executable twin `fullInterpB` must agree with the
  intended truth values on concrete argument lists.
* **End-to-end** — a model with global constraints plus a solution string
  accepted/rejected by `checkSolutionFull`.
-/

open LeanFzn

/-- Parse a source string, or panic on failure (all cases are
    syntactically valid). -/
private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- Models using global constraints, all well-formed under `fullSig`
    (parameters must precede variables, per the FlatZinc section order
    this parser enforces). -/
private def staticOk : List (String × String) :=
  [ ("fzn_all_different_int", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_all_different_int(xs);\nsolve satisfy;")
  , ("fzn_all_equal_int", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_all_equal_int(xs);\nsolve satisfy;")
  , ("fzn_global_cardinality", "array [1..2] of int: cover = [1, 2];\narray [1..3] of var 0..9: xs = [1, 2, 3];\narray [1..2] of var 0..3: counts = [1, 1];\nconstraint fzn_global_cardinality(xs, cover, counts);\nsolve satisfy;")
  , ("fzn_cumulative", "array [1..2] of int: d = [2, 2];\narray [1..2] of int: r = [1, 1];\nvar int: cap = 2;\narray [1..2] of var 0..5: s = [0, 1];\nconstraint fzn_cumulative(s, d, r, cap);\nsolve satisfy;")
  , ("fzn_lex_less_int", "array [1..2] of var 0..9: xs = [1, 2];\narray [1..2] of var 0..9: ys = [2, 1];\nconstraint fzn_lex_less_int(xs, ys);\nsolve satisfy;")
  , ("fzn_member_int", "array [1..3] of var 0..9: xs = [1, 2, 3];\nvar 0..9: e;\nconstraint fzn_member_int(xs, e);\nsolve satisfy;")
  , ("fzn_sliding_sum", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_sliding_sum(3, 5, 2, xs);\nsolve satisfy;")
  , ("fzn_disjoint", "var set of 1..5: a;\nvar set of 1..5: b;\nconstraint fzn_disjoint(a, b);\nsolve satisfy;")
  , ("fzn_table_int", "array [1..4] of int: t = [1, 2, 3, 4];\narray [1..2] of var 0..9: xs = [1, 2];\nconstraint fzn_table_int(xs, t);\nsolve satisfy;")
  , ("fzn_nvalue", "var 0..3: n;\narray [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_nvalue(n, xs);\nsolve satisfy;")
  , ("fzn_inverse", "array [1..2] of var 1..2: xs = [1, 2];\narray [1..2] of var 1..2: ys = [1, 2];\nconstraint fzn_inverse(xs, ys);\nsolve satisfy;")
  , ("std and global mixed", "var 0..9: x;\nvar 0..9: y;\narray [1..2] of var 0..9: zs = [1, 4];\nconstraint int_plus(x, y, 5);\nconstraint fzn_increasing_int(zs);\nsolve satisfy;")
  ]

/-- Models that misuse global constraints, all ill-formed under
    `fullSig`. -/
private def staticBad : List (String × String) :=
  [ ("wrong arity", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_all_different_int(xs, xs);\nsolve satisfy;")
  , ("wrong argument type", "var 0..9: x;\nconstraint fzn_all_different_int(x);\nsolve satisfy;")
  , ("set in int-array position", "var set of 1..5: a;\nconstraint fzn_all_different_int(a);\nsolve satisfy;")
  , ("unsupported global", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_span(xs);\nsolve satisfy;")
  , ("unknown predicate", "var 0..9: x;\nconstraint fzn_no_such_global(x);\nsolve satisfy;")
  ]

/-- Dynamic interpretation checks: predicate name, argument list, and
    the expected truth value. -/
private def dynamicCases : List (String × String × List Value × Bool) :=
  [ ("all_different true", "fzn_all_different_int",
      [.array [.int 1, .int 2, .int 3]], true)
  , ("all_different false", "fzn_all_different_int",
      [.array [.int 1, .int 2, .int 2]], false)
  , ("all_different_except_0 true", "fzn_alldifferent_except_0",
      [.array [.int 0, .int 0, .int 1]], true)
  , ("all_different_except_0 false", "fzn_alldifferent_except_0",
      [.array [.int 0, .int 1, .int 1]], false)
  , ("nvalue true", "fzn_nvalue",
      [.int 3, .array [.int 1, .int 2, .int 3]], true)
  , ("nvalue false", "fzn_nvalue",
      [.int 2, .array [.int 1, .int 2, .int 3]], false)
  , ("count_eq", "fzn_count_eq",
      [.array [.int 1, .int 2, .int 1], .int 1, .int 2], true)
  , ("count_geq false", "fzn_count_geq",
      [.array [.int 1, .int 2, .int 1], .int 1, .int 1], false)
  , ("among", "fzn_among",
      [.int 2, .array [.int 1, .int 2, .int 3],
        .setOfInt (.enumeration [1, 2])], true)
  , ("lex_less true", "fzn_lex_less_int",
      [.array [.int 1, .int 2], .array [.int 2, .int 1]], true)
  , ("lex_less false", "fzn_lex_less_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 1]], false)
  , ("increasing", "fzn_increasing_int",
      [.array [.int 1, .int 2, .int 2]], true)
  , ("sort", "fzn_sort",
      [.array [.int 3, .int 1], .array [.int 1, .int 3]], true)
  , ("member true", "fzn_member_int",
      [.array [.int 1, .int 2, .int 3], .int 2], true)
  , ("member false", "fzn_member_int",
      [.array [.int 1, .int 2, .int 3], .int 4], false)
  , ("inverse", "fzn_inverse",
      [.array [.int 2, .int 1], .array [.int 2, .int 1]], true)
  , ("sliding_sum true", "fzn_sliding_sum",
      [.int 3, .int 5, .int 2, .array [.int 1, .int 2, .int 3]], true)
  , ("sliding_sum false", "fzn_sliding_sum",
      [.int 3, .int 4, .int 2, .array [.int 1, .int 2, .int 3]], false)
  , ("table", "fzn_table_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 2, .int 3, .int 4]],
      true)
  , ("cumulative true", "fzn_cumulative",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .int 2], true)
  , ("cumulative false", "fzn_cumulative",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 2, .int 2], .int 2], false)
  , ("disjoint", "fzn_disjoint",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [3, 4])],
      true)
  , ("disjoint false", "fzn_disjoint",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3])],
      false)
  , ("set_member", "fzn_set_member",
      [.setOfInt (.enumeration [1, 2]), .int 2], true)
  , ("wrong shape", "fzn_all_different_int", [.int 1], false)
  ]

/-- End-to-end checks: model, solution string, expected verdict. -/
private def endToEnd : List (String × String × String × Bool) :=
  [ ("all_different accept",
      "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_all_different_int(xs);\nsolve satisfy;",
      "xs = array1d(1..3, [1, 2, 3]);\n----------", true)
  , ("all_different reject",
      "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_all_different_int(xs);\nsolve satisfy;",
      "xs = array1d(1..3, [1, 2, 2]);\n----------", false)
  , ("gcc accept",
      "array [1..2] of int: cover = [1, 2];\narray [1..3] of var 0..9: xs = [1, 2, 3];\narray [1..2] of var 0..3: counts = [1, 1];\nconstraint fzn_global_cardinality(xs, cover, counts);\nsolve satisfy;",
      "xs = array1d(1..3, [1, 2, 3]);\ncounts = array1d(1..2, [1, 1]);\n----------",
      true)
  , ("gcc reject",
      "array [1..2] of int: cover = [1, 2];\narray [1..3] of var 0..9: xs = [1, 2, 3];\narray [1..2] of var 0..3: counts = [1, 1];\nconstraint fzn_global_cardinality(xs, cover, counts);\nsolve satisfy;",
      "xs = array1d(1..3, [1, 2, 3]);\ncounts = array1d(1..2, [2, 1]);\n----------",
      false)
  , ("mixed std/global accept",
      "var 0..9: x;\nvar 0..9: y;\narray [1..2] of var 0..9: zs = [1, 4];\nconstraint int_plus(x, y, 5);\nconstraint fzn_increasing_int(zs);\nsolve satisfy;",
      "x = 2;\ny = 3;\nzs = array1d(1..2, [1, 4]);\n----------", true)
  , ("mixed std/global reject (std constraint)",
      "var 0..9: x;\nvar 0..9: y;\narray [1..2] of var 0..9: zs = [1, 4];\nconstraint int_plus(x, y, 5);\nconstraint fzn_increasing_int(zs);\nsolve satisfy;",
      "x = 2;\ny = 2;\nzs = array1d(1..2, [1, 4]);\n----------", false)
  , ("mixed std/global reject (global constraint)",
      "var 0..9: x;\nvar 0..9: y;\narray [1..2] of var 0..9: zs = [1, 4];\nconstraint int_plus(x, y, 5);\nconstraint fzn_increasing_int(zs);\nsolve satisfy;",
      "x = 2;\ny = 3;\nzs = array1d(1..2, [4, 1]);\n----------", false)
  , ("sets disjoint accept",
      "var set of 1..5: a;\nvar set of 1..5: b;\nconstraint fzn_disjoint(a, b);\nsolve satisfy;",
      "a = {1, 2};\nb = {3, 4};\n----------", true)
  , ("sets disjoint reject",
      "var set of 1..5: a;\nvar set of 1..5: b;\nconstraint fzn_disjoint(a, b);\nsolve satisfy;",
      "a = {1, 2};\nb = {2, 3};\n----------", false)
  , ("unparseable solution rejected",
      "var 0..9: x;\nconstraint fzn_member_int([1, 2, 3], x);\nsolve satisfy;",
      "x = ;\n----------", false)
  ]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, src) in staticOk do
    if !(wellFormedB Globals.fullSig (parseOrPanic src)) then
      IO.eprintln s!"FAIL (expected well-formed): {name}"
      failures := failures + 1
  for (name, src) in staticBad do
    if wellFormedB Globals.fullSig (parseOrPanic src) then
      IO.eprintln s!"FAIL (expected ill-formed): {name}"
      failures := failures + 1
  for (name, pred, args, expected) in dynamicCases do
    let holds : Bool := Globals.fullInterpB ⟨pred⟩ args
    if holds != expected then
      IO.eprintln s!"FAIL (dynamic): {name}: got {holds}, expected {expected}"
      failures := failures + 1
  for (name, msrc, sol, expected) in endToEnd do
    let verdict := Globals.checkSolutionFull (parseOrPanic msrc) sol
    if verdict != expected then
      IO.eprintln s!"FAIL (end-to-end): {name}: got {verdict}, expected {expected}"
      failures := failures + 1
  let total := staticOk.length + staticBad.length + dynamicCases.length +
    endToEnd.length
  if failures == 0 then
    IO.println s!"passed {total} globals tests"
    return 0
  else
    IO.eprintln s!"{failures} globals test(s) failed"
    return 1
