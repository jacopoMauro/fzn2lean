import LeanFzn.FznStdLib
import LeanFzn.FznParser

/-!
# Standard-library tests

Two suites:

* **Static** — models that use standard predicates must be well-formed
  under `stdSig` (and malformed variants must be rejected).
* **Dynamic** — the executable twin `stdInterpB` must agree with the
  intended truth values on concrete argument lists.  Only the decidable
  interpretations are exercised here; the extensional set predicates
  (`set_eq`, `set_subset`, `set_union`, `set_intersection`, `set_diff`)
  quantify over all integers and are covered by signature checking only.
-/

open LeanFzn

/-- Parse a source string, or panic on failure (all cases are
    syntactically valid). -/
private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- Models using standard predicates, all well-formed under `stdSig`. -/
private def staticOk : List (String × String) :=
  [ ("int_eq", "var 0..9: x;\nconstraint int_eq(x, 3);\nsolve satisfy;")
  , ("int_plus", "var 0..9: x;\nvar 0..9: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;")
  , ("bool_not with par literal", "var bool: b;\nconstraint bool_not(b, false);\nsolve satisfy;")
  , ("all_different", "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint all_different(xs);\nsolve satisfy;")
  , ("set_in", "var set of {1, 2}: s;\nvar 1..2: x;\nconstraint set_in(x, s);\nsolve satisfy;")
  , ("int_le_reif", "var 0..9: x;\nvar bool: b;\nconstraint int_le_reif(x, 5, b);\nsolve satisfy;")
  , ("bool_clause", "array [1..2] of var bool: bs = [true, false];\narray [1..2] of var bool: cs = [false, false];\nconstraint bool_clause(bs, cs);\nsolve satisfy;")
  , ("dom", "var 0..9: x;\nconstraint dom(x, {1, 3, 5});\nsolve satisfy;")
  , ("int_lin_eq", "array [1..2] of int: as_ = [1, 2];\narray [1..2] of var 0..9: xs = [1, 2];\nvar 0..9: r;\nconstraint int_lin_eq(as_, xs, r);\nsolve satisfy;")
  , ("int_abs", "var -9..9: x;\nvar 0..9: y;\nconstraint int_abs(x, y);\nsolve satisfy;")
  , ("array_int_maximum", "array [1..3] of var 0..9: xs = [1, 2, 3];\nvar 0..9: m;\nconstraint array_int_maximum(m, xs);\nsolve satisfy;")
  ]

/-- Models that misuse standard predicates, all ill-formed under `stdSig`. -/
private def staticBad : List (String × String) :=
  [ ("wrong arity", "var 0..9: x;\nconstraint int_eq(x);\nsolve satisfy;")
  , ("wrong argument type", "var bool: b;\nconstraint int_eq(b, b);\nsolve satisfy;")
  , ("unknown predicate", "var 0..9: x;\nconstraint no_such(x);\nsolve satisfy;")
  , ("var in par array position", "array [1..2] of var 0..9: xs = [1, 2];\nvar 0..9: r;\nconstraint int_lin_eq(xs, xs, r);\nsolve satisfy;")
  ]

/-- Dynamic interpretation checks: predicate name, argument list, and the
    expected truth value. -/
private def dynamicCases : List (String × String × List Value × Bool) :=
  [ ("int_eq true", "int_eq", [.int 3, .int 3], true)
  , ("int_eq false", "int_eq", [.int 3, .int 4], false)
  , ("int_ne", "int_ne", [.int 3, .int 4], true)
  , ("int_le eq", "int_le", [.int 3, .int 3], true)
  , ("int_le false", "int_le", [.int 4, .int 3], false)
  , ("int_lt", "int_lt", [.int 3, .int 4], true)
  , ("int_ge", "int_ge", [.int 3, .int 3], true)
  , ("int_gt", "int_gt", [.int 4, .int 3], true)
  , ("int_plus true", "int_plus", [.int 2, .int 3, .int 5], true)
  , ("int_plus false", "int_plus", [.int 2, .int 3, .int 6], false)
  , ("int_minus", "int_minus", [.int 5, .int 3, .int 2], true)
  , ("int_times", "int_times", [.int 2, .int 3, .int 6], true)
  , ("int_div", "int_div", [.int 7, .int 2, .int 3], true)
  , ("int_mod", "int_mod", [.int 7, .int 2, .int 1], true)
  , ("int_min", "int_min", [.int 2, .int 3, .int 2], true)
  , ("int_max", "int_max", [.int 2, .int 3, .int 3], true)
  , ("int_abs", "int_abs", [.int (-5), .int 5], true)
  , ("bool_not", "bool_not", [.bool true, .bool false], true)
  , ("bool_and true", "bool_and", [.bool true, .bool true, .bool true], true)
  , ("bool_and false", "bool_and", [.bool true, .bool false, .bool true], false)
  , ("bool_or", "bool_or", [.bool true, .bool false, .bool true], true)
  , ("bool_xor", "bool_xor", [.bool true, .bool false, .bool true], true)
  , ("all_different true", "all_different",
      [.array [.int 1, .int 2, .int 3]], true)
  , ("all_different false", "all_different",
      [.array [.int 1, .int 2, .int 1]], false)
  , ("all_different_except_0 true", "all_different_except_0",
      [.array [.int 0, .int 0, .int 1]], true)
  , ("all_different_except_0 false", "all_different_except_0",
      [.array [.int 0, .int 1, .int 1]], false)
  , ("set_in true", "set_in", [.int 2, .setOfInt (.enumeration [1, 2])], true)
  , ("set_in false", "set_in", [.int 3, .setOfInt (.enumeration [1, 2])], false)
  , ("set_in interval", "set_in", [.int 3, .setOfInt (.interval 1 5)], true)
  , ("dom", "dom", [.int 3, .setOfInt (.enumeration [1, 3, 5])], true)
  , ("set_card enumeration", "set_card",
      [.setOfInt (.enumeration [1, 2]), .int 2], true)
  , ("set_card interval", "set_card",
      [.setOfInt (.interval 1 5), .int 5], true)
  , ("set_card reversed interval", "set_card",
      [.setOfInt (.interval 5 1), .int 0], true)
  , ("int_lin_eq true", "int_lin_eq",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11], true)
  , ("int_lin_eq false", "int_lin_eq",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], false)
  , ("int_lin_le true", "int_lin_le",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11], true)
  , ("int_lin_le false", "int_lin_le",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], false)
  , ("int_lin_ne", "int_lin_ne",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], true)
  , ("array_int_maximum", "array_int_maximum",
      [.int 3, .array [.int 1, .int 2, .int 3]], true)
  , ("array_int_minimum", "array_int_minimum",
      [.int 1, .array [.int 1, .int 2, .int 3]], true)
  , ("bool_clause true", "bool_clause",
      [.array [.bool true], .array [.bool false]], true)
  , ("bool_clause neg-true", "bool_clause",
      [.array [.bool false], .array [.bool false]], true)
  , ("bool_clause pos-neg-false", "bool_clause",
      [.array [.bool false], .array [.bool true]], false)
  , ("int_eq_reif true", "int_eq_reif", [.int 3, .int 3, .bool true], true)
  , ("int_eq_reif false", "int_eq_reif", [.int 3, .int 4, .bool true], false)
  , ("int_eq_reif negated", "int_eq_reif", [.int 3, .int 4, .bool false], true)
  , ("set_in_reif", "set_in_reif",
      [.int 2, .setOfInt (.enumeration [1, 2]), .bool true], true)
  , ("true", "true", [], true)
  , ("wrong shape", "int_eq", [.bool true], false)
  ]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, src) in staticOk do
    if !(wellFormedB stdSig (parseOrPanic src)) then
      IO.eprintln s!"FAIL (expected well-formed): {name}"
      failures := failures + 1
  for (name, src) in staticBad do
    if wellFormedB stdSig (parseOrPanic src) then
      IO.eprintln s!"FAIL (expected ill-formed): {name}"
      failures := failures + 1
  for (name, pred, args, expected) in dynamicCases do
    let holds : Bool := stdInterpB ⟨pred⟩ args
    if holds != expected then
      IO.eprintln s!"FAIL (dynamic): {name}: got {holds}, expected {expected}"
      failures := failures + 1
  let total := staticOk.length + staticBad.length + dynamicCases.length
  if failures == 0 then
    IO.println s!"passed {total} stdlib tests"
    return 0
  else
    IO.eprintln s!"{failures} stdlib test(s) failed"
    return 1
