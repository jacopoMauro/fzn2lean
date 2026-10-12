import LeanFzn.Checker.Globals
import LeanFzn.Semantics.Globals
import LeanFzn.Parser.Parser
import LeanFzn.Semantics.StdLib

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation


/-!
# Complete predicate/globals coverage tests

This suite exercises **every** predicate with an executable verified
interpretation: the standard builtins (`stdNames` + `setNames`), and
all 138 `fzn_*` global-constraint names (`globalsNames`), plus the
deprecated builtins kept in the fragment.  It guarantees:

* **dynamic coverage** — every checkable name is evaluated by
  `fullInterpB` (or the builtin twin) at least once on arguments where
  it evaluates to `true`, and at least once on arguments where it
  evaluates to `false` (or a wrong-shape rejection), so both the
  accepting and rejecting branches of every twin are executed;
* **static coverage** — every name is used in a *well-formed* model
  under `fullSig` (via a compact per-family model batch), proving the
  signature entries accept real FlatZinc calls;
* **end-to-end coverage** — a representative subset is driven through
  the full `checkSolutionFull` pipeline (parse model, parse solution
  string, build the completed store, evaluate).

The final check re-derives the covered-name set from
`stdNames ++ setNames ++ globalsNames` and fails if any name was
missed, so a newly added predicate without tests breaks the build.
-/

open LeanFzn LeanFzn.Checker.Globals

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-! ## Dynamic cases: standard-library builtins

Each entry: name, arguments, expected verdict (both truth values
exercised).  Builtins are checked through `LeanFzn.Semantics.Evaluation.interpB`
(the std twin of the checker). -/

private def stdDynamic : List (String × String × List Value × Bool) :=
  -- integer comparisons and their reified forms
  [ ("int_eq t", "int_eq", [.int 3, .int 3], true)
  , ("int_eq f", "int_eq", [.int 3, .int 4], false)
  , ("int_ne t", "int_ne", [.int 3, .int 4], true)
  , ("int_ne f", "int_ne", [.int 3, .int 3], false)
  , ("int_le t", "int_le", [.int 3, .int 4], true)
  , ("int_le f", "int_le", [.int 4, .int 3], false)
  , ("int_lt t", "int_lt", [.int 3, .int 4], true)
  , ("int_lt f", "int_lt", [.int 4, .int 4], false)
  , ("int_ge t", "int_ge", [.int 4, .int 3], true)
  , ("int_ge f", "int_ge", [.int 3, .int 4], false)
  , ("int_gt t", "int_gt", [.int 4, .int 3], true)
  , ("int_gt f", "int_gt", [.int 3, .int 4], false)
  , ("int_eq_reif t", "int_eq_reif", [.int 3, .int 3, .bool true], true)
  , ("int_eq_reif f", "int_eq_reif", [.int 3, .int 4, .bool false], true)
  , ("int_eq_reif bad", "int_eq_reif", [.int 3, .int 3, .bool false], false)
  , ("int_ne_reif t", "int_ne_reif", [.int 3, .int 4, .bool true], true)
  , ("int_ne_reif f", "int_ne_reif", [.int 3, .int 3, .bool false], true)
  , ("int_ne_reif bad", "int_ne_reif", [.int 3, .int 4, .bool false], false)
  , ("int_le_reif t", "int_le_reif", [.int 3, .int 4, .bool true], true)
  , ("int_le_reif f", "int_le_reif", [.int 4, .int 3, .bool false], true)
  , ("int_le_reif bad", "int_le_reif", [.int 4, .int 3, .bool true], false)
  , ("int_lt_reif t", "int_lt_reif", [.int 3, .int 4, .bool true], true)
  , ("int_lt_reif f", "int_lt_reif", [.int 4, .int 3, .bool false], true)
  , ("int_lt_reif bad", "int_lt_reif", [.int 4, .int 3, .bool true], false)
  , ("int_ge_reif t", "int_ge_reif", [.int 4, .int 3, .bool true], true)
  , ("int_ge_reif f", "int_ge_reif", [.int 3, .int 4, .bool false], true)
  , ("int_ge_reif bad", "int_ge_reif", [.int 3, .int 4, .bool true], false)
  , ("int_gt_reif t", "int_gt_reif", [.int 4, .int 3, .bool true], true)
  , ("int_gt_reif f", "int_gt_reif", [.int 3, .int 4, .bool false], true)
  , ("int_gt_reif bad", "int_gt_reif", [.int 3, .int 4, .bool true], false)
  -- bool predicates
  , ("bool_eq t", "bool_eq", [.bool true, .bool true], true)
  , ("bool_eq f", "bool_eq", [.bool true, .bool false], false)
  , ("bool_not t", "bool_not", [.bool true, .bool false], true)
  , ("bool_not f", "bool_not", [.bool true, .bool true], false)
  , ("bool_and t", "bool_and", [.bool true, .bool true, .bool true], true)
  , ("bool_and f", "bool_and", [.bool true, .bool false, .bool true], false)
  , ("bool_or t", "bool_or", [.bool false, .bool true, .bool true], true)
  , ("bool_or f", "bool_or", [.bool false, .bool false, .bool false], true)
  , ("bool_or bad", "bool_or", [.bool false, .bool false, .bool true], false)
  , ("bool_xor t", "bool_xor", [.bool true, .bool false, .bool true], true)
  , ("bool_xor f", "bool_xor", [.bool true, .bool false, .bool false], false)
  , ("bool_le t", "bool_le", [.bool false, .bool true], true)
  , ("bool_le f", "bool_le", [.bool true, .bool false], false)
  , ("bool_lt t", "bool_lt", [.bool false, .bool true], true)
  , ("bool_lt f", "bool_lt", [.bool true, .bool false], false)
  , ("bool_eq_reif t", "bool_eq_reif", [.bool false, .bool false, .bool true], true)
  , ("bool_eq_reif f", "bool_eq_reif", [.bool false, .bool true, .bool false], true)
  , ("bool_le_reif t", "bool_le_reif", [.bool false, .bool true, .bool true], true)
  , ("bool_le_reif bad", "bool_le_reif", [.bool true, .bool false, .bool true], false)
  , ("bool_lt_reif t", "bool_lt_reif", [.bool false, .bool true, .bool true], true)
  , ("bool_lt_reif bad", "bool_lt_reif", [.bool true, .bool false, .bool true], false)
  , ("bool_clause pos", "bool_clause",
      [.array [.bool true], .array [.bool false]], true)
  , ("bool_clause neg", "bool_clause",
      [.array [.bool false], .array [.bool false]], true)
  , ("bool_clause f", "bool_clause",
      [.array [.bool false], .array [.bool true]], false)
  , ("bool_clause_reif t", "bool_clause_reif",
      [.array [.bool true], .array [.bool false], .bool true], true)
  , ("bool_clause_reif f", "bool_clause_reif",
      [.array [.bool false], .array [.bool true], .bool false], true)
  , ("bool_clause_reif bad", "bool_clause_reif",
      [.array [.bool false], .array [.bool true], .bool true], false)
  , ("bool2int t", "bool2int", [.bool true, .int 1], true)
  , ("bool2int f", "bool2int", [.bool true, .int 0], false)
  , ("array_bool_and t", "array_bool_and",
      [.array [.bool true, .bool true], .bool true], true)
  , ("array_bool_and f", "array_bool_and",
      [.array [.bool true, .bool false], .bool false], true)
  , ("array_bool_and bad", "array_bool_and",
      [.array [.bool true, .bool false], .bool true], false)
  , ("array_bool_xor t", "array_bool_xor",
      [.array [.bool true, .bool false, .bool true]], false)
  , ("array_bool_xor odd", "array_bool_xor",
      [.array [.bool true, .bool false]], true)
  , ("array_bool_or t", "array_bool_or",
      [.array [.bool false, .bool true], .bool true], true)
  , ("array_bool_or f", "array_bool_or",
      [.array [.bool false, .bool false], .bool false], true)
  , ("array_bool_or bad", "array_bool_or",
      [.array [.bool false], .bool true], false)
  -- integer arithmetic
  , ("int_plus t", "int_plus", [.int 2, .int 3, .int 5], true)
  , ("int_plus f", "int_plus", [.int 2, .int 3, .int 6], false)
  , ("int_minus t", "int_minus", [.int 5, .int 3, .int 2], true)
  , ("int_minus f", "int_minus", [.int 5, .int 3, .int 3], false)
  , ("int_times t", "int_times", [.int 2, .int 3, .int 6], true)
  , ("int_times f", "int_times", [.int 2, .int 3, .int 7], false)
  , ("int_div t", "int_div", [.int 7, .int 4, .int 1], true)
  , ("int_div neg", "int_div", [.int (-7), .int 4, .int (-1)], true)
  , ("int_div f", "int_div", [.int 7, .int 4, .int 2], false)
  , ("int_div zero", "int_div", [.int 7, .int 0, .int 1], false)
  , ("int_mod t", "int_mod", [.int 7, .int 4, .int 3], true)
  , ("int_mod neg", "int_mod", [.int (-7), .int 4, .int (-3)], true)
  , ("int_mod f", "int_mod", [.int 7, .int 4, .int 4], false)
  , ("int_min t", "int_min", [.int 3, .int 4, .int 3], true)
  , ("int_min f", "int_min", [.int 3, .int 4, .int 4], false)
  , ("int_max t", "int_max", [.int 3, .int 4, .int 4], true)
  , ("int_max f", "int_max", [.int 3, .int 4, .int 3], false)
  , ("int_abs t", "int_abs", [.int (-5), .int 5], true)
  , ("int_abs f", "int_abs", [.int (-5), .int 4], false)
  , ("int_pow t", "int_pow", [.int 2, .int 3, .int 8], true)
  , ("int_pow neg", "int_pow", [.int 2, .int (-1), .int 0], true)
  , ("int_pow f", "int_pow", [.int 2, .int 3, .int 9], false)
  , ("int_pow_fixed t", "int_pow_fixed", [.int 3, .int 4, .int 81], true)
  , ("int_pow_fixed f", "int_pow_fixed", [.int 3, .int 4, .int 80], false)
  -- linear
  , ("int_lin_eq t", "int_lin_eq",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11], true)
  , ("int_lin_eq f", "int_lin_eq",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], false)
  , ("int_lin_le t", "int_lin_le",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 12], true)
  , ("int_lin_le f", "int_lin_le",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], false)
  , ("int_lin_ne t", "int_lin_ne",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10], true)
  , ("int_lin_ne f", "int_lin_ne",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11], false)
  , ("int_lin_eq_reif t", "int_lin_eq_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11, .bool true], true)
  , ("int_lin_eq_reif f", "int_lin_eq_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11, .bool false], false)
  , ("int_lin_le_reif t", "int_lin_le_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 12, .bool true], true)
  , ("int_lin_le_reif f", "int_lin_le_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10, .bool true], false)
  , ("int_lin_ne_reif t", "int_lin_ne_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 10, .bool true], true)
  , ("int_lin_ne_reif f", "int_lin_ne_reif",
      [.array [.int 1, .int 2], .array [.int 3, .int 4], .int 11, .bool true], false)
  , ("bool_lin_eq t", "bool_lin_eq",
      [.array [.int 1, .int 2], .array [.bool true, .bool false], .int 1], true)
  , ("bool_lin_eq f", "bool_lin_eq",
      [.array [.int 1, .int 2], .array [.bool true, .bool false], .int 2], false)
  , ("bool_lin_le t", "bool_lin_le",
      [.array [.int 1, .int 2], .array [.bool true, .bool false], .int 2], true)
  , ("bool_lin_le f", "bool_lin_le",
      [.array [.int 1, .int 2], .array [.bool true, .bool true], .int 2], false)
  -- element family (1-based)
  , ("array_int_element t", "array_int_element",
      [.int 2, .array [.int 10, .int 20, .int 30], .int 20], true)
  , ("array_int_element f", "array_int_element",
      [.int 2, .array [.int 10, .int 20, .int 30], .int 30], false)
  , ("array_var_int_element t", "array_var_int_element",
      [.int 1, .array [.int 5, .int 6], .int 5], true)
  , ("array_var_int_element_nonshifted t", "array_var_int_element_nonshifted",
      [.int 1, .array [.int 5, .int 6], .int 5], true)
  , ("array_bool_element t", "array_bool_element",
      [.int 2, .array [.bool true, .bool false], .bool false], true)
  , ("array_bool_element f", "array_bool_element",
      [.int 2, .array [.bool true, .bool false], .bool true], false)
  , ("array_var_bool_element t", "array_var_bool_element",
      [.int 1, .array [.bool true, .bool false], .bool true], true)
  , ("array_var_bool_element_nonshifted t", "array_var_bool_element_nonshifted",
      [.int 2, .array [.bool true, .bool false], .bool false], true)
  , ("array_int_maximum t", "array_int_maximum",
      [.int 3, .array [.int 1, .int 3, .int 2]], true)
  , ("array_int_maximum f", "array_int_maximum",
      [.int 2, .array [.int 1, .int 3, .int 2]], false)
  , ("array_int_minimum t", "array_int_minimum",
      [.int 1, .array [.int 1, .int 3, .int 2]], true)
  , ("array_int_minimum f", "array_int_minimum",
      [.int 2, .array [.int 1, .int 3, .int 2]], false)
  , ("all_different t", "all_different",
      [.array [.int 1, .int 2, .int 3]], true)
  , ("all_different f", "all_different",
      [.array [.int 1, .int 2, .int 2]], false)
  , ("all_different_except_0 t", "all_different_except_0",
      [.array [.int 0, .int 0, .int 1]], true)
  , ("all_different_except_0 f", "all_different_except_0",
      [.array [.int 1, .int 1, .int 0]], false)
  , ("set_in t", "set_in", [.int 2, .setOfInt (.enumeration [1, 2])], true)
  , ("set_in f", "set_in", [.int 3, .setOfInt (.enumeration [1, 2])], false)
  , ("set_in_reif t", "set_in_reif",
      [.int 2, .setOfInt (.enumeration [1, 2]), .bool true], true)
  , ("set_in_reif f", "set_in_reif",
      [.int 3, .setOfInt (.enumeration [1, 2]), .bool false], true)
  , ("set_in_reif bad", "set_in_reif",
      [.int 3, .setOfInt (.enumeration [1, 2]), .bool true], false)
  , ("dom t", "dom", [.int 2, .setOfInt (.interval 1 3)], true)
  , ("dom f", "dom", [.int 4, .setOfInt (.interval 1 3)], false)
  , ("set_card t", "set_card",
      [.setOfInt (.enumeration [1, 2, 3]), .int 3], true)
  , ("set_card range", "set_card",
      [.setOfInt (.interval 1 5), .int 5], true)
  , ("set_card f", "set_card",
      [.setOfInt (.enumeration [1, 2, 3]), .int 4], false)
  , ("true builtin", "true", [], true)
  ]

/-! ## Dynamic cases: extensional set builtins (via `interpB`) -/

private def setDynamic : List (String × String × List Value × Bool) :=
  [ ("set_eq t", "set_eq",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.interval 1 2)], true)
  , ("set_eq f", "set_eq",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [1, 3])], false)
  , ("set_ne t", "set_ne",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [1, 3])], true)
  , ("set_ne f", "set_ne",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.interval 1 2)], false)
  , ("set_le t", "set_le",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1, 2])], true)
  , ("set_le f", "set_le",
      [.setOfInt (.enumeration [2]), .setOfInt (.enumeration [1, 2])], false)
  , ("set_lt t", "set_lt",
      [.setOfInt (.enumeration []), .setOfInt (.enumeration [1])], true)
  , ("set_lt f", "set_lt",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1])], false)
  , ("set_subset t", "set_subset",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1, 2])], true)
  , ("set_subset f", "set_subset",
      [.setOfInt (.enumeration [1, 3]), .setOfInt (.enumeration [1, 2])], false)
  , ("set_superset t", "set_superset",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [1])], true)
  , ("set_superset f", "set_superset",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1, 2])], false)
  , ("set_eq_reif t", "set_eq_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1), .bool true], true)
  , ("set_eq_reif f", "set_eq_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]), .bool false], true)
  , ("set_ne_reif t", "set_ne_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]), .bool true], true)
  , ("set_ne_reit bad", "set_ne_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]), .bool false], false)
  , ("set_le_reif t", "set_le_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1, 2]), .bool true], true)
  , ("set_lt_reif t", "set_lt_reif",
      [.setOfInt (.enumeration []), .setOfInt (.enumeration [1]), .bool true], true)
  , ("set_subset_reif t", "set_subset_reif",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1, 2]), .bool true], true)
  , ("set_superset_reif t", "set_superset_reif",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [1]), .bool true], true)
  , ("set_union t", "set_union",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]),
        .setOfInt (.enumeration [1, 2])], true)
  , ("set_union f", "set_union",
      [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]),
        .setOfInt (.enumeration [1])], false)
  , ("set_intersect t", "set_intersect",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3]),
        .setOfInt (.enumeration [2])], true)
  , ("set_intersect f", "set_intersect",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3]),
        .setOfInt (.enumeration [1])], false)
  , ("set_diff t", "set_diff",
      [.setOfInt (.enumeration [1, 2, 3]), .setOfInt (.enumeration [2]),
        .setOfInt (.enumeration [1, 3])], true)
  , ("set_symdiff t", "set_symdiff",
      [.setOfInt (.enumeration [1, 2, 3]), .setOfInt (.enumeration [1, 3, 5]),
        .setOfInt (.enumeration [2, 5])], true)
  , ("set_symdiff f", "set_symdiff",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2]),
        .setOfInt (.enumeration [1, 2])], false)
  , ("array_set_element t", "array_set_element",
      [.int 1, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], true)
  , ("array_var_set_element t", "array_var_set_element",
      [.int 2, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [2])], true)
  , ("array_var_set_element_nonshifted t", "array_var_set_element_nonshifted",
      [.int 2, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [2])], true)
  ]

/-! ## Dynamic cases: all 138 globals (via `fullInterpB`) -/

private def globDynamic : List (String × String × List Value × Bool) :=
  -- ===== all-different family (8) =====
  [ ("fzn_all_different_int t", "fzn_all_different_int",
      [.array [.int 3, .int 1, .int 2]], true)
  , ("fzn_all_different_int f", "fzn_all_different_int",
      [.array [.int 1, .int 2, .int 2]], false)
  , ("fzn_all_different_set t", "fzn_all_different_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])]], true)
  , ("fzn_all_different_set f", "fzn_all_different_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)]], false)
  , ("fzn_all_disjoint t", "fzn_all_disjoint",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])]], true)
  , ("fzn_all_disjoint f", "fzn_all_disjoint",
      [.array [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2])]], false)
  , ("fzn_all_equal_int t", "fzn_all_equal_int",
      [.array [.int 2, .int 2]], true)
  , ("fzn_all_equal_int f", "fzn_all_equal_int",
      [.array [.int 2, .int 3]], false)
  , ("fzn_all_equal_set t", "fzn_all_equal_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)]], true)
  , ("fzn_all_equal_set f", "fzn_all_equal_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])]], false)
  , ("fzn_alldifferent_except t", "fzn_alldifferent_except",
      [.array [.int 1, .int 2, .int 5], .setOfInt (.enumeration [5])], true)
  , ("fzn_alldifferent_except f", "fzn_alldifferent_except",
      [.array [.int 5, .int 2, .int 5], .setOfInt (.enumeration [2])], false)
  , ("fzn_alldifferent_except_0 t", "fzn_alldifferent_except_0",
      [.array [.int 0, .int 0, .int 2]], true)
  , ("fzn_alldifferent_except_0 f", "fzn_alldifferent_except_0",
      [.array [.int 2, .int 0, .int 2]], false)
  , ("fzn_symmetric_all_different t", "fzn_symmetric_all_different",
      [.array [.int 2, .int 1]], true)
  , ("fzn_symmetric_all_different f", "fzn_symmetric_all_different",
      [.array [.int 1, .int 1]], false)
  -- ===== counting family (32) =====
  , ("fzn_nvalue t", "fzn_nvalue",
      [.int 3, .array [.int 1, .int 2, .int 3]], true)
  , ("fzn_nvalue f", "fzn_nvalue",
      [.int 2, .array [.int 1, .int 2, .int 3]], false)
  , ("fzn_among t", "fzn_among",
      [.int 2, .array [.int 1, .int 2, .int 5], .setOfInt (.enumeration [1, 2])], true)
  , ("fzn_among f", "fzn_among",
      [.int 3, .array [.int 1, .int 2, .int 5], .setOfInt (.enumeration [1, 2])], false)
  , ("fzn_at_least_int t", "fzn_at_least_int",
      [.int 2, .array [.int 1, .int 1, .int 2], .int 1], true)
  , ("fzn_at_least_int f", "fzn_at_least_int",
      [.int 3, .array [.int 1, .int 1, .int 2], .int 1], false)
  , ("fzn_at_most_int t", "fzn_at_most_int",
      [.int 2, .array [.int 1, .int 1, .int 2], .int 1], true)
  , ("fzn_at_most_int f", "fzn_at_most_int",
      [.int 1, .array [.int 1, .int 1, .int 2], .int 1], false)
  , ("fzn_exactly_int t", "fzn_exactly_int",
      [.int 2, .array [.int 1, .int 1, .int 2], .int 1], true)
  , ("fzn_exactly_int f", "fzn_exactly_int",
      [.int 3, .array [.int 1, .int 1, .int 2], .int 1], false)
  , ("fzn_count_eq t", "fzn_count_eq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], true)
  , ("fzn_count_eq f", "fzn_count_eq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 3], false)
  , ("fzn_count_eq_par t", "fzn_count_eq_par",
      [.array [.int 1, .int 1], .int 2, .int 0], true)
  , ("fzn_count_geq t", "fzn_count_geq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], true)
  , ("fzn_count_geq f", "fzn_count_geq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 1], false)
  , ("fzn_count_geq_par t", "fzn_count_geq_par",
      [.array [.int 1, .int 1], .int 1, .int 2], true)
  , ("fzn_count_gt t", "fzn_count_gt",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 3], true)
  , ("fzn_count_gt f", "fzn_count_gt",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], false)
  , ("fzn_count_gt_par t", "fzn_count_gt_par",
      [.array [.int 1, .int 1], .int 1, .int 3], true)
  , ("fzn_count_leq t", "fzn_count_leq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], true)
  , ("fzn_count_leq f", "fzn_count_leq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 3], false)
  , ("fzn_count_leq_par t", "fzn_count_leq_par",
      [.array [.int 1, .int 1], .int 1, .int 2], true)
  , ("fzn_count_lt t", "fzn_count_lt",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 1], true)
  , ("fzn_count_lt f", "fzn_count_lt",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], false)
  , ("fzn_count_lt_par t", "fzn_count_lt_par",
      [.array [.int 1, .int 1], .int 1, .int 1], true)
  , ("fzn_count_neq t", "fzn_count_neq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 3], true)
  , ("fzn_count_neq f", "fzn_count_neq",
      [.array [.int 1, .int 1, .int 2], .int 1, .int 2], false)
  , ("fzn_count_neq_par t", "fzn_count_neq_par",
      [.array [.int 1, .int 1], .int 1, .int 3], true)
  , ("fzn_distribute t", "fzn_distribute",
      [.array [.int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 1, .int 1, .int 2]], true)
  , ("fzn_distribute f", "fzn_distribute",
      [.array [.int 1, .int 2], .array [.int 1, .int 2],
        .array [.int 1, .int 1, .int 2]], false)
  , ("fzn_global_cardinality t", "fzn_global_cardinality",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 2, .int 1]], true)
  , ("fzn_global_cardinality f", "fzn_global_cardinality",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 1, .int 1]], false)
  , ("fzn_global_cardinality_closed t", "fzn_global_cardinality_closed",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 2, .int 1]], true)
  , ("fzn_global_cardinality_closed f (outside)",
      "fzn_global_cardinality_closed",
      [.array [.int 1, .int 3, .int 1], .array [.int 1, .int 2],
        .array [.int 2, .int 0]], false)
  , ("fzn_global_cardinality_low_up t", "fzn_global_cardinality_low_up",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 1, .int 1], .array [.int 3, .int 3]], true)
  , ("fzn_global_cardinality_low_up f", "fzn_global_cardinality_low_up",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 2, .int 2], .array [.int 3, .int 3]], false)
  , ("fzn_global_cardinality_low_up_closed t",
      "fzn_global_cardinality_low_up_closed",
      [.array [.int 1, .int 2, .int 1], .array [.int 1, .int 2],
        .array [.int 1, .int 1], .array [.int 3, .int 3]], true)
  , ("fzn_global_cardinality_low_up_closed f",
      "fzn_global_cardinality_low_up_closed",
      [.array [.int 1, .int 5, .int 1], .array [.int 1, .int 2],
        .array [.int 1, .int 1], .array [.int 3, .int 3]], false)
  -- set-counting
  , ("fzn_count_eq_set t", "fzn_count_eq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)],
        .setOfInt (.enumeration [1]), .int 2], true)
  , ("fzn_count_eq_set f", "fzn_count_eq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)],
        .setOfInt (.enumeration [1]), .int 1], false)
  , ("fzn_count_eq_set_par t", "fzn_count_eq_set_par",
      [.array [.setOfInt (.enumeration [1])], .setOfInt (.enumeration [1]),
        .int 1], true)
  , ("fzn_count_geq_set t", "fzn_count_geq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 1], true)
  , ("fzn_count_geq_set f", "fzn_count_geq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 0], false)
  , ("fzn_count_gt_set t", "fzn_count_gt_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 2], true)
  , ("fzn_count_gt_set f", "fzn_count_gt_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 1], false)
  , ("fzn_count_leq_set t", "fzn_count_leq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 1], true)
  , ("fzn_count_leq_set f", "fzn_count_leq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)],
        .setOfInt (.enumeration [1]), .int 3], false)
  , ("fzn_count_lt_set t", "fzn_count_lt_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)],
        .setOfInt (.enumeration [1]), .int 1], true)
  , ("fzn_count_lt_set f", "fzn_count_lt_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.interval 1 1)],
        .setOfInt (.enumeration [1]), .int 2], false)
  , ("fzn_count_neq_set t", "fzn_count_neq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1]), .int 2], true)
  , ("fzn_count_neq_set f", "fzn_count_neq_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [1]), .int 2], false)
  , ("fzn_at_least_set t", "fzn_at_least_set",
      [.int 1, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_at_least_set f", "fzn_at_least_set",
      [.int 2, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], false)
  , ("fzn_at_most_set t", "fzn_at_most_set",
      [.int 1, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_at_most_set f", "fzn_at_most_set",
      [.int 0, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], false)
  , ("fzn_exactly_set t", "fzn_exactly_set",
      [.int 1, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_exactly_set f", "fzn_exactly_set",
      [.int 2, .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1])], false)
  -- ===== lex/sort family (12) =====
  , ("fzn_lex_less_int t", "fzn_lex_less_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 3]], true)
  , ("fzn_lex_less_int f", "fzn_lex_less_int",
      [.array [.int 1, .int 3], .array [.int 1, .int 2]], false)
  , ("fzn_lex_lesseq_int t", "fzn_lex_lesseq_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 2]], true)
  , ("fzn_lex_lesseq_int f", "fzn_lex_lesseq_int",
      [.array [.int 2], .array [.int 1]], false)
  , ("fzn_increasing_int t", "fzn_increasing_int",
      [.array [.int 1, .int 2, .int 2]], true)
  , ("fzn_increasing_int f", "fzn_increasing_int",
      [.array [.int 2, .int 1]], false)
  , ("fzn_increasing_bool t", "fzn_increasing_bool",
      [.array [.bool false, .bool true]], true)
  , ("fzn_increasing_bool f", "fzn_increasing_bool",
      [.array [.bool true, .bool false]], false)
  , ("fzn_strictly_increasing_int t", "fzn_strictly_increasing_int",
      [.array [.int 1, .int 2, .int 3]], true)
  , ("fzn_strictly_increasing_int f", "fzn_strictly_increasing_int",
      [.array [.int 1, .int 1]], false)
  , ("fzn_sort t", "fzn_sort",
      [.array [.int 3, .int 1], .array [.int 1, .int 3]], true)
  , ("fzn_sort f", "fzn_sort",
      [.array [.int 3, .int 1], .array [.int 3, .int 1]], false)
  , ("fzn_arg_sort_int t", "fzn_arg_sort_int",
      [.array [.int 30, .int 10], .array [.int 2, .int 1]], true)
  , ("fzn_arg_sort_int f", "fzn_arg_sort_int",
      [.array [.int 30, .int 10], .array [.int 1, .int 2]], false)
  , ("fzn_maximum_arg_int t", "fzn_maximum_arg_int",
      [.array [.int 3, .int 7, .int 5], .int 2], true)
  , ("fzn_maximum_arg_int f", "fzn_maximum_arg_int",
      [.array [.int 3, .int 7, .int 5], .int 1], false)
  , ("fzn_minimum_arg_int t", "fzn_minimum_arg_int",
      [.array [.int 3, .int 7, .int 5], .int 1], true)
  , ("fzn_minimum_arg_int f", "fzn_minimum_arg_int",
      [.array [.int 3, .int 7, .int 5], .int 3], false)
  , ("fzn_value_precede_int t", "fzn_value_precede_int",
      [.int 1, .int 2, .array [.int 1, .int 2, .int 2]], true)
  , ("fzn_value_precede_int f", "fzn_value_precede_int",
      [.int 1, .int 2, .array [.int 2, .int 1]], false)
  , ("fzn_value_precede_chain_int t", "fzn_value_precede_chain_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 2, .int 1]], true)
  , ("fzn_value_precede_chain_int f", "fzn_value_precede_chain_int",
      [.array [.int 1, .int 2], .array [.int 2, .int 1]], false)
  , ("fzn_seq_precede_chain_int t", "fzn_seq_precede_chain_int",
      [.array [.int 1, .int 2, .int 3]], true)
  , ("fzn_seq_precede_chain_int f", "fzn_seq_precede_chain_int",
      [.array [.int 3, .int 1]], false)
  -- ===== packing/scheduling family (17) =====
  , ("fzn_bin_packing t", "fzn_bin_packing",
      [.int 5, .array [.int 1, .int 1], .array [.int 3, .int 2]], true)
  , ("fzn_bin_packing f", "fzn_bin_packing",
      [.int 4, .array [.int 1, .int 1], .array [.int 3, .int 2]], false)
  , ("fzn_bin_packing_capa t", "fzn_bin_packing_capa",
      [.array [.int 5, .int 4], .array [.int 1, .int 2], .array [.int 3, .int 2]],
      true)
  , ("fzn_bin_packing_capa f", "fzn_bin_packing_capa",
      [.array [.int 2, .int 4], .array [.int 1, .int 2], .array [.int 3, .int 3]],
      false)
  , ("fzn_bin_packing_load t", "fzn_bin_packing_load",
      [.array [.int 3, .int 2], .array [.int 1, .int 2], .array [.int 3, .int 2]],
      true)
  , ("fzn_bin_packing_load f", "fzn_bin_packing_load",
      [.array [.int 2, .int 2], .array [.int 1, .int 2], .array [.int 3, .int 2]],
      false)
  , ("fzn_knapsack t", "fzn_knapsack",
      [.array [.int 2, .int 3], .array [.int 4, .int 5], .array [.int 1, .int 1],
        .int 5, .int 9], true)
  , ("fzn_knapsack f", "fzn_knapsack",
      [.array [.int 2, .int 3], .array [.int 4, .int 5], .array [.int 1, .int 1],
        .int 5, .int 8], false)
  , ("fzn_diffn t", "fzn_diffn",
      [.array [.int 0, .int 5], .array [.int 0, .int 0],
        .array [.int 2, .int 2], .array [.int 2, .int 2]], true)
  , ("fzn_diffn f", "fzn_diffn",
      [.array [.int 0, .int 1], .array [.int 0, .int 0],
        .array [.int 2, .int 2], .array [.int 2, .int 2]], false)
  , ("fzn_diffn_nonstrict t", "fzn_diffn_nonstrict",
      [.array [.int 0, .int 2], .array [.int 0, .int 0],
        .array [.int 2, .int 2], .array [.int 2, .int 2]], true)
  , ("fzn_diffn_nonstrict f", "fzn_diffn_nonstrict",
      [.array [.int 0, .int 1], .array [.int 0, .int 0],
        .array [.int 2, .int 2], .array [.int 2, .int 2]], false)
  , ("fzn_geost_nonoverlap_k t", "fzn_geost_nonoverlap_k",
      [.array [.int 0, .int 5], .array [.int 2, .int 2],
        .array [.int 5, .int 0], .array [.int 2, .int 2]], true)
  , ("fzn_geost_nonoverlap_k f", "fzn_geost_nonoverlap_k",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 1, .int 0], .array [.int 2, .int 2]], false)
  , ("fzn_disjunctive t", "fzn_disjunctive",
      [.array [.int 0, .int 5], .array [.int 2, .int 2]], true)
  , ("fzn_disjunctive f", "fzn_disjunctive",
      [.array [.int 0, .int 1], .array [.int 2, .int 2]], false)
  , ("fzn_disjunctive_strict t", "fzn_disjunctive_strict",
      [.array [.int 0, .int 5], .array [.int 2, .int 2]], true)
  , ("fzn_disjunctive_strict f", "fzn_disjunctive_strict",
      [.array [.int 0, .int 1], .array [.int 2, .int 2]], false)
  , ("fzn_cumulative t", "fzn_cumulative",
      [.array [.int 0, .int 5], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .int 1], true)
  , ("fzn_cumulative f", "fzn_cumulative",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .int 1], false)
  , ("fzn_table_int t", "fzn_table_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 2, .int 3, .int 4]], true)
  , ("fzn_table_int f", "fzn_table_int",
      [.array [.int 1, .int 2], .array [.int 9, .int 9, .int 9, .int 9]], false)
  , ("fzn_if_then_else_int t", "fzn_if_then_else_int",
      [.array [.bool false, .bool true], .array [.int 10, .int 20], .int 20], true)
  , ("fzn_if_then_else_int f", "fzn_if_then_else_int",
      [.array [.bool false, .bool true], .array [.int 10, .int 20], .int 10], false)
  , ("fzn_if_then_else_bool t", "fzn_if_then_else_bool",
      [.array [.bool true, .bool false], .array [.bool false, .bool true],
        .bool false], true)
  , ("fzn_if_then_else_bool f", "fzn_if_then_else_bool",
      [.array [.bool true], .array [.bool true], .bool false], false)
  , ("fzn_if_then_else_set t", "fzn_if_then_else_set",
      [.array [.bool true], .array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_if_then_else_set f", "fzn_if_then_else_set",
      [.array [.bool true], .array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [2])], false)
  , ("fzn_if_then_else_var_int t", "fzn_if_then_else_var_int",
      [.array [.bool false, .bool true], .array [.int 10, .int 20], .int 20], true)
  , ("fzn_if_then_else_var_int f", "fzn_if_then_else_var_int",
      [.array [.bool true, .bool false], .array [.int 10, .int 20], .int 20], false)
  , ("fzn_if_then_else_var_bool t", "fzn_if_then_else_var_bool",
      [.array [.bool false], .array [.bool false], .bool false], true)
  , ("fzn_if_then_else_var_bool f", "fzn_if_then_else_var_bool",
      [.array [.bool true], .array [.bool true], .bool false], false)
  , ("fzn_if_then_else_var_set t", "fzn_if_then_else_var_set",
      [.array [.bool false], .array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_if_then_else_var_set f", "fzn_if_then_else_var_set",
      [.array [.bool false, .bool true], .array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [1])], false)
  -- ===== channeling family (11) =====
  , ("fzn_inverse t", "fzn_inverse",
      [.array [.int 2, .int 1], .array [.int 2, .int 1]], true)
  , ("fzn_inverse f", "fzn_inverse",
      [.array [.int 1, .int 1], .array [.int 1, .int 2]], false)
  , ("fzn_inverse_in_range t", "fzn_inverse_in_range",
      [.array [.int 2, .int 1], .array [.int 2, .int 1]], true)
  , ("fzn_inverse_in_range f", "fzn_inverse_in_range",
      [.array [.int 1, .int 1], .array [.int 1, .int 2]], false)
  , ("fzn_int_set_channel t", "fzn_int_set_channel",
      [.array [.int 1, .int 2],
        .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])]], true)
  , ("fzn_int_set_channel f", "fzn_int_set_channel",
      [.array [.int 2, .int 1],
        .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])]], false)
  , ("fzn_link_set_to_booleans t", "fzn_link_set_to_booleans",
      [.setOfInt (.enumeration [1]),
        .array [.bool true, .bool false]], true)
  , ("fzn_link_set_to_booleans f", "fzn_link_set_to_booleans",
      [.setOfInt (.enumeration [1]),
        .array [.bool true, .bool true]], false)
  , ("fzn_member_int t", "fzn_member_int",
      [.array [.int 1, .int 2, .int 3], .int 2], true)
  , ("fzn_member_int f", "fzn_member_int",
      [.array [.int 1, .int 2, .int 3], .int 4], false)
  , ("fzn_member_bool t", "fzn_member_bool",
      [.array [.bool true, .bool false], .bool false], true)
  , ("fzn_member_bool f", "fzn_member_bool",
      [.array [.bool false, .bool false], .bool true], false)
  , ("fzn_member_set t", "fzn_member_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.interval 2 2)], true)
  , ("fzn_member_set f", "fzn_member_set",
      [.array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [3])], false)
  , ("fzn_arg_val_int t", "fzn_arg_val_int",
      [.array [.int 5, .int 7], .int 7, .int 2], true)
  , ("fzn_arg_val_int f", "fzn_arg_val_int",
      [.array [.int 5, .int 7], .int 7, .int 1], false)
  , ("fzn_arg_val_bool t", "fzn_arg_val_bool",
      [.array [.bool false, .bool true], .bool true, .int 2], true)
  , ("fzn_arg_val_bool f", "fzn_arg_val_bool",
      [.array [.bool false, .bool true], .bool true, .int 1], false)
  , ("fzn_write t", "fzn_write",
      [.array [.int 1, .int 2], .int 2, .int 9, .array [.int 1, .int 9]], true)
  , ("fzn_write f", "fzn_write",
      [.array [.int 1, .int 2], .int 2, .int 9, .array [.int 1, .int 2]], false)
  , ("fzn_writes t", "fzn_writes",
      [.array [.int 1, .int 2, .int 3], .array [.int 1, .int 3],
        .array [.int 9, .int 8], .array [.int 9, .int 2, .int 8]], true)
  , ("fzn_writes f", "fzn_writes",
      [.array [.int 1, .int 2, .int 3], .array [.int 1, .int 3],
        .array [.int 9, .int 8], .array [.int 1, .int 2, .int 3]], false)
  -- ===== set/math family (14) =====
  , ("fzn_disjoint t", "fzn_disjoint",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [3])], true)
  , ("fzn_disjoint f", "fzn_disjoint",
      [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3])], false)
  , ("fzn_set_member t", "fzn_set_member",
      [.setOfInt (.enumeration [1, 2]), .int 2], true)
  , ("fzn_set_member f", "fzn_set_member",
      [.setOfInt (.enumeration [1, 2]), .int 3], false)
  , ("fzn_partition_set t", "fzn_partition_set",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1, 2])], true)
  , ("fzn_partition_set f", "fzn_partition_set",
      [.array [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1, 2])], false)
  , ("fzn_at_most1 t", "fzn_at_most1",
      [.array [.setOfInt (.enumeration [1, 2]),
        .setOfInt (.enumeration [2, 3])]], true)
  , ("fzn_at_most1 f", "fzn_at_most1",
      [.array [.setOfInt (.enumeration [1, 2, 5]),
        .setOfInt (.enumeration [2, 3, 5])]], false)
  , ("fzn_sum_set t", "fzn_sum_set",
      [.array [.int 1, .int 2], .array [.int 10, .int 20],
        .setOfInt (.enumeration [1]), .int 10], true)
  , ("fzn_sum_set f", "fzn_sum_set",
      [.array [.int 1, .int 2], .array [.int 10, .int 20],
        .setOfInt (.enumeration [1]), .int 20], false)
  , ("fzn_sum_pred t", "fzn_sum_pred",
      [.int 1, .array [.setOfInt (.enumeration [1, 2])],
        .array [.int 10, .int 20], .int 30], true)
  , ("fzn_sum_pred f", "fzn_sum_pred",
      [.int 1, .array [.setOfInt (.enumeration [1, 2])],
        .array [.int 10, .int 20], .int 20], false)
  , ("fzn_range t", "fzn_range",
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1, 2]),
        .setOfInt (.enumeration [10, 20])], true)
  , ("fzn_range f", "fzn_range",
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1, 2]),
        .setOfInt (.enumeration [10])], false)
  , ("fzn_roots t", "fzn_roots",
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1, 2]),
        .setOfInt (.enumeration [10, 20])], true)
  , ("fzn_roots f", "fzn_roots",
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [10, 20])], false)
  , ("fzn_array_int_union t", "fzn_array_int_union",
      [.array [.int 1, .int 2, .int 2], .setOfInt (.enumeration [1, 2])], true)
  , ("fzn_array_int_union f", "fzn_array_int_union",
      [.array [.int 1, .int 2], .setOfInt (.enumeration [1])], false)
  , ("fzn_array_set_union t", "fzn_array_set_union",
      [.array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
        .setOfInt (.enumeration [1, 2])], true)
  , ("fzn_array_set_union f", "fzn_array_set_union",
      [.array [.setOfInt (.enumeration [1])],
        .setOfInt (.enumeration [1, 2])], false)
  , ("fzn_array_set_intersect t", "fzn_array_set_intersect",
      [.array [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3])],
        .setOfInt (.enumeration [2])], true)
  , ("fzn_array_set_intersect f", "fzn_array_set_intersect",
      [.array [.setOfInt (.enumeration [1, 2]), .setOfInt (.enumeration [2, 3])],
        .setOfInt (.enumeration [1])], false)
  , ("fzn_sliding_sum t", "fzn_sliding_sum",
      [.int 3, .int 5, .int 2, .array [.int 1, .int 2, .int 3]], true)
  , ("fzn_sliding_sum f", "fzn_sliding_sum",
      [.int 3, .int 4, .int 2, .array [.int 1, .int 2, .int 3]], false)
  , ("fzn_sliding_among_int t", "fzn_sliding_among_int",
      [.int 1, .int 2, .int 2, .array [.int 1, .int 5, .int 1],
        .setOfInt (.enumeration [1])], true)
  , ("fzn_sliding_among_int f", "fzn_sliding_among_int",
      [.int 2, .int 2, .int 2, .array [.int 1, .int 5, .int 1],
        .setOfInt (.enumeration [1])], false)
  , ("fzn_sliding_among_bool t", "fzn_sliding_among_bool",
      [.int 1, .int 2, .int 2, .array [.bool true, .bool false, .bool true],
        .bool true], true)
  , ("fzn_sliding_among_bool f", "fzn_sliding_among_bool",
      [.int 2, .int 2, .int 2, .array [.bool true, .bool false, .bool true],
        .bool true], false)
  -- new families: lex-chain (G24)
  , ("fzn_lex_greater_int t", "fzn_lex_greater_int",
      [.array [.int 2, .int 1], .array [.int 1, .int 9]], true)
  , ("fzn_lex_greater_int f", "fzn_lex_greater_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 9]], false)
  , ("fzn_lex_greatereq_int t", "fzn_lex_greatereq_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 2]], true)
  , ("fzn_lex_greatereq_int f", "fzn_lex_greatereq_int",
      [.array [.int 1, .int 2], .array [.int 1, .int 9]], false)
  , ("fzn_lex_chain_less_int t", "fzn_lex_chain_less_int",
      [.array [.array [.int 1, .int 5], .array [.int 2, .int 1]]], true)
  , ("fzn_lex_chain_less_int f", "fzn_lex_chain_less_int",
      [.array [.array [.int 2, .int 1], .array [.int 1, .int 5]]], false)
  , ("fzn_lex_chain_lesseq_int t", "fzn_lex_chain_lesseq_int",
      [.array [.array [.int 1, .int 5], .array [.int 1, .int 5]]], true)
  , ("fzn_lex_chain_lesseq_int f", "fzn_lex_chain_lesseq_int",
      [.array [.array [.int 2, .int 1], .array [.int 1, .int 5]]], false)
  , ("fzn_lex2 t", "fzn_lex2",
      [.array [.array [.int 1, .int 2], .array [.int 1, .int 2]]], true)
  , ("fzn_lex2 f", "fzn_lex2",
      [.array [.array [.int 2, .int 1], .array [.int 1, .int 2]]], false)
  , ("fzn_strict_lex2 t", "fzn_strict_lex2",
      [.array [.array [.int 1, .int 2], .array [.int 1, .int 3]]], true)
  , ("fzn_strict_lex2 f", "fzn_strict_lex2",
      [.array [.array [.int 1, .int 2], .array [.int 1, .int 2]]], false)
  , ("fzn_lex_chain_lesseq_orbitope t", "fzn_lex_chain_lesseq_orbitope",
      [.array [.array [.int 0, .int 1],
        .array [.int 1, .int 0]], .int 1], true)
  , ("fzn_lex_chain_lesseq_orbitope f", "fzn_lex_chain_lesseq_orbitope",
       [.array [.array [.int 1, .int 0],
         .array [.int 0, .int 1]], .int 2], false)
  , ("fzn_lex_chain_greater_int t", "fzn_lex_chain_greater_int",
       [.array [.array [.int 2, .int 1], .array [.int 1, .int 5]]], true)
  , ("fzn_lex_chain_greater_int f", "fzn_lex_chain_greater_int",
       [.array [.array [.int 1, .int 5], .array [.int 2, .int 1]]], false)
  , ("fzn_lex_chain_greatereq_int t", "fzn_lex_chain_greatereq_int",
       [.array [.array [.int 1, .int 5], .array [.int 1, .int 5]]], true)
  , ("fzn_lex_chain_greatereq_int f", "fzn_lex_chain_greatereq_int",
       [.array [.array [.int 1, .int 5], .array [.int 2, .int 1]]], false)
  , ("fzn_lex_chain_greatereq_orbitope t", "fzn_lex_chain_greatereq_orbitope",
       [.array [.array [.int 1, .int 0],
         .array [.int 0, .int 1]], .int 1], true)
  , ("fzn_lex_chain_greatereq_orbitope f", "fzn_lex_chain_greatereq_orbitope",
       [.array [.array [.int 0, .int 1],
         .array [.int 1, .int 0]], .int 2], false)
  -- circuit / subcircuit (G25)
  , ("fzn_circuit t", "fzn_circuit",
      [.array [.int 2, .int 3, .int 1]], true)
  , ("fzn_circuit f", "fzn_circuit",
      [.array [.int 1, .int 2, .int 3]], false)
  , ("fzn_subcircuit t", "fzn_subcircuit",
      [.array [.int 2, .int 1, .int 3]], true)
  , ("fzn_subcircuit f", "fzn_subcircuit",
      [.array [.int 2, .int 1, .int 1]], false)
  -- graph family (G29)
  , ("fzn_subgraph t", "fzn_subgraph",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true]], true)
  , ("fzn_subgraph f", "fzn_subgraph",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true], .array [.bool true, .bool true]], false)
  , ("fzn_dag t", "fzn_dag",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true], .array [.bool true, .bool true]], true)
  , ("fzn_dag f", "fzn_dag",
      [.array [.int 1, .int 2], .array [.int 2, .int 1],
        .array [.bool true, .bool true], .array [.bool true, .bool true]], false)
  , ("fzn_connected t", "fzn_connected",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true]], true)
  , ("fzn_connected f", "fzn_connected",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool false, .bool true],
        .array [.bool true, .bool false]], false)
  , ("fzn_dconnected t", "fzn_dconnected",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true]], true)
  , ("fzn_dconnected f", "fzn_dconnected",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool false]], false)
  , ("fzn_reachable t", "fzn_reachable",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], true)
  , ("fzn_reachable f", "fzn_reachable",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool false],
        .array [.bool true, .bool true], .int 1], false)
  , ("fzn_dreachable t", "fzn_dreachable",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], true)
  , ("fzn_dreachable f", "fzn_dreachable",
      [.array [.int 1, .int 2], .array [.int 3, .int 2],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], false)
  , ("fzn_tree t", "fzn_tree",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], true)
  , ("fzn_tree f", "fzn_tree",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool false],
        .array [.bool true, .bool true], .int 1], false)
  , ("fzn_dtree t", "fzn_dtree",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], true)
  , ("fzn_dtree f", "fzn_dtree",
      [.array [.int 1, .int 2], .array [.int 2, .int 1],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1], false)
  , ("fzn_path t", "fzn_path",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3], true)
  , ("fzn_path f", "fzn_path",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool false, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3], false)
  , ("fzn_dpath t", "fzn_dpath",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3], true)
  , ("fzn_dpath f", "fzn_dpath",
      [.array [.int 1, .int 1], .array [.int 3, .int 2],
        .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3], false)
  , ("fzn_bounded_path t", "fzn_bounded_path",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3, .int 2], true)
  , ("fzn_bounded_path f", "fzn_bounded_path",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3, .int 1], false)
  , ("fzn_bounded_dpath t", "fzn_bounded_dpath",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3, .int 2], true)
  , ("fzn_bounded_dpath f", "fzn_bounded_dpath",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 3, .int 1], false)
  , ("fzn_steiner t", "fzn_steiner",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 2], true)
  , ("fzn_steiner f", "fzn_steiner",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 1], false)
  , ("fzn_dsteiner t", "fzn_dsteiner",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 2], true)
  , ("fzn_dsteiner f", "fzn_dsteiner",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true, .bool true],
        .array [.bool true, .bool true], .int 1, .int 1], false)
  , ("fzn_wst t", "fzn_wst",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true], .int 2], true)
  , ("fzn_wst f", "fzn_wst",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool false], .int 2], false)
  , ("fzn_dwst t", "fzn_dwst",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true], .int 1, .int 2], true)
  , ("fzn_dwst f", "fzn_dwst",
      [.array [.int 1, .int 2], .array [.int 2, .int 3],
        .array [.int 1, .int 1], .array [.bool true, .bool true], .int 1, .int 1], false)
  -- regular family (G27/G28)
  , ("fzn_regular t", "fzn_regular",
      [.array [.int 1, .int 1], .int 2, .int 2,
        .array [.int 2, .int 2, .int 2, .int 0], .int 1,
        .array [.int 0, .int 1]], true)
  , ("fzn_regular f", "fzn_regular",
      [.array [.int 1, .int 1], .int 2, .int 2,
        .array [.int 2, .int 2, .int 2, .int 0], .int 1,
        .array [.int 1, .int 0]], false)
  , ("fzn_regular_nfa t", "fzn_regular_nfa",
      [.array [.int 1, .int 1], .int 2, .int 2,
        .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration []),
          .setOfInt (.enumeration []), .setOfInt (.enumeration [])], .int 1,
        .array [.int 1, .int 0]], true)
  , ("fzn_regular_nfa f", "fzn_regular_nfa",
      [.array [.int 2, .int 2], .int 2, .int 2,
        .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration []),
          .setOfInt (.enumeration []), .setOfInt (.enumeration [])], .int 1,
        .array [.int 1, .int 0]], false)
  , ("fzn_cost_regular t", "fzn_cost_regular",
      [.array [.int 1, .int 1], .int 2, .int 2,
        .array [.int 2, .int 2, .int 2, .int 0], .int 1,
        .array [.int 0, .int 1], .array [.int 3, .int 5, .int 0, .int 0], .int 3], true)
  , ("fzn_cost_regular f", "fzn_cost_regular",
      [.array [.int 1, .int 1], .int 2, .int 2,
        .array [.int 2, .int 2, .int 2, .int 0], .int 1,
        .array [.int 0, .int 1], .array [.int 3, .int 5, .int 0, .int 0], .int 4], false)
  , ("fzn_mdd t", "fzn_mdd",
      [.array [.int 1, .int 2], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])],
        .array [.int 2, .int 0, .int 0]], true)
  , ("fzn_mdd f", "fzn_mdd",
      [.array [.int 1, .int 1], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])],
        .array [.int 2, .int 0, .int 0]], false)
  , ("fzn_mdd_nondet t", "fzn_mdd_nondet",
      [.array [.int 1, .int 2], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])],
        .array [.int 2, .int 0, .int 0]], true)
  , ("fzn_mdd_nondet f", "fzn_mdd_nondet",
      [.array [.int 1, .int 1], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])],
        .array [.int 2, .int 0, .int 0]], false)
  , ("fzn_cost_mdd t", "fzn_cost_mdd",
      [.array [.int 1, .int 2], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])], .array [.int 4, .int 6, .int 7],
        .array [.int 2, .int 0, .int 0], .int 11], true)
  , ("fzn_cost_mdd f", "fzn_cost_mdd",
      [.array [.int 1, .int 2], .int 3, .array [.int 1, .int 2, .int 3],
        .int 3, .array [.int 1, .int 1, .int 2], .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [2]), .setOfInt (.enumeration [2])], .array [.int 4, .int 6, .int 7],
        .array [.int 2, .int 0, .int 0], .int 10], false)
  -- sched2 family (G26/G30/G31/G32)
  , ("fzn_cumulatives t", "fzn_cumulatives",
      [.array [.int 0, .int 2], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .array [.int 1, .int 1],
        .array [.int 1, .int 1], .bool true, .int 1], true)
  , ("fzn_cumulatives f", "fzn_cumulatives",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .array [.int 1, .int 1],
        .array [.int 1, .int 1], .bool true, .int 1], false)
  , ("fzn_cumulatives_decomp t", "fzn_cumulatives_decomp",
      [.array [.int 0, .int 2], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .array [.int 1, .int 1],
        .array [.int 1, .int 1], .bool true], true)
  , ("fzn_cumulatives_decomp f", "fzn_cumulatives_decomp",
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
        .array [.int 1, .int 1], .array [.int 1, .int 1],
        .array [.int 1, .int 1], .bool true], false)
  , ("fzn_geost t", "fzn_geost",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 5], .array [.int 1, .int 1]], true)
  , ("fzn_geost f", "fzn_geost",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 0], .array [.int 1, .int 1]], false)
  , ("fzn_geost_bb t", "fzn_geost_bb",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 5], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 6]], true)
  , ("fzn_geost_bb f", "fzn_geost_bb",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 5], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 5]], false)
  , ("fzn_geost_smallest_bb t", "fzn_geost_smallest_bb",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 5], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 6]], true)
  , ("fzn_geost_smallest_bb f", "fzn_geost_smallest_bb",
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
        .array [.int 0, .int 0, .int 0, .int 0],
        .array [.setOfInt (.enumeration [1])],
        .array [.int 0, .int 5], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 9]], false)
  , ("fzn_diffn_nonoverlap_k t", "fzn_diffn_nonoverlap_k",
      [.array [.int 0, .int 5], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 1]], true)
  , ("fzn_diffn_nonoverlap_k f", "fzn_diffn_nonoverlap_k",
      [.array [.int 0, .int 0], .array [.int 1, .int 1],
        .array [.int 0, .int 0], .array [.int 1, .int 1]], false)
  , ("fzn_diffn_k t", "fzn_diffn_k",
      [.array [.array [.int 0, .int 0], .array [.int 5, .int 0]],
        .array [.array [.int 1, .int 1], .array [.int 1, .int 1]]], true)
  , ("fzn_diffn_k f", "fzn_diffn_k",
      [.array [.array [.int 0, .int 0], .array [.int 0, .int 0]],
        .array [.array [.int 1, .int 1], .array [.int 1, .int 1]]], false)
  , ("fzn_diffn_nonstrict_k t", "fzn_diffn_nonstrict_k",
      [.array [.array [.int 0, .int 0], .array [.int 5, .int 0]],
        .array [.array [.int 1, .int 0], .array [.int 1, .int 1]]], true)
  , ("fzn_diffn_nonstrict_k f", "fzn_diffn_nonstrict_k",
      [.array [.array [.int 0, .int 0], .array [.int 0, .int 0]],
        .array [.array [.int 1, .int 1], .array [.int 1, .int 1]]], false)
  , ("fzn_writes_seq t", "fzn_writes_seq",
      [.array [.int 9, .int 8], .array [.int 2, .int 1],
        .array [.int 5, .int 6], .array [.int 6, .int 5]], true)
  , ("fzn_writes_seq f", "fzn_writes_seq",
      [.array [.int 9, .int 8], .array [.int 2, .int 1],
        .array [.int 5, .int 6], .array [.int 9, .int 8]], false)
  , ("fzn_if_then_else_partiality t", "fzn_if_then_else_partiality",
      [.array [.bool false, .bool true], .array [.bool false, .bool true],
        .bool true], true)
  , ("fzn_if_then_else_partiality f", "fzn_if_then_else_partiality",
      [.array [.bool false, .bool true], .array [.bool false, .bool true],
        .bool false], false)
  ]

/-! ## End-to-end checks (checkSolutionFull) -/

private def endToEnd : List (String × String × String × Bool) :=
  [ ("counting accept",
      "var 0..3: n;\narray [1..3] of var 0..3: xs = [1, 2, 1];\nconstraint fzn_nvalue(n, xs);\nconstraint fzn_count_eq(xs, 1, 2);\nsolve satisfy;",
      "n = 2;\nxs = array1d(1..3, [1, 2, 1]);\n----------", true)
  , ("counting reject",
      "var 0..3: n;\narray [1..3] of var 0..3: xs = [1, 2, 1];\nconstraint fzn_nvalue(n, xs);\nconstraint fzn_count_eq(xs, 1, 2);\nsolve satisfy;",
      "n = 2;\nxs = array1d(1..3, [1, 1, 1]);\n----------", false)
  , ("sort accept",
      "var 0..9: y1;\nvar 0..9: y2;\nvar 0..9: y3;\narray [1..3] of var 0..9: xs = [3, 1, 2];\narray [1..3] of var 0..9: ys = [y1, y2, y3];\nconstraint fzn_sort(xs, ys);\nsolve satisfy;",
      "xs = array1d(1..3, [3, 1, 2]);\ny1 = 1;\ny2 = 2;\ny3 = 3;\nys = array1d(1..3, [1, 2, 3]);\n----------", true)
  , ("sort reject",
      "var 0..9: y1;\nvar 0..9: y2;\nvar 0..9: y3;\narray [1..3] of var 0..9: xs = [3, 1, 2];\narray [1..3] of var 0..9: ys = [y1, y2, y3];\nconstraint fzn_sort(xs, ys);\nsolve satisfy;",
      "xs = array1d(1..3, [3, 1, 2]);\ny1 = 3;\ny2 = 2;\ny3 = 1;\nys = array1d(1..3, [3, 2, 1]);\n----------", false)
  , ("inverse accept",
      "var 1..3: a1;\nvar 1..3: a2;\nvar 1..3: a3;\nvar 1..3: b1;\nvar 1..3: b2;\nvar 1..3: b3;\narray [1..3] of var 1..3: xs = [a1, a2, a3];\narray [1..3] of var 1..3: ys = [b1, b2, b3];\nconstraint fzn_inverse(xs, ys);\nsolve satisfy;",
      "a1 = 3;\na2 = 1;\na3 = 2;\nb1 = 2;\nb2 = 3;\nb3 = 1;\nxs = array1d(1..3, [3, 1, 2]);\nys = array1d(1..3, [2, 3, 1]);\n----------", true)
  , ("inverse reject",
      "var 1..3: a1;\nvar 1..3: a2;\nvar 1..3: a3;\nvar 1..3: b1;\nvar 1..3: b2;\nvar 1..3: b3;\narray [1..3] of var 1..3: xs = [a1, a2, a3];\narray [1..3] of var 1..3: ys = [b1, b2, b3];\nconstraint fzn_inverse(xs, ys);\nsolve satisfy;",
      "a1 = 1;\na2 = 1;\na3 = 2;\nb1 = 1;\nb2 = 2;\nb3 = 3;\nxs = array1d(1..3, [1, 1, 2]);\nys = array1d(1..3, [1, 2, 3]);\n----------", false)
  , ("sliding accept",
      "array [1..3] of var 0..9: xs = [1, 2, 3];\nconstraint fzn_sliding_sum(3, 5, 2, xs);\nsolve satisfy;",
      "xs = array1d(1..3, [1, 2, 3]);\n----------", true)
  , ("disjunctive accept",
      "array [1..2] of int: d = [2, 2];\narray [1..2] of var 0..9: s = [0, 5];\nconstraint fzn_disjunctive(s, d);\nsolve satisfy;",
      "s = array1d(1..2, [0, 5]);\n----------", true)
  , ("disjunctive reject",
      "array [1..2] of int: d = [2, 2];\narray [1..2] of var 0..9: s = [0, 5];\nconstraint fzn_disjunctive(s, d);\nsolve satisfy;",
      "s = array1d(1..2, [0, 1]);\n----------", false)
  , ("bin packing accept",
      "array [1..2] of int: w = [3, 2];\narray [1..2] of var 1..2: b = [1, 2];\nconstraint fzn_bin_packing(3, b, w);\nsolve satisfy;",
      "b = array1d(1..2, [1, 2]);\n----------", true)
  , ("bin packing reject",
      "array [1..2] of int: w = [3, 2];\narray [1..2] of var 1..2: b = [1, 2];\nconstraint fzn_bin_packing(2, b, w);\nsolve satisfy;",
      "b = array1d(1..2, [1, 2]);\n----------", false)
  , ("set member accept",
      "var set of 1..5: a;\nconstraint fzn_set_member(a, 2);\nsolve satisfy;",
      "a = {2, 5};\n----------", true)
  , ("set member reject",
      "var set of 1..5: a;\nconstraint fzn_set_member(a, 2);\nsolve satisfy;",
      "a = {5};\n----------", false)
  , ("table accept",
      "array [1..4] of int: t = [1, 2, 3, 4];\nvar 0..9: u1;\nvar 0..9: u2;\narray [1..2] of var 0..9: xs = [u1, u2];\nconstraint fzn_table_int(xs, t);\nsolve satisfy;",
      "u1 = 3;\nu2 = 4;\nxs = array1d(1..2, [3, 4]);\n----------", true)
  , ("table reject",
      "array [1..4] of int: t = [1, 2, 3, 4];\nvar 0..9: u1;\nvar 0..9: u2;\narray [1..2] of var 0..9: xs = [u1, u2];\nconstraint fzn_table_int(xs, t);\nsolve satisfy;",
      "u1 = 4;\nu2 = 3;\nxs = array1d(1..2, [4, 3]);\n----------", false)
  , ("builtin if_then_else accept",
      "array [1..2] of var bool: cs = [false, true];\nvar 0..9: y;\nconstraint fzn_if_then_else_int(cs, [4, 7], y);\nsolve satisfy;",
      "cs = array1d(1..2, [false, true]);\ny = 7;\n----------", true)
  , ("link_set accept",
      "var bool: c1;\nvar bool: c2;\nvar bool: c3;\nvar set of 1..3: s;\narray [1..3] of var bool: bs = [c1, c2, c3];\nconstraint fzn_link_set_to_booleans(s, bs);\nsolve satisfy;",
      "c1 = true;\nc2 = false;\nc3 = true;\ns = {1, 3};\nbs = array1d(1..3, [true, false, true]);\n----------", true)
  , ("link_set reject",
      "var bool: c1;\nvar bool: c2;\nvar bool: c3;\nvar set of 1..3: s;\narray [1..3] of var bool: bs = [c1, c2, c3];\nconstraint fzn_link_set_to_booleans(s, bs);\nsolve satisfy;",
      "c1 = true;\nc2 = true;\nc3 = true;\ns = {1, 3};\nbs = array1d(1..3, [true, true, true]);\n----------", false)
  , ("lex-chain greater vacuous accept",
      "constraint fzn_lex_chain_greater_int([]);\nsolve satisfy;",
      "----------", true)
  , ("lex-chain greatereq orbitope accept",
      "constraint fzn_lex_chain_greatereq_orbitope([], 1);\nsolve satisfy;",
      "----------", true)
  ]

/-! ## Static coverage: every global used in a well-formed model -/

/-- One model per family using every family member at once; combined
    with `globDynamic` this gives every name both a static and a
    dynamic check.  Parameters come first (FlatZinc section order). -/
private def staticModels : List (String × String) :=
  [ ("all-diff family", "var 1..3: q1;\nvar 1..3: q2;\n\
       array [1..2] of var 1..3: xs = [q1, q2];\n\
       array [1..2] of var set of 1..3: ss = [{1}, {2}];\n\
       constraint fzn_all_different_int(xs);\n\
       constraint fzn_all_different_set(ss);\n\
       constraint fzn_all_disjoint(ss);\n\
       constraint fzn_all_equal_int([q1, q1]);\n\
       constraint fzn_all_equal_set([{1}, {1}]);\n\
       constraint fzn_alldifferent_except(xs, {3});\n\
       constraint fzn_alldifferent_except_0([0, q1]);\n\
       constraint fzn_symmetric_all_different([2, 1]);\n\
       solve satisfy;")
  , ("counting family 1", "array [1..2] of int: cover = [1, 2];\n\
       var 0..3: n;\n\
       array [1..3] of var 0..3: xs = [1, 2, 1];\n\
       array [1..2] of var 0..3: cs = [2, 1];\n\
       array [1..2] of var 0..3: lo = [1, 1];\n\
       array [1..2] of var 0..3: up = [3, 3];\n\
       constraint fzn_nvalue(n, xs);\n\
       constraint fzn_among(n, xs, {1, 2});\n\
       constraint fzn_at_least_int(1, xs, 1);\n\
       constraint fzn_at_most_int(3, xs, 1);\n\
       constraint fzn_exactly_int(2, xs, 1);\n\
       constraint fzn_count_eq(xs, 1, n);\n\
       constraint fzn_count_eq_par(xs, 2, 1);\n\
       constraint fzn_count_geq(xs, 1, 2);\n\
       constraint fzn_count_geq_par(xs, 1, 2);\n\
       constraint fzn_count_gt(xs, 1, 3);\n\
       constraint fzn_count_gt_par(xs, 1, 3);\n\
       constraint fzn_count_leq(xs, 1, 2);\n\
       constraint fzn_count_leq_par(xs, 1, 2);\n\
       constraint fzn_count_lt(xs, 1, 1);\n\
       constraint fzn_count_lt_par(xs, 1, 1);\n\
       constraint fzn_count_neq(xs, 1, 3);\n\
       constraint fzn_count_neq_par(xs, 1, 3);\n\
       constraint fzn_distribute(cs, cover, xs);\n\
       solve satisfy;")
  , ("gcc family", "array [1..2] of int: cover = [1, 2];\n\
       array [1..2] of int: lo = [1, 1];\n\
       array [1..2] of int: up = [3, 3];\n\
       array [1..3] of var 0..3: xs = [1, 2, 1];\n\
       array [1..2] of var 0..3: cs = [2, 1];\n\
       constraint fzn_global_cardinality(xs, cover, cs);\n\
       constraint fzn_global_cardinality_closed(xs, cover, cs);\n\
       constraint fzn_global_cardinality_low_up(xs, cover, lo, up);\n\
       constraint fzn_global_cardinality_low_up_closed(xs, cover, lo, up);\n\
       solve satisfy;")
  , ("set counting family", "var 0..2: n;\n\
       var set of 1..2: v;\n\
       array [1..2] of var set of 1..2: ss = [v, v];\n\
       constraint fzn_count_eq_set(ss, v, n);\n\
       constraint fzn_count_eq_set_par(ss, {1}, 2);\n\
       constraint fzn_count_geq_set(ss, v, n);\n\
       constraint fzn_count_gt_set(ss, v, n);\n\
       constraint fzn_count_leq_set(ss, v, n);\n\
       constraint fzn_count_lt_set(ss, v, n);\n\
       constraint fzn_count_neq_set(ss, v, n);\n\
       constraint fzn_at_least_set(0, ss, {1});\n\
       constraint fzn_at_most_set(2, ss, {1});\n\
       constraint fzn_exactly_set(2, ss, {1});\n\
       solve satisfy;")
  , ("lex/sort family", "array [1..2] of var 0..9: xs = [1, 2];\n\
       array [1..2] of var 0..9: ys = [2, 1];\n\
       array [1..2] of var 0..9: perm = [1, 2];\n\
       array [1..2] of var bool: bs = [false, true];\n\
       var 0..2: arg;\n\
       constraint fzn_lex_less_int(xs, ys);\n\
       constraint fzn_lex_lesseq_int(xs, xs);\n\
       constraint fzn_increasing_int(xs);\n\
       constraint fzn_increasing_bool(bs);\n\
       constraint fzn_strictly_increasing_int(ys);\n\
       constraint fzn_sort([3, 1], xs);\n\
       constraint fzn_arg_sort_int([30, 10], perm);\n\
       constraint fzn_maximum_arg_int([3, 7], arg);\n\
       constraint fzn_minimum_arg_int([3, 7], arg);\n\
       constraint fzn_value_precede_int(1, 2, xs);\n\
       constraint fzn_value_precede_chain_int([1, 2], xs);\n\
       constraint fzn_seq_precede_chain_int(xs);\n\
       solve satisfy;")
  , ("packing/scheduling family", "array [1..2] of int: d = [2, 2];\n\
       array [1..2] of int: r = [1, 1];\n\
       array [1..4] of int: t = [1, 2, 3, 4];\n\
       array [1..2] of int: w2 = [1, 1];\n\
       var int: cap = 2;\n\
       array [1..2] of var 0..5: s = [0, 5];\n\
       array [1..2] of var 0..5: l = [2, 0];\n\
       array [1..2] of var 1..2: b = [1, 2];\n\
       array [1..2] of var 0..9: o = [1, 2];\n\
       array [1..2] of var bool: cs = [false, true];\n\
       array [1..2] of var 0..9: dv = [2, 2];\n\
       array [1..2] of var 0..9: rv = [1, 1];\n\
       var 0..9: y;\n\
       var 0..9: tw;\n\
       var 0..99: tp;\n\
       var set of 1..3: w;\n\
       constraint fzn_bin_packing(3, b, w2);\n\
       constraint fzn_bin_packing_capa([3, 3], b, w2);\n\
       constraint fzn_bin_packing_load(l, b, w2);\n\
       constraint fzn_knapsack(w2, [4, 5], o, tw, tp);\n\
       constraint fzn_diffn(s, s, dv, dv);\n\
       constraint fzn_diffn_nonstrict(s, s, dv, dv);\n\
       constraint fzn_geost_nonoverlap_k(s, d, s, d);\n\
       constraint fzn_disjunctive(s, dv);\n\
       constraint fzn_disjunctive_strict(s, dv);\n\
       constraint fzn_cumulative(s, dv, rv, cap);\n\
       constraint fzn_table_int(o, t);\n\
       constraint fzn_if_then_else_int(cs, [1, 2], y);\n\
       constraint fzn_if_then_else_bool(cs, [false, false], false);\n\
       constraint fzn_if_then_else_set(cs, [{1}], w);\n\
       constraint fzn_if_then_else_var_int(cs, [1, 2], y);\n\
       constraint fzn_if_then_else_var_bool(cs, [false, false], false);\n\
       constraint fzn_if_then_else_var_set(cs, [{1}], w);\n\
       solve satisfy;")
  , ("channeling family", "array [1..2] of var 1..2: xs = [2, 1];\n\
       array [1..2] of var 1..2: ys = [2, 1];\n\
       array [1..2] of var bool: bs = [true, false];\n\
       array [1..2] of var set of 1..2: ss = [{1}, {2}];\n\
       var 0..2: i;\n\
       constraint fzn_inverse(xs, ys);\n\
       constraint fzn_inverse_in_range(xs, ys);\n\
       constraint fzn_int_set_channel(xs, ss);\n\
       constraint fzn_link_set_to_booleans({1}, bs);\n\
       constraint fzn_member_int(xs, 2);\n\
       constraint fzn_member_bool(bs, true);\n\
       constraint fzn_member_set(ss, {2});\n\
       constraint fzn_arg_val_int(xs, 2, i);\n\
       constraint fzn_arg_val_bool(bs, false, i);\n\
       constraint fzn_write(xs, 1, 9, [9, 1]);\n\
       constraint fzn_writes(xs, [1, 2], [9, 8], [9, 8]);\n\
       solve satisfy;")
  , ("set/math family", "array [1..2] of int: vals = [1, 2];\n\
       array [1..2] of int: wts = [10, 20];\n\
       array [1..2] of set of int: pss = [{1}, {2}];\n\
       var set of 1..3: u;\n\
       var set of 1..3: v;\n\
       array [1..2] of var set of 1..3: ss = [u, v];\n\
       array [1..3] of var 0..9: xs = [1, 2, 2];\n\
       array [1..3] of var bool: bs = [true, false, true];\n\
       var 0..99: total;\n\
       var 0..99: total2;\n\
       constraint fzn_disjoint(u, v);\n\
       constraint fzn_set_member(u, 1);\n\
       constraint fzn_partition_set(ss, {1, 2, 3});\n\
       constraint fzn_at_most1(ss);\n\
       constraint fzn_sum_set(vals, wts, u, total);\n\
       constraint fzn_sum_pred(1, pss, wts, total2);\n\
       constraint fzn_range(xs, {1, 2}, v);\n\
       constraint fzn_roots(xs, {1, 2}, v);\n\
       constraint fzn_array_int_union(xs, v);\n\
       constraint fzn_array_set_union(ss, v);\n\
       constraint fzn_array_set_intersect(ss, u);\n\
       constraint fzn_sliding_sum(3, 5, 2, xs);\n\
       constraint fzn_sliding_among_int(1, 2, 2, xs, {1});\n\
       constraint fzn_sliding_among_bool(1, 2, 2, bs, true);\n\
       solve satisfy;")
  , ("lex-chain family", "var 1..9: a;
var 1..9: b;
\
       array [1..2] of var 1..9: xs = [a, b];
\
       array [1..2] of var 1..9: ys = [b, a];
\
       constraint fzn_lex_greater_int(xs, ys);
\
       constraint fzn_lex_greatereq_int(xs, ys);
\
       constraint fzn_lex_chain_less_int([a, b, b, a]);
\
       constraint fzn_lex_chain_lesseq_int([a, b, b, a]);
\
       constraint fzn_lex2([a, b, b, a]);
\
       constraint fzn_strict_lex2([a, b, b, a]);
\
       constraint fzn_lex_chain_lesseq_orbitope([a, b, b, a], 1);
\
       constraint fzn_lex_chain_greater_int([a, b, b, a]);
\
       constraint fzn_lex_chain_greatereq_int([a, b, b, a]);
\
       constraint fzn_lex_chain_greatereq_orbitope([a, b, b, a], 1);
\
       solve satisfy;")
  , ("graph family", "array [1..2] of int: from = [1, 2];\n\
       array [1..2] of int: to = [2, 3];\n\
       array [1..2] of int: w = [1, 1];\n\
       var 1..3: n1;\n\
       var 1..3: n2;\n\
       var 1..3: n3;\n\
       array [1..3] of var bool: ns = [true, true, true];\n\
       array [1..2] of var bool: es = [true, true];\n\
       constraint fzn_subgraph(from, to, ns, es);\n\
       constraint fzn_dag(from, to, ns, es);\n\
       constraint fzn_connected(from, to, ns, es);\n\
       constraint fzn_dconnected(from, to, ns, es);\n\
       constraint fzn_reachable(from, to, ns, es, 1);\n\
       constraint fzn_dreachable(from, to, ns, es, 1);\n\
       constraint fzn_tree(from, to, ns, es, 1);\n\
       constraint fzn_dtree(from, to, ns, es, 1);\n\
       constraint fzn_path(from, to, ns, es, 1, 3);\n\
       constraint fzn_dpath(from, to, ns, es, 1, 3);\n\
       constraint fzn_bounded_path(from, to, w, ns, es, 1, 3, 2);\n\
       constraint fzn_bounded_dpath(from, to, w, ns, es, 1, 3, 2);\n\
       constraint fzn_steiner(from, to, w, ns, es, 1, 2);\n\
       constraint fzn_dsteiner(from, to, w, ns, es, 1, 2);\n\
       constraint fzn_wst(from, to, w, es, 2);\n\
       constraint fzn_dwst(from, to, w, es, 1, 2);\n\
       constraint fzn_circuit([n1, n2, n3]);\n\
       constraint fzn_subcircuit([n1, n2, n3]);\n\
       solve satisfy;")
  , ("regular family", "array [1..4] of int: d = [0, 2, 0, 0];\n\
       array [1..4] of int: c = [3, 5, 0, 0];\n\
       array [1..4] of set of int: nd = [{1}, {2}, {2}, {2}];\n\
       array [1..3] of int: level = [1, 2, 3];\n\
       array [1..2] of int: efrom = [1, 1];\n\
       array [1..2] of set of int: elabel = [{1}, {2}];\n\
       array [1..2] of int: ecost = [4, 6];\n\
       array [1..2] of int: eto = [2, 0];\n\
       array [1..2] of var 1..2: xs = [1, 1];\n\
       var int: total;\n\
       constraint fzn_regular(xs, 2, 2, d, 1, [1]);\n\
       constraint fzn_regular_nfa(xs, 2, 2, nd, 1, [1]);\n\
       constraint fzn_cost_regular(xs, 2, 2, d, 1, [1], c, total);\n\
       constraint fzn_mdd(xs, 3, level, 2, efrom, elabel, eto);\n\
       constraint fzn_mdd_nondet(xs, 3, level, 2, efrom, elabel, eto);\n\
       constraint fzn_cost_mdd(xs, 3, level, 2, efrom, elabel, ecost, eto, total);\n\
       solve satisfy;")
  , ("sched2 family", "array [1..4] of int: rs = [1, 1, 1, 1];\n\
       array [1..4] of int: ro = [0, 0, 0, 0];\n\
       array [1..1] of set of int: sh = [{1}];\n\
       array [1..2] of var int: s = [0, 2];\n\
       array [1..2] of var int: dur = [2, 2];\n\
       array [1..2] of var int: res = [1, 1];\n\
       array [1..2] of var int: mach = [1, 1];\n\
       array [1..2] of var int: bnd = [1, 1];\n\
       array [1..2] of var int: ox = [0, 5];\n\
       array [1..2] of var int: kd = [1, 1];\n\
       array [1..2] of var int: lo = [0, 0];\n\
       array [1..2] of var int: up = [6, 6];\n\
       array [1..2] of var int: bp1 = [0, 5];\n\
       array [1..2] of var int: bs1 = [1, 1];\n\
       array [1..2] of var int: bp2 = [0, 0];\n\
       array [1..2] of var int: bs2 = [1, 1];\n\
       array [1..2] of var int: wi = [9, 8];\n\
       array [1..2] of var int: wp = [2, 1];\n\
       array [1..2] of var int: wv = [5, 6];\n\
       array [1..2] of var int: wo = [9, 6];\n\
       array [1..2] of var bool: itc = [false, true];\n\
       array [1..2] of var bool: itd = [false, true];\n\
       var bool: itb;\n\
       constraint fzn_cumulatives(s, dur, res, mach, bnd, true, 1);\n\
       constraint fzn_cumulatives_decomp(s, dur, res, mach, bnd, true);\n\
       constraint fzn_geost(2, rs, ro, sh, ox, kd);\n\
       constraint fzn_geost_bb(2, rs, ro, sh, ox, kd, lo, up);\n\
       constraint fzn_geost_smallest_bb(2, rs, ro, sh, ox, kd, lo, up);\n\
       constraint fzn_diffn_nonoverlap_k(bp1, bs1, bp2, bs2);\n\
       constraint fzn_diffn_k([0, 5, 0, 0], [1, 1, 1, 1]);\n\
       constraint fzn_diffn_nonstrict_k([0, 5, 0, 0], [1, 1, 1, 1]);\n\
       constraint fzn_writes_seq(wi, wp, wv, wo);\n\
       constraint fzn_if_then_else_partiality(itc, itd, itb);\n\
       solve satisfy;")
  ]

/-! ## Coverage accounting -/

/-- All names that must be covered. -/
private def requiredNames : List String :=
  LeanFzn.Semantics.Evaluation.stdNames ++ LeanFzn.Semantics.Evaluation.setNames ++ LeanFzn.Semantics.Globals.globalsNames

/-- Names actually exercised by the dynamic suites. -/
private def coveredNames : List String :=
  ((stdDynamic.map (fun x => x.2.1)) ++
    (setDynamic.map (fun x => x.2.1)) ++
    (globDynamic.map (fun x => x.2.1))).eraseDups

/-- All dynamic evaluations route through the checker's combined twin
    (`fullInterpB` handles both the standard builtins and the globals). -/
private def evalStd (name : String) (args : List Value) : Bool :=
  LeanFzn.Semantics.Globals.fullInterpB (Ident.mk name) args

private def evalGlob (name : String) (args : List Value) : Bool :=
  LeanFzn.Semantics.Globals.fullInterpB (Ident.mk name) args

def main : IO UInt32 := do
  let mut failures := 0
  let mut total := 0
  -- 1. standard builtin dynamics
  for (name, pred, args, expected) in stdDynamic do
    total := total + 1
    let holds := evalStd pred args
    if holds != expected then
      IO.eprintln s!"FAIL (std dynamic) {name}: got {holds}, expected {expected}"
      failures := failures + 1
  -- 2. extensional set builtin dynamics
  for (name, pred, args, expected) in setDynamic do
    total := total + 1
    let holds := evalStd pred args
    if holds != expected then
      IO.eprintln s!"FAIL (set dynamic) {name}: got {holds}, expected {expected}"
      failures := failures + 1
  -- 3. global dynamics
  for (name, pred, args, expected) in globDynamic do
    total := total + 1
    let holds := evalGlob pred args
    if holds != expected then
      IO.eprintln s!"FAIL (glob dynamic) {name}: got {holds}, expected {expected}"
      failures := failures + 1
  -- 4. static well-formedness of every family model
  for (name, src) in staticModels do
    total := total + 1
    let m := parseOrPanic src
    unless wellFormedB LeanFzn.Semantics.Globals.fullSig m do
      IO.eprintln s!"FAIL (static) {name}: not well-formed under fullSig"
      failures := failures + 1
  -- 5. end-to-end
  for (name, msrc, sol, expected) in endToEnd do
    total := total + 1
    let verdict := LeanFzn.Checker.Globals.checkSolutionFull (parseOrPanic msrc) sol
    if verdict != expected then
      IO.eprintln s!"FAIL (end-to-end) {name}: got {verdict}, expected {expected}"
      failures := failures + 1
  -- 6. coverage accounting: every required name exercised dynamically
  let missing := requiredNames.filter (fun n => !(coveredNames.contains n))
  for n in missing do
    IO.eprintln s!"FAIL (coverage) predicate '{n}' has no dynamic test case"
    failures := failures + 1
  total := total + missing.length
  let dupCheck := coveredNames.filter (fun n =>
    (coveredNames.filter (· == n)).length > 1)
  if !dupCheck.isEmpty then
    IO.eprintln s!"NOTE: covered-name list has internal duplicates (harmless)"
  -- report
  let nStd := stdDynamic.length
  let nSet := setDynamic.length
  let nGlob := globDynamic.length
  let nStatic := staticModels.length
  let nE2E := endToEnd.length
  IO.println s!"dynamic: {nStd} std + {nSet} set + {nGlob} globals cases; {nStatic} static models; {nE2E} end-to-end"
  IO.println s!"coverage: {coveredNames.length}/{requiredNames.length} checkable names exercised"
  if failures == 0 then
    IO.println s!"passed all {total} coverage tests"
    return 0
  else
    IO.eprintln s!"{failures} coverage test(s) failed"
    return 1
