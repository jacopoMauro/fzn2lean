import LeanFzn
import LeanFzn.FznGlobals

/-!
# Gecode-derived tests

Regression tests ported from the Gecode constraint solver's FlatZinc
test suite (`gecode/test/flatzinc/*.cpp`, MIT-licensed, fetched from
https://github.com/Gecode/gecode).  Each case is a FlatZinc model and a
solver-produced solution string; the test asserts that
`checkSolutionFull` accepts the reference solution (and rejects
deliberately corrupted variants), and that rejected/wrong answers stay
rejected.

Gecode's tests exercise the solver end-to-end; here we exercise the
*checker*: a Gecode-accepted solution must satisfy every dynamic
condition of `Satisfies` under `fullInterp`, which is exactly what
`checkSolutionFull` decides (per `checkSolutionFull_correct`).

Adaptations for the pinned MiniZinc 2.10.0 grammar of this project:

* array variable declarations carry an initializer (the grammar's
  `<array-var-type>` rule requires `= <array-literal>`), where Gecode
  also accepts uninitialized arrays;
* no array indexing in expressions (`q[1]` is a Gecode extension, not
  in the FlatZinc grammar) — the queens4 case uses scalar variables
  instead;
* float variables and float predicates are out of scope (dropped);
* `int_div`/`int_mod` semantics: truncated division, per the handbook
  ("rounded to the value closest to zero") — exactly the semantics
  pinned by Gecode's `test_int_div.cpp`/`test_int_mod.cpp`, and now
  implemented with `Int.tdiv`/`Int.tmod`.
-/

open LeanFzn LeanFzn.Globals LeanFzn.Solution

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- A test case: name, model source, reference solution, corrupted
    variants that must be rejected. -/
structure GecodeCase where
  name : String
  model : String
  good : List String
  bad : List String

/-! ## int_div / int_mod — Gecode `test_int_div.cpp`, `test_int_mod.cpp`

Truncated division and modulo on all four sign combinations; Gecode's
expected outputs are `7 div 4 = 1`, `-7 div 4 = -1`,
`7 div -4 = -1`, `-7 div -4 = 1` and `7 mod 4 = 3`, `-7 mod 4 = -3`,
`7 mod -4 = 3`, `-7 mod -4 = -3`.  These pin the truncated (not
Euclidean, not floored) semantics of the handbook's `int_div`. -/

private def intDivCase : GecodeCase :=
  { name := "gecode int_div"
  , model :=
      "var int: a;\n\
      var int: b;\n\
      var int: c;\n\
      var int: d;\n\
      constraint int_div(7, 4, a);\n\
      constraint int_div(-7, 4, b);\n\
      constraint int_div(7, -4, c);\n\
      constraint int_div(-7, -4, d);\n\
      solve satisfy;"
  , good :=
      [ "a = 1;\nb = -1;\nc = -1;\nd = 1;\n----------" ]
  , bad :=
      [ -- Euclidean-division answers would be wrong here:
        "a = 1;\nb = -2;\nc = -2;\nd = 1;\n----------"
        -- floored answers, also wrong:
      , "a = 1;\nb = -2;\nc = -1;\nd = 1;\n----------"
      , "a = 3;\nb = -2;\nc = -2;\nd = 1;\n----------"
      , "a = 2;\nb = -1;\nc = -1;\nd = 1;\n----------"
      ] }

private def intModCase : GecodeCase :=
  { name := "gecode int_mod"
  , model :=
      "var int: a;\n\
      var int: b;\n\
      var int: c;\n\
      var int: d;\n\
      var 0..10: x;\n\
      var 0..10: y;\n\
      constraint int_mod(7, 4, a);\n\
      constraint int_mod(-7, 4, b);\n\
      constraint int_mod(7, -4, c);\n\
      constraint int_mod(-7, -4, d);\n\
      constraint int_mod(x, y, 3);\n\
      solve satisfy;"
  , good :=
      [ "a = 3;\nb = -3;\nc = 3;\nd = -3;\nx = 3;\ny = 4;\n----------"
      , "a = 3;\nb = -3;\nc = 3;\nd = -3;\nx = 3;\ny = 7;\n----------" ]
  , bad :=
      [ -- Euclidean-division mod (always non-negative) is wrong:
        "a = 3;\nb = 1;\nc = 3;\nd = 1;\nx = 3;\ny = 4;\n----------"
      , "a = 3;\nb = -3;\nc = 3;\nd = -3;\nx = 4;\ny = 3;\n----------" -- 4 mod 3 = 1 ≠ 3
      ] }

/-! ## fzn_arith — Gecode `test_fzn_arith.cpp` (int part)

`int_plus`, `int_times`, `int_div`, `int_mod`, `int_min`, `int_max`,
`int_abs` with mixed par/var arguments, and the reference solution
Gecode reports (`i1 = 2` from `int_plus(i1, 1, 3)`, `i3 = 4` from
`int_times(i3, 2, 8)`, `i5 = 6` from `int_div(i5, 3, 2)`,
`i6 = 6` from `int_mod(i6, 6, 0)`, `i7 = 8` from `int_min(i7, 9, 8)`,
`i8 = 9` from `int_max(i8, 7, 9)`, `i9 = 10` from `int_abs(-10, i9)`). -/

private def fznArithCase : GecodeCase :=
  { name := "gecode fzn_arith (int)"
  , model :=
      "var 1..10: i1;\n\
      var 1..10: i2;\n\
      var 1..10: i3;\n\
      var 1..10: i4;\n\
      var 1..10: i5;\n\
      var 1..10: i6;\n\
      var 1..10: i7;\n\
      var 1..10: i8;\n\
      var 1..10: i9;\n\
      constraint int_plus(1, 1, 2);\n\
      constraint int_plus(i1, 1, 3);\n\
      constraint int_plus(0, 1, 1);\n\
      constraint int_plus(2, 1, i2);\n\
      constraint int_times(1, 1, 1);\n\
      constraint int_times(i3, 2, 8);\n\
      constraint int_plus(-1, 1, 0);\n\
      constraint int_plus(-5, i4, 0);\n\
      constraint int_div(1, 1, 1);\n\
      constraint int_div(i5, 3, 2);\n\
      constraint int_mod(1, 2, 1);\n\
      constraint int_mod(i6, 6, 0);\n\
      constraint int_min(1, 2, 1);\n\
      constraint int_min(i7, 9, 8);\n\
      constraint int_max(1, 2, 2);\n\
      constraint int_max(i8, 7, 9);\n\
      constraint int_abs(-1, 1);\n\
      constraint int_abs(-10, i9);\n\
      solve satisfy;"
  , good :=
      [ "i1 = 2;\ni2 = 3;\ni3 = 4;\ni4 = 5;\ni5 = 6;\ni6 = 6;\ni7 = 8;\ni8 = 9;\ni9 = 10;\n----------" ]
  , bad :=
      [ "i1 = 2;\ni2 = 3;\ni3 = 4;\ni4 = 5;\ni5 = 5;\ni6 = 6;\ni7 = 8;\ni8 = 9;\ni9 = 10;\n----------"
        -- i5 = 5 violates int_div(i5, 3, 2): 5 tdiv 3 = 1 ≠ 2
      , "i1 = 2;\ni2 = 3;\ni3 = 5;\ni4 = 5;\ni5 = 6;\ni6 = 6;\ni7 = 8;\ni8 = 9;\ni9 = 10;\n----------"
        -- i3 = 5 violates int_times(i3, 2, 8)
      , "i1 = 2;\ni2 = 3;\ni3 = 4;\ni4 = 5;\ni5 = 6;\ni6 = 6;\ni7 = 9;\ni8 = 9;\ni9 = 10;\n----------"
        -- i7 = 9 violates int_min(i7, 9, 8)
      , "i1 = 2;\ni2 = 3;\ni3 = 4;\ni4 = 5;\ni5 = 6;\ni6 = 6;\ni7 = 8;\ni8 = 9;\ni9 = -10;\n----------"
        -- i9 = -10 violates int_abs(-10, i9)
      ] }

/-! ## fzn_logic — Gecode `test_fzn_logic.cpp`

The truth tables of `bool_and`, `bool_or`, `bool_xor`, `bool_not`,
`bool_le_reif`, `array_bool_and`, `array_bool_or` on par literals,
plus the reference solution for the variable occurrences.  The array
variables are given initializers of fresh variables (grammar
adaptation). -/

private def fznLogicCase : GecodeCase :=
  { name := "gecode fzn_logic"
  , model :=
      "var bool: b1;\n\
      var bool: b2;\n\
      var bool: b3;\n\
      var bool: b4;\n\
      var bool: b5;\n\
      var bool: b6;\n\
      array [1..3] of var bool: ab1 = [b1, b2, b3];\n\
      array [1..3] of var bool: ab2 = [b4, b5, b6];\n\
      constraint bool_eq(true, true);\n\
      constraint bool_eq(false, false);\n\
      constraint bool_not(true, false);\n\
      constraint bool_not(false, true);\n\
      constraint bool_and(false, true, false);\n\
      constraint bool_and(false, false, false);\n\
      constraint bool_and(true, false, false);\n\
      constraint bool_and(true, true, true);\n\
      constraint bool_and(b1, true, true);\n\
      constraint bool_or(false, true, true);\n\
      constraint bool_or(false, false, false);\n\
      constraint bool_or(true, false, true);\n\
      constraint bool_or(true, true, true);\n\
      constraint bool_or(b2, false, true);\n\
      constraint bool_xor(false, true, true);\n\
      constraint bool_xor(false, false, false);\n\
      constraint bool_xor(true, false, true);\n\
      constraint bool_xor(true, true, false);\n\
      constraint bool_xor(b3, false, true);\n\
      constraint bool_le_reif(false, true, true);\n\
      constraint bool_le_reif(false, false, true);\n\
      constraint bool_le_reif(true, false, false);\n\
      constraint bool_le_reif(true, true, true);\n\
      constraint bool_le_reif(true, b4, true);\n\
      constraint bool_not(false, true);\n\
      constraint bool_not(true, false);\n\
      constraint bool_not(b6, false);\n\
      constraint array_bool_and([false], false);\n\
      constraint array_bool_and([true], true);\n\
      constraint array_bool_and([false, true], false);\n\
      constraint array_bool_and([false, false], false);\n\
      constraint array_bool_and([true, false], false);\n\
      constraint array_bool_and([true, true], true);\n\
      constraint array_bool_and(ab1, true);\n\
      constraint array_bool_or([false], false);\n\
      constraint array_bool_or([true], true);\n\
      constraint array_bool_or([false, true], true);\n\
      constraint array_bool_or([false, false], false);\n\
      constraint array_bool_or([true, false], true);\n\
      constraint array_bool_or([true, true], true);\n\
      constraint array_bool_or(ab2, true);\n\
      solve satisfy;"
  , good :=
      [ -- adapted reference: b1..b4, b6 forced true by their constraints; b5 free
        "ab1 = array1d(1..3, [true, true, true]);\n\
         ab2 = array1d(1..3, [true, false, true]);\n\
         b1 = true;\nb2 = true;\nb3 = true;\nb4 = true;\nb5 = false;\nb6 = true;\n----------"
      , "ab1 = array1d(1..3, [true, true, true]);\n\
         ab2 = array1d(1..3, [true, true, true]);\n\
         b1 = true;\nb2 = true;\nb3 = true;\nb4 = true;\nb5 = true;\nb6 = true;\n----------" ]
  , bad :=
      [ -- b1 = false violates bool_and(b1, true, true)
        "ab1 = array1d(1..3, [false, true, true]);\n\
         ab2 = array1d(1..3, [true, false, true]);\n\
         b1 = false;\nb2 = true;\nb3 = true;\nb4 = true;\nb5 = false;\nb6 = true;\n----------"
      , -- b6 = false violates bool_not(b6, false)
        "ab1 = array1d(1..3, [true, true, true]);\n\
         ab2 = array1d(1..3, [true, false, false]);\n\
         b1 = true;\nb2 = true;\nb3 = true;\nb4 = true;\nb5 = false;\nb6 = false;\n----------"
      , -- a truth-table row corrupted: bool_xor(b3, false, true) forces b3 = true
        "ab1 = array1d(1..3, [true, true, true]);\n\
         ab2 = array1d(1..3, [true, false, true]);\n\
         b1 = true;\nb2 = true;\nb3 = false;\nb4 = true;\nb5 = false;\nb6 = true;\n----------"
      , -- initializer consistency: ab1 says [T,T,T] but b3 = false
        "ab1 = array1d(1..3, [true, true, true]);\n\
         ab2 = array1d(1..3, [true, false, true]);\n\
         b1 = true;\nb2 = true;\nb3 = false;\nb4 = true;\nb5 = false;\nb6 = true;\n----------"
      ] }

/-! ## fzn_comparison — Gecode `test_fzn_comparison.cpp` (int/set part)

`int_lt/le/eq/ne` and their `_reif` forms, `set_lt`, `set_le`,
`set_eq`, `set_ne` (lexicographic and extensional), `int_lin_le`,
`int_lin_eq`, `int_lin_le_reif`, `int_lin_eq_reif`, `set_in`.  The
fresh set variables `s1..s6` are constrained to equal specific sets;
Gecode's reference solution is one possible completion. -/

private def fznComparisonCase : GecodeCase :=
  { name := "gecode fzn_comparison (int/set)"
  , model :=
      "var 1..10: i1;\n\
      var 1..10: i2;\n\
      var 1..10: i3;\n\
      var 1..10: i4;\n\
      var 1..10: i5;\n\
      var 1..10: i6;\n\
      var bool: ri1;\n\
      var bool: ri2;\n\
      var bool: ri3;\n\
      var bool: ri4;\n\
      var bool: ri5;\n\
      var bool: ri6;\n\
      var 1..10: j1;\n\
      var 1..10: j2;\n\
      var 1..10: j3;\n\
      var 1..10: k1;\n\
      var 1..10: k2;\n\
      var 1..10: k3;\n\
      var 1..10: l1;\n\
      var 1..10: l2;\n\
      var 1..10: l3;\n\
      array [1..3] of var 1..10: ia2 = [j1, j2, j3];\n\
      array [1..3] of var 1..10: ia4 = [k1, k2, k3];\n\
      array [1..3] of var 1..10: ia5 = [l1, l2, l3];\n\
      var set of 1..3: s1;\n\
      var set of 1..3: s2;\n\
      var set of 1..3: s3;\n\
      var set of 1..3: s4;\n\
      var set of 1..3: s5;\n\
      var set of 1..3: s6;\n\
      constraint int_lt(2, 3);\n\
      constraint int_lt(2, i1);\n\
      constraint int_lt(i1, 9);\n\
      constraint int_le(2, 3);\n\
      constraint int_le(2, i2);\n\
      constraint int_le(i2, 9);\n\
      constraint int_le(2, i3);\n\
      constraint int_le(i3, 9);\n\
      constraint int_lt(2, i4);\n\
      constraint int_lt(i4, 9);\n\
      constraint int_eq(2, 2);\n\
      constraint int_eq(2, i5);\n\
      constraint int_ne(2, 3);\n\
      constraint int_ne(1, i6);\n\
      constraint int_lt_reif(2, 3, ri1);\n\
      constraint int_lt_reif(2, i1, ri1);\n\
      constraint int_lt_reif(i1, 9, ri1);\n\
      constraint int_le_reif(2, 3, ri2);\n\
      constraint int_le_reif(2, i2, ri2);\n\
      constraint int_le_reif(i2, 9, ri2);\n\
      constraint int_le_reif(2, 3, ri3);\n\
      constraint int_le_reif(2, i3, ri3);\n\
      constraint int_le_reif(i3, 9, ri3);\n\
      constraint int_lt_reif(2, 3, ri4);\n\
      constraint int_lt_reif(2, i4, ri4);\n\
      constraint int_lt_reif(i4, 9, ri4);\n\
      constraint int_eq_reif(2, 2, ri5);\n\
      constraint int_eq_reif(2, i5, ri5);\n\
      constraint int_ne_reif(2, 3, ri6);\n\
      constraint int_ne_reif(1, i6, ri6);\n\
      constraint set_lt({}, {1, 2, 3});\n\
      constraint set_lt({}, s1);\n\
      constraint set_lt(s1, {1, 2, 3});\n\
      constraint set_le({}, {1, 2, 3});\n\
      constraint set_le({1}, s2);\n\
      constraint set_le(s2, {1, 2, 3});\n\
      constraint set_lt({}, s3);\n\
      constraint set_lt(s3, {1, 2, 3});\n\
      constraint set_le({1}, s4);\n\
      constraint set_le(s4, {1, 2, 3});\n\
      constraint set_eq({1, 2, 3}, {1, 2, 3});\n\
      constraint set_eq(s5, {1, 2, 3});\n\
      constraint set_ne({}, {1, 2, 3});\n\
      constraint set_ne(s6, {1, 2, 3});\n\
      constraint int_lin_le([1, 2, 3], [1, 2, 3], 100);\n\
      constraint int_lin_le([1, 2, 3], ia2, 10);\n\
      constraint int_lin_le([-1, -2, -3], [1, 2, 3], -10);\n\
      constraint int_lin_le([-1, -2, -3], ia4, -10);\n\
      constraint int_lin_eq([1, 2, 3], [1, 2, 3], 14);\n\
      constraint int_lin_eq([1, 2, 3], ia5, 14);\n\
      constraint int_lin_le_reif([1, 2, 3], [1, 2, 3], 100, ri2);\n\
      constraint int_lin_le_reif([1, 2, 3], ia2, 10, ri2);\n\
      constraint int_lin_le_reif([-1, -2, -3], [1, 2, 3], -10, ri4);\n\
      constraint int_lin_le_reif([-1, -2, -3], ia4, -10, ri4);\n\
      constraint int_lin_eq_reif([1, 2, 3], [1, 2, 3], 14, ri5);\n\
      constraint int_lin_eq_reif([1, 2, 3], ia5, 14, ri5);\n\
      solve satisfy;"
  , good :=
      [ "i1 = 3;\ni2 = 3;\ni3 = 3;\ni4 = 3;\ni5 = 2;\ni6 = 3;\n\
         ri1 = true;\nri2 = true;\nri3 = true;\nri4 = true;\nri5 = true;\nri6 = true;\n\
         j1 = 1;\nj2 = 1;\nj3 = 2;\nk1 = 2;\nk2 = 2;\nk3 = 2;\n\
         l1 = 2;\nl2 = 3;\nl3 = 2;\n\
         s1 = {1, 2};\ns2 = {1, 2};\ns3 = {1, 2};\ns4 = {1, 2};\ns5 = {1, 2, 3};\ns6 = {1, 2};\n----------" ]
  , bad :=
      [ -- set_eq(s5, {1,2,3}) violated
        "i1 = 3;\ni2 = 3;\ni3 = 3;\ni4 = 3;\ni5 = 2;\ni6 = 3;\n\
         ri1 = true;\nri2 = true;\nri3 = true;\nri4 = true;\nri5 = true;\nri6 = true;\n\
         j1 = 1;\nj2 = 1;\nj3 = 2;\nk1 = 2;\nk2 = 2;\nk3 = 2;\n\
         l1 = 2;\nl2 = 3;\nl3 = 2;\n\
         s1 = {1, 2};\ns2 = {1, 2};\ns3 = {1, 2};\ns4 = {1, 2};\ns5 = {1, 2};\ns6 = {1, 2};\n----------"
      , -- int_eq(2, i5) violated (and its reification honestly flipped)
        "i1 = 3;\ni2 = 3;\ni3 = 3;\ni4 = 3;\ni5 = 4;\ni6 = 3;\n\
         ri1 = true;\nri2 = true;\nri3 = true;\nri4 = true;\nri5 = false;\nri6 = true;\n\
         j1 = 1;\nj2 = 1;\nj3 = 2;\nk1 = 2;\nk2 = 2;\nk3 = 2;\n\
         l1 = 2;\nl2 = 3;\nl3 = 2;\n\
         s1 = {1, 2};\ns2 = {1, 2};\ns3 = {1, 2};\ns4 = {1, 2};\ns5 = {1, 2, 3};\ns6 = {1, 2};\n----------"
      , -- int_lin_eq([1,2,3], ia5, 14) violated: l-sum = 2+6+6 = 14 ok, corrupt l3
        "i1 = 3;\ni2 = 3;\ni3 = 3;\ni4 = 3;\ni5 = 2;\ni6 = 3;\n\
         ri1 = true;\nri2 = true;\nri3 = true;\nri4 = true;\nri5 = false;\nri6 = true;\n\
         j1 = 1;\nj2 = 1;\nj3 = 2;\nk1 = 2;\nk2 = 2;\nk3 = 2;\n\
         l1 = 2;\nl2 = 3;\nl3 = 3;\n\
         s1 = {1, 2};\ns2 = {1, 2};\ns3 = {1, 2};\ns4 = {1, 2};\ns5 = {1, 2, 3};\ns6 = {1, 2};\n----------"
      ] }

/-! ## fzn_sets — Gecode `test_fzn_sets.cpp`

`set_in`, `set_in_reif`, `set_subset`, `set_subset_reif`,
`set_intersect`, `set_diff`, `set_symdiff`, `set_union`, `set_card`
on par set literals and fresh set variables, with Gecode's reference
solutions (one satisfying completion). -/

private def fznSetsCase : GecodeCase :=
  { name := "gecode fzn_sets"
  , model :=
      "var set of 1..10: s1;\n\
      var set of 1..10: s2;\n\
      var set of 1..10: s3;\n\
      var set of 1..10: s4;\n\
      var set of 1..10: s5;\n\
      var set of 1..10: s6;\n\
      var set of 1..10: s7;\n\
      var set of 1..10: s8;\n\
      var bool: rs1;\n\
      var bool: rs2;\n\
      var bool: rs3;\n\
      constraint set_in(1, {1, 2, 3});\n\
      constraint set_in(1, s1);\n\
      constraint set_in_reif(2, s1, rs1);\n\
      constraint set_subset({1, 2}, {1, 2, 3});\n\
      constraint set_subset({1, 2}, s2);\n\
      constraint set_subset_reif({1, 2, 3}, s2, rs2);\n\
      constraint set_subset({1, 2, 3}, s3);\n\
      constraint set_subset_reif({1, 2, 3, 4}, s3, rs3);\n\
      constraint set_intersect({1, 2, 3}, {1, 3, 5}, {1, 3});\n\
      constraint set_intersect(s4, {1, 2, 3}, {1, 3});\n\
      constraint set_diff({1, 2, 3}, {1, 3, 5}, {2});\n\
      constraint set_diff(s5, {2}, {1, 3});\n\
      constraint set_symdiff({1, 2, 3}, {1, 3, 5}, {2, 5});\n\
      constraint set_symdiff(s6, {2, 5}, {1, 5});\n\
      constraint set_union({1, 2, 3}, {1, 3, 5}, {1, 2, 3, 5});\n\
      constraint set_union(s7, {2, 5}, {1, 2, 3, 4, 5});\n\
      constraint set_card({1, 2, 3}, 3);\n\
      constraint set_card(s8, 3);\n\
      solve satisfy;"
  , good :=
      [ "rs1 = false;\nrs2 = false;\nrs3 = false;\n\
         s1 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s2 = {1, 2, 4, 5, 6, 7, 8, 9, 10};\n\
         s3 = {1, 2, 3, 5, 6, 7, 8, 9, 10};\n\
         s4 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s5 = 1..3;\n\
         s6 = 1..2;\n\
         s7 = 1..5;\n\
         s8 = 1..3;\n----------"
      , -- a second satisfying completion with enumeration-style sets
        "rs1 = true;\nrs2 = true;\nrs3 = true;\n\
         s1 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s2 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s3 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s4 = {1, 3};\n\
         s5 = {1, 3};\n\
         s6 = {1, 2};\n\
         s7 = {1, 2, 3, 4, 5};\n\
         s8 = {2, 3, 5};\n----------" ]
  , bad :=
      [ -- set_in(1, s1) violated
        "rs1 = false;\nrs2 = false;\nrs3 = false;\n\
         s1 = {2, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s2 = {1, 2, 4, 5, 6, 7, 8, 9, 10};\n\
         s3 = {1, 2, 3, 5, 6, 7, 8, 9, 10};\n\
         s4 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s5 = 1..3;\n\
         s6 = 1..2;\n\
         s7 = 1..5;\n\
         s8 = 1..3;\n----------"
      , -- set_card(s8, 3) violated: {1,2} has cardinality 2
        "rs1 = false;\nrs2 = false;\nrs3 = false;\n\
         s1 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s2 = {1, 2, 4, 5, 6, 7, 8, 9, 10};\n\
         s3 = {1, 2, 3, 5, 6, 7, 8, 9, 10};\n\
         s4 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s5 = 1..3;\n\
         s6 = 1..2;\n\
         s7 = 1..5;\n\
         s8 = {1, 2};\n----------"
      , -- set_symdiff(s6, {2,5}, {1,5}) violated: symdiff of {2,5} and {2,5} is {}
        "rs1 = false;\nrs2 = false;\nrs3 = false;\n\
         s1 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s2 = {1, 2, 4, 5, 6, 7, 8, 9, 10};\n\
         s3 = {1, 2, 3, 5, 6, 7, 8, 9, 10};\n\
         s4 = {1, 3, 4, 5, 6, 7, 8, 9, 10};\n\
         s5 = 1..3;\n\
         s6 = {2, 5};\n\
         s7 = 1..5;\n\
         s8 = 1..3;\n----------"
      ] }

/-! ## fzn_arrays — Gecode `test_fzn_arrays.cpp` (int/bool/set part)

`array_bool_element`, `array_var_bool_element`, `array_int_element`,
`array_var_int_element`, `array_set_element`,
`array_var_set_element` with the reference completion. -/

private def fznArraysCase : GecodeCase :=
  { name := "gecode fzn_arrays"
  , model :=
      "var bool: b1;\n\
      var 1..10: i1;\n\
      var set of 1..10: s1;\n\
      var set of 1..10: s2;\n\
      array [1..3] of var bool: ab1 = [b1, true, false];\n\
      array [1..3] of var 1..10: ai1 = [i1, 2, 3];\n\
      array [1..3] of var set of 1..10: as1 = [s2, {2}, {3}];\n\
      constraint array_bool_element(1, [true, false], b1);\n\
      constraint array_var_bool_element(2, ab1, b1);\n\
      constraint array_int_element(2, [1, 2, 3], i1);\n\
      constraint array_var_int_element(2, ai1, i1);\n\
      constraint array_set_element(1, [{1}, {2}, {3}], s1);\n\
      constraint array_var_set_element(2, as1, s2);\n\
      solve satisfy;"
  , good :=
      [ "b1 = true;\ni1 = 2;\ns1 = {1};\ns2 = {2};\n----------"
      , "b1 = true;\ni1 = 2;\ns1 = 1..1;\ns2 = 2..2;\n----------" ]
  , bad :=
      [ -- array_bool_element(1, [true,false], b1) forces b1 = true
        "b1 = false;\ni1 = 2;\ns1 = {1};\ns2 = {2};\n----------"
      , -- array_int_element(2, [1,2,3], i1) forces i1 = 2
        "b1 = true;\ni1 = 3;\ns1 = {1};\ns2 = {2};\n----------"
      , -- array_set_element(1, [{1},{2},{3}], s1) forces s1 = {1}
        "b1 = true;\ni1 = 2;\ns1 = {1, 2};\ns2 = {2};\n----------"
      , -- array_var_set_element(2, as1, s2) forces s2 = as1[2] = {2}
        "b1 = true;\ni1 = 2;\ns1 = {1};\ns2 = {1};\n----------"
      ] }

/-! ## int_ranges_as_values — Gecode `test_int_ranges_as_values.cpp`

`set_in_reif` with a *range* set literal `1..2` used as a value. -/

private def intRangesCase : GecodeCase :=
  { name := "gecode int_ranges_as_values"
  , model :=
      "var 1..10: a;\n\
      var bool: b;\n\
      constraint set_in_reif(a, 1..2, b);\n\
      solve satisfy;"
  , good :=
      [ "a = 3;\nb = false;\n----------"
      , "a = 1;\nb = true;\n----------"
      , "a = 2;\nb = true;\n----------" ]
  , bad :=
      [ "a = 3;\nb = true;\n----------"
      , "a = 1;\nb = false;\n----------" ] }

/-! ## empty domain — Gecode `empty_domain_1.cpp`

A reversed range denotes the empty domain (resolution R1): the model
is well-formed but unsatisfiable, so every solution string is
rejected. -/

private def emptyDomainCase : GecodeCase :=
  { name := "gecode empty_domain"
  , model := "var 11..10: x;\nsolve satisfy;"
  , good := []
  , bad :=
      [ "x = 11;\n----------"
      , "x = 5;\n----------" ] }

/-! ## queens4 — Gecode `queens4.cpp` (adapted)

The 4-queens model via difference variables (`int_plus`,
`int_ne`), with scalar variables instead of array indexing (a
Gecode grammar extension).  Gecode's reference solution
`q = [3, 1, 4, 2]` with differences `dq01 = 2, dq02 = -1, dq03 = 1,
dq12 = -3, dq13 = -1, dq23 = 2`. -/

private def queens4Case : GecodeCase :=
  { name := "gecode queens4 (adapted)"
  , model :=
      "var 1..4: q1;\n\
      var 1..4: q2;\n\
      var 1..4: q3;\n\
      var 1..4: q4;\n\
      var int: dq01;\n\
      var int: dq02;\n\
      var int: dq03;\n\
      var int: dq12;\n\
      var int: dq13;\n\
      var int: dq23;\n\
      constraint int_plus(dq01, q2, q1);\n\
      constraint int_plus(dq02, q3, q1);\n\
      constraint int_plus(dq03, q4, q1);\n\
      constraint int_plus(dq12, q3, q2);\n\
      constraint int_plus(dq13, q4, q2);\n\
      constraint int_plus(dq23, q4, q3);\n\
      constraint int_ne(q1, q2);\n\
      constraint int_ne(q1, q3);\n\
      constraint int_ne(q1, q4);\n\
      constraint int_ne(q2, q3);\n\
      constraint int_ne(q2, q4);\n\
      constraint int_ne(q3, q4);\n\
      constraint int_ne(dq01, -1);\n\
      constraint int_ne(dq01, 1);\n\
      constraint int_ne(dq02, -2);\n\
      constraint int_ne(dq02, 2);\n\
      constraint int_ne(dq03, -3);\n\
      constraint int_ne(dq03, 3);\n\
      constraint int_ne(dq12, -1);\n\
      constraint int_ne(dq12, 1);\n\
      constraint int_ne(dq13, -2);\n\
      constraint int_ne(dq13, 2);\n\
      constraint int_ne(dq23, -1);\n\
      constraint int_ne(dq23, 1);\n\
      solve satisfy;"
  , good :=
      [ -- Gecode's reference: q = [3, 1, 4, 2]
        "dq01 = 2;\ndq02 = -1;\ndq03 = 1;\ndq12 = -3;\ndq13 = -1;\ndq23 = 2;\n\
         q1 = 3;\nq2 = 1;\nq3 = 4;\nq4 = 2;\n----------"
      , -- the mirror solution q = [2, 4, 1, 3]
        "dq01 = -2;\ndq02 = 1;\ndq03 = -1;\ndq12 = 3;\ndq13 = 1;\ndq23 = -2;\n\
         q1 = 2;\nq2 = 4;\nq3 = 1;\nq4 = 3;\n----------" ]
  , bad :=
      [ -- q = [3, 1, 4, 2] but dq01 corrupted (int_plus(dq01, q2, q1) violated)
        "dq01 = -2;\ndq02 = -1;\ndq03 = 1;\ndq12 = -3;\ndq13 = -1;\ndq23 = 2;\n\
         q1 = 3;\nq2 = 1;\nq3 = 4;\nq4 = 2;\n----------"
      , -- not a 4-queens solution: diagonal attack (dq01 = 1 forbidden)
        "dq01 = 1;\ndq02 = -1;\ndq03 = 1;\ndq12 = -3;\ndq13 = -1;\ndq23 = 2;\n\
         q1 = 3;\nq2 = 2;\nq3 = 4;\nq4 = 1;\n----------"
      , -- duplicate row: int_ne(q1, q3) violated
        "dq01 = 2;\ndq02 = 0;\ndq03 = 1;\ndq12 = -3;\ndq13 = -1;\ndq23 = 2;\n\
         q1 = 3;\nq2 = 1;\nq3 = 3;\nq4 = 2;\n----------"
      ] }

/-! ## bug232 — Gecode `bug232.cpp`

A zero coefficient linear reification: `int_lin_le_reif([0], [x], 4,
b)` with `x ∈ 0..1`.  `0·x = 0 ≤ 4` always holds, so `b` must be
`true` in every solution. -/

private def bug232Case : GecodeCase :=
  { name := "gecode bug232"
  , model :=
      "var 0..1: INT___1;\n\
      var bool: BOOL___6;\n\
      constraint int_lin_le_reif([0], [INT___1], 4, BOOL___6);\n\
      solve satisfy;"
  , good :=
      [ "INT___1 = 0;\nBOOL___6 = true;\n----------"
      , "INT___1 = 1;\nBOOL___6 = true;\n----------" ]
  , bad :=
      [ "INT___1 = 0;\nBOOL___6 = false;\n----------" ] }

/-! ## sat_cmp_reif — Gecode `sat_cmp_reif.cpp`

Boolean comparison reification: `bool_lt_reif`, `bool_le_reif` on
mixed par/var arguments, with Gecode's reference assignment
`result = [false, true, true, false, true, false, false, false,
true]`. -/

private def satCmpReifCase : GecodeCase :=
  { name := "gecode sat_cmp_reif"
  , model :=
      "var bool: lt_a;\n\
      var bool: lt_b;\n\
      var bool: gt_a;\n\
      var bool: gt_b;\n\
      var bool: le_a;\n\
      var bool: le_b;\n\
      var bool: le_c;\n\
      var bool: ge_a;\n\
      var bool: ge_b;\n\
      array [1..9] of var bool: result = [lt_a, lt_b, gt_a, gt_b, le_a, le_b, le_c, ge_a, ge_b];\n\
      constraint bool_lt_reif(lt_a, lt_b, true);\n\
      constraint bool_lt_reif(gt_b, gt_a, true);\n\
      constraint bool_le_reif(true, le_a, true);\n\
      constraint bool_le_reif(le_b, false, true);\n\
      constraint bool_le_reif(false, true, true);\n\
      constraint bool_le_reif(ge_a, false, true);\n\
      constraint bool_le_reif(true, ge_b, true);\n\
      solve satisfy;"
  , good :=
      [ "result = array1d(1..9, [false, true, true, false, true, false, false, false, true]);\n\
         lt_a = false;\nlt_b = true;\ngt_a = true;\ngt_b = false;\n\
         le_a = true;\nle_b = false;\nle_c = false;\nge_a = false;\nge_b = true;\n----------" ]
  , bad :=
      [ -- bool_lt_reif(lt_a, lt_b, true) forces lt_a < lt_b, i.e. false < true
        "result = array1d(1..9, [false, true, true, false, true, false, false, false, true]);\n\
         lt_a = true;\nlt_b = true;\ngt_a = true;\ngt_b = false;\n\
         le_a = true;\nle_b = false;\nle_c = false;\nge_a = false;\nge_b = true;\n----------"
      , -- bool_le_reif(le_b, false, true) forces le_b = false
        "result = array1d(1..9, [false, true, true, false, true, false, false, false, true]);\n\
         lt_a = false;\nlt_b = true;\ngt_a = true;\ngt_b = false;\n\
         le_a = true;\nle_b = true;\nle_c = false;\nge_a = false;\nge_b = true;\n----------" ] }

/-! ## sat_eq_reif — Gecode `sat_eq_reif.cpp`

`bool_eq_reif` and `bool_xor` with par/var arguments; reference
`result = [false, true, false, true, false]`. -/

private def satEqReifCase : GecodeCase :=
  { name := "gecode sat_eq_reif"
  , model :=
      "var bool: eq_a;\n\
      var bool: eq_b;\n\
      var bool: eq_c;\n\
      var bool: ne_a;\n\
      var bool: ne_b;\n\
      array [1..5] of var bool: result = [eq_a, eq_b, eq_c, ne_a, ne_b];\n\
      constraint bool_eq_reif(false, eq_a, true);\n\
      constraint bool_eq_reif(eq_b, true, true);\n\
      constraint bool_eq_reif(false, true, eq_c);\n\
      constraint bool_xor(false, ne_a, true);\n\
      constraint bool_xor(ne_b, true, true);\n\
      constraint bool_xor(false, true, true);\n\
      solve satisfy;"
  , good :=
      [ "result = array1d(1..5, [false, true, false, true, false]);\n\
         eq_a = false;\neq_b = true;\neq_c = false;\nne_a = true;\nne_b = false;\n----------" ]
  , bad :=
      [ -- bool_eq_reif(false, eq_a, true) forces eq_a = false
        "result = array1d(1..5, [false, true, false, true, false]);\n\
         eq_a = true;\neq_b = true;\neq_c = false;\nne_a = true;\nne_b = false;\n----------"
      , -- bool_xor(ne_b, true, true) forces ne_b = false
        "result = array1d(1..5, [false, true, false, true, false]);\n\
         eq_a = false;\neq_b = true;\neq_c = false;\nne_a = true;\nne_b = true;\n----------" ] }

/-! ## bool_clause — Gecode `bool_clause.cpp`

Clause with singleton/empty literal arrays, on variables and literals. -/

private def boolClauseCase : GecodeCase :=
  { name := "gecode bool_clause"
  , model :=
      "var bool: w;\n\
      var bool: x;\n\
      array [1..3] of var bool: y = [w, x, false];\n\
      array [1..3] of var bool: z = [false, x, false];\n\
      constraint bool_clause([w], []);\n\
      constraint bool_clause([], [x]);\n\
      constraint bool_clause(y, []);\n\
      constraint bool_clause([], z);\n\
      solve satisfy;"
  , good :=
      [ -- Gecode's reference: w = true, x = false, y = [T,F,F], z = [F,F,F]
        "w = true;\nx = false;\n\
         y = array1d(1..3, [true, false, false]);\n\
         z = array1d(1..3, [false, false, false]);\n----------"
        -- w = true, x = true also satisfies (clause([w],[]) needs w; clause([],[x]) needs ¬x? no: negative literal x must be false)
      ]
  , bad :=
      [ -- w = false violates bool_clause([w], [])
        "w = false;\nx = false;\n\
         y = array1d(1..3, [false, false, false]);\n\
         z = array1d(1..3, [false, false, false]);\n----------"
      , -- x = true violates bool_clause([], [x]) (negative literal)
        "w = true;\nx = true;\n\
         y = array1d(1..3, [true, false, false]);\n\
         z = array1d(1..3, [false, true, false]);\n----------" ] }

/-! ## int_set_as_type1 — Gecode `int_set_as_type1.cpp` (adapted)

A set-valued domain `var {1, 3, 5}` (grammar adaptation: the pinned
grammar allows `var {1, 3, 5}`? No — it allows `var {int-literals}`;
yes it does). -/

private def intSetAsTypeCase : GecodeCase :=
  { name := "gecode int_set_as_type"
  , model :=
      "var {1, 3, 5}: x;\n\
      constraint set_in(x, {1, 2, 3, 4, 5});\n\
      solve satisfy;"
  , good :=
      [ "x = 5;\n----------"
      , "x = 1;\n----------"
      , "x = 3;\n----------" ]
  , bad :=
      [ "x = 2;\n----------"
      , "x = 4;\n----------" ] }

/-- All Gecode-derived test cases. -/
private def cases : List GecodeCase :=
  [ intDivCase, intModCase, fznArithCase, fznLogicCase, fznComparisonCase
  , fznSetsCase, fznArraysCase, intRangesCase, emptyDomainCase
  , queens4Case, bug232Case, satCmpReifCase, satEqReifCase
  , boolClauseCase, intSetAsTypeCase ]

/-- Run one case: every good solution must be accepted, every bad one
    rejected (static well-formedness under `fullSig` is checked too). -/
private def runCase (c : GecodeCase) : IO Bool := do
  let m := parseOrPanic c.model
  let mut ok := true
  unless wellFormedB fullSig m do
    IO.eprintln s!"FAIL {c.name}: model not well-formed under fullSig"
    ok := false
  for sol in c.good do
    unless checkSolutionFull m sol do
      IO.eprintln s!"FAIL {c.name}: reference solution rejected:\n{sol}"
      ok := false
  for sol in c.bad do
    if checkSolutionFull m sol then
      IO.eprintln s!"FAIL {c.name}: invalid solution accepted:\n{sol}"
      ok := false
  return ok

def main : IO UInt32 := do
  let mut ok := true
  let mut total := 0
  for c in cases do
    total := total + c.good.length + c.bad.length
    if !(← runCase c) then
      ok := false
  if ok then
    IO.println s!"passed all {total} gecode-derived solution checks ({cases.length} models)"
    return 0
  else
    return 1
