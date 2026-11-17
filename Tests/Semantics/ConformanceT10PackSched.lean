/-
Purpose: SC-04 (T10) ABI-level regression witnesses for the packing,
  scheduling and if-then-else globals in `PackSched.lean`
  (`fzn_bin_packing*`, `fzn_knapsack`, `fzn_diffn[_nonstrict]`,
  `fzn_geost_nonoverlap_k`, `fzn_disjunctive[_strict]`, and the six
  `fzn_if_then_else_*` predicates).
Dependencies: `LeanFzn.Semantics.Globals` (which re-exports `PackSched`).
Why: The expected Boolean results are read off the pinned upstream text
  (`fzn_bin_packing*.mzn`, `fzn_knapsack.mzn`, `fzn_diffn[_nonstrict].mzn`,
  `fzn_geost_nonoverlap_k.mzn`, `fzn_disjunctive[_strict].mzn`,
  `fzn_if_then_else_*.mzn`), independently of the `Prop`/Boolean agreement
  proofs.  Each `_rejected` case is a direct regression for a silent
  `getD`/`zip` default that the old equality gates hid, and each
  `_longer_*` case pins the longer-unused-trailing-array behaviour that the
  raw decompositions permit.
DAG: Semantic families -> these kernel-evaluated regressions; no runtime
  imports them.
-/
import LeanFzn.Semantics.Globals

open LeanFzn LeanFzn.Semantics
open LeanFzn.Semantics.Globals

namespace Tests.Semantics.ConformanceT10PackSched

/-! ## Argument helpers (exact FlatZinc shapes) -/

abbrev vi (x : Int) : Value := .int x
abbrev vints (xs : List Int) : Value := .array (xs.map .int)
abbrev vb (b : Bool) : Value := .bool b
abbrev vbools (bs : List Bool) : Value := .array (bs.map .bool)
abbrev vset (xs : List Int) : Value := .setOfInt (.enumeration xs)
abbrev vsets (xs : List (List Int)) : Value :=
  .array (xs.map fun s => .setOfInt (.enumeration s))

/-! ## `fzn_bin_packing`

Upstream `fzn_bin_packing.mzn` lines 1-8: `bin = []` is the `if
length(bin) > 0` false branch and is true regardless of `weight` and
`capacity`; otherwise `sum(weight)` ranges over all of `weight` while the
inner sum ranges over `index_set(bin)`.
-/

/-- Accepted: the two items on bin 1 have total weight `3 + 2 = 5 ≤ 5`. -/
theorem t10_packsched_bin_packing_accepts :
    fullInterpB ⟨"fzn_bin_packing"⟩
      [vi 5, vints [1, 1], vints [3, 2]] = true := by decide

/-- Line 2: an empty `bin` takes the `if` false branch; `capacity = -3` and
    the nonempty `weight` are not inspected. -/
theorem t10_packsched_bin_packing_empty_bin_accepts :
    fullInterpB ⟨"fzn_bin_packing"⟩
      [vi (-3), vints [], vints [1, 2]] = true := by decide

/-- Nonempty `bin` with a longer `weight`: outside the restricted identity
    domain (`bin.length = weight.length`), rejected. -/
theorem t10_packsched_bin_packing_mismatch_rejected :
    fullInterpB ⟨"fzn_bin_packing"⟩
      [vi 5, vints [1], vints [3, 2]] = false := by decide

/-- The public packing contract requires nonnegative weights; a negative
    weight is rejected. -/
theorem t10_packsched_bin_packing_negative_weight_rejected :
    fullInterpB ⟨"fzn_bin_packing"⟩
      [vi 5, vints [1], vints [-1]] = false := by decide

/-! ## `fzn_bin_packing_capa`

Upstream lines 6-10: the range check reads `weight[i]` over
`index_set(bin)` (`bin.length ≤ weight.length`), and the load loop runs
over all of `index_set(capacity)`.
-/

/-- Accepted: bin 1 load `3 ≤ 5`, bin 2 load `2 ≤ 4`. -/
theorem t10_packsched_bin_packing_capa_accepts :
    fullInterpB ⟨"fzn_bin_packing_capa"⟩
      [vints [5, 4], vints [1, 2], vints [3, 2]] = true := by decide

/-- A longer `weight` is unused beyond `index_set(bin)`; accepted. -/
theorem t10_packsched_bin_packing_capa_longer_weight_accepts :
    fullInterpB ⟨"fzn_bin_packing_capa"⟩
      [vints [5], vints [1], vints [3, 99]] = true := by decide

/-- A `bin` longer than `weight` reads `weight[2]` outside its index set;
    rejected. -/
theorem t10_packsched_bin_packing_capa_mismatch_rejected :
    fullInterpB ⟨"fzn_bin_packing_capa"⟩
      [vints [5], vints [1, 2], vints [3]] = false := by decide

/-- Line 7 lower range: bin value `0` is outside `1..|capacity|`. -/
theorem t10_packsched_bin_packing_capa_bin_zero_rejected :
    fullInterpB ⟨"fzn_bin_packing_capa"⟩
      [vints [5], vints [0], vints [3]] = false := by decide

/-- Line 7 upper range: bin value `|capacity| + 1` is outside
    `1..|capacity|`. -/
theorem t10_packsched_bin_packing_capa_bin_high_rejected :
    fullInterpB ⟨"fzn_bin_packing_capa"⟩
      [vints [5], vints [2], vints [3]] = false := by decide

/-! ## `fzn_bin_packing_load`

Upstream lines 6-10: `sum(load) = sum(weight)` is an explicit conjunct,
`bin[i] ∈ 1..|load|` for `i ∈ index_set(bin)`, and the per-bin equation
reads `weight[i]` only over `index_set(bin)`.
-/

/-- Accepted: `load = [3, 2]` matches the two bin sums, and both totals
    are `5`. -/
theorem t10_packsched_bin_packing_load_accepts :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [3, 2], vints [1, 2], vints [3, 2]] = true := by decide

/-- A longer `weight` with a zero tail keeps `sum(load) = sum(weight)` and
    the bin-1 load; accepted. -/
theorem t10_packsched_bin_packing_load_longer_weight_zero_tail_accepts :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [3], vints [1], vints [3, 0]] = true := by decide

/-- A longer `weight` with a nonzero tail breaks the explicit
    `sum(load) = sum(weight)` conjunct (`3 ≠ 8`); rejected. -/
theorem t10_packsched_bin_packing_load_longer_weight_nonzero_tail_rejected :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [3], vints [1], vints [3, 5]] = false := by decide

/-- A `bin` longer than `weight` is rejected (the per-bin sum would read
    `weight[2]` outside its index set). -/
theorem t10_packsched_bin_packing_load_mismatch_rejected :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [4, 0], vints [1, 2], vints [4]] = false := by decide

/-- Line 8 lower range: bin value `0` is outside `1..|load|`. -/
theorem t10_packsched_bin_packing_load_bin_zero_rejected :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [0], vints [0], vints [0]] = false := by decide

/-- Line 8 upper range: bin value `|load| + 1` is outside `1..|load|`. -/
theorem t10_packsched_bin_packing_load_bin_high_rejected :
    fullInterpB ⟨"fzn_bin_packing_load"⟩
      [vints [0], vints [2], vints [0]] = false := by decide

/-! ## `fzn_knapsack`

Upstream `fzn_knapsack.mzn` lines 8-12: nonnegativity over all of
`index_set(xs)`; the two sums range over all of `index_set(profit)` and
`index_set(weight)`, so only `profit.length ≤ xs.length` and
`weight.length ≤ xs.length` are required.
-/

/-- Accepted: `1*2 + 1*3 = 5` and `1*4 + 1*5 = 9`. -/
theorem t10_packsched_knapsack_accepts :
    fullInterpB ⟨"fzn_knapsack"⟩
      [vints [2, 3], vints [4, 5], vints [1, 1], vi 5, vi 9] = true := by decide

/-- `weight` longer than `xs` reads `xs[2]` outside its index set;
    rejected. -/
theorem t10_packsched_knapsack_weight_mismatch_rejected :
    fullInterpB ⟨"fzn_knapsack"⟩
      [vints [2, 3], vints [4], vints [1], vi 2, vi 4] = false := by decide

/-- `profit` longer than `xs` reads `xs[2]` outside its index set;
    rejected. -/
theorem t10_packsched_knapsack_profit_mismatch_rejected :
    fullInterpB ⟨"fzn_knapsack"⟩
      [vints [2], vints [4, 5], vints [1], vi 2, vi 4] = false := by decide

/-- Trailing `xs` entries are unused by the two sums; only their
    nonnegativity is checked.  Accepted with `xs = [1, 0, 7]`. -/
theorem t10_packsched_knapsack_longer_xs_accepts :
    fullInterpB ⟨"fzn_knapsack"⟩
      [vints [2], vints [4], vints [1, 0, 7], vi 2, vi 4] = true := by decide

/-- `weight` and `profit` need not have equal length when both fit in
    `xs`; accepted with `profit = [4, 5]` and `xs = [1, 0]`. -/
theorem t10_packsched_knapsack_unequal_parameter_lengths_accepts :
    fullInterpB ⟨"fzn_knapsack"⟩
      [vints [2], vints [4, 5], vints [1, 0], vi 2, vi 4] = true := by decide

/-! ## `fzn_diffn` and `fzn_diffn_nonstrict`

Both decompositions loop over `index_set(x)` and index `y`, `dx`, `dy`
only at `i, j ∈ index_set(x)`.  The loop is vacuous for `|x| ≤ 1`, and
for a nonempty pair a true disjunct masks a missing later entry.
-/

/-- Accepted: `x = [0, 5]`, `dx = [2, 2]` puts the first rectangle to the
    left of the second. -/
theorem t10_packsched_diffn_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0, 5], vints [0, 0], vints [2, 2], vints [2, 2]] = true := by decide

/-- A singleton `x` makes the pair loop empty, so no `y`/`dx`/`dy` entry
    is read; accepted with all three parallel arrays empty. -/
theorem t10_packsched_diffn_singleton_empty_parallel_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0], vints [], vints [], vints []] = true := by decide

/-- Singleton `x` with sparse `dx`/`dy` and empty `y`: still vacuous, so
    the missing `y` entry is not read. -/
theorem t10_packsched_diffn_singleton_sparse_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0], vints [], vints [2], vints [2]] = true := by decide

/-- A nonvacuous pair whose first disjunct is true (`0 + 2 ≤ 5`) masks
    the missing `y` entry; accepted. -/
theorem t10_packsched_diffn_masked_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0, 5], vints [], vints [2, 2], vints [2, 2]] = true := by decide

/-- Same masking with a one-element `y`: the missing `y[2]` is masked by
    the first disjunct; accepted. -/
theorem t10_packsched_diffn_masked_short_y_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0, 5], vints [0], vints [2, 2], vints [2, 2]] = true := by decide

/-- No disjunct is true and the missing `y[2]` is not masked: the raw
    call is false. -/
theorem t10_packsched_diffn_mismatch_rejected :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0, 1], vints [0], vints [2, 2], vints [2, 2]] = false := by decide

/-- A longer trailing `y` is unused by the pair loop; accepted (there is
    only one rectangle, so the pair conjunction is vacuous). -/
theorem t10_packsched_diffn_longer_trailing_accepts :
    fullInterpB ⟨"fzn_diffn"⟩
      [vints [0], vints [0, 0], vints [2, 2], vints [2, 2]] = true := by decide

/-- Accepted: touching at `x = 2` is non-overlap for `diffn`. -/
theorem t10_packsched_diffn_nonstrict_accepts :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0, 2], vints [0, 0], vints [2, 2], vints [2, 2]] = true := by decide

/-- A singleton `x` makes the nonstrict pair loop empty; accepted with
    all parallel arrays empty. -/
theorem t10_packsched_diffn_nonstrict_singleton_empty_parallel_accepts :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0], vints [], vints [], vints []] = true := by decide

/-- Singleton `x` with sparse `dx`/`dy` and empty `y`: the loop is
    vacuous; accepted. -/
theorem t10_packsched_diffn_nonstrict_singleton_sparse_accepts :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0], vints [], vints [2], vints [2]] = true := by decide

/-- A nonvacuous pair whose zero-side disjuncts are false but whose
    separation disjunct `0 + 2 ≤ 5` is true; the missing `y` is masked;
    accepted. -/
theorem t10_packsched_diffn_nonstrict_masked_accepts :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0, 5], vints [], vints [2, 2], vints [2, 2]] = true := by decide

/-- No zero side and no true separation: the missing `y[2]` is not
    masked, so the raw call is false. -/
theorem t10_packsched_diffn_nonstrict_mismatch_rejected :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0, 1], vints [0], vints [2, 2], vints [2, 2]] = false := by decide

/-- A longer trailing `y` is unused; accepted. -/
theorem t10_packsched_diffn_nonstrict_longer_trailing_accepts :
    fullInterpB ⟨"fzn_diffn_nonstrict"⟩
      [vints [0], vints [0, 0], vints [2, 2], vints [2, 2]] = true := by decide

/-! ## `fzn_geost_nonoverlap_k`

Upstream lines 7-8: the `exists` runs over `index_set(x1)` and reads
`w1[j]`, `x2[j]`, `w2[j]`.
-/

/-- Accepted: dimension 1 separates the boxes (`0 + 2 ≤ 5`). -/
theorem t10_packsched_geost_nonoverlap_k_accepts :
    fullInterpB ⟨"fzn_geost_nonoverlap_k"⟩
      [vints [0, 5], vints [2, 2], vints [5, 0], vints [2, 2]] = true := by decide

/-- The `exists` is already true at `j = 1` (`0 + 2 ≤ 5`), so the
    missing `w1[2]` is never read; accepted. -/
theorem t10_packsched_geost_nonoverlap_k_masked_early_accepts :
    fullInterpB ⟨"fzn_geost_nonoverlap_k"⟩
      [vints [0, 5], vints [2], vints [5, 0], vints [2, 2]] = true := by decide

/-- The first dimension's disjunction is undefined, but `j = 2`'s second
    disjunct `0 + 2 ≤ 5` is true; `exists` is true and the missing
    `w1[1]` is masked; accepted. -/
theorem t10_packsched_geost_nonoverlap_k_masked_late_accepts :
    fullInterpB ⟨"fzn_geost_nonoverlap_k"⟩
      [vints [0, 5], vints [], vints [5, 0], vints [2, 2]] = true := by decide

/-- No dimension separates and the missing `w1` entries make every
    disjunct undefined: the raw call is false. -/
theorem t10_packsched_geost_nonoverlap_k_mismatch_rejected :
    fullInterpB ⟨"fzn_geost_nonoverlap_k"⟩
      [vints [0, 5], vints [], vints [5, 5], vints [2, 2]] = false := by decide

/-- A longer trailing `w1` is unused; accepted. -/
theorem t10_packsched_geost_nonoverlap_k_longer_trailing_accepts :
    fullInterpB ⟨"fzn_geost_nonoverlap_k"⟩
      [vints [0], vints [2, 2], vints [5, 5], vints [2, 2]] = true := by decide

/-! ## `fzn_disjunctive` and `fzn_disjunctive_strict`

Upstream lines 2-5 / 4-9: all loops run over `index_set(duration)`, and
`start[i]` is the only other access.
-/

/-- Accepted: the first task ends at 2 before the second starts at 5. -/
theorem t10_packsched_disjunctive_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [0, 5], vints [2, 2]] = true := by decide

/-- A longer trailing `start` is unused; accepted. -/
theorem t10_packsched_disjunctive_longer_start_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [0, 5, 9], vints [2, 2]] = true := by decide

/-- A singleton `duration` makes the pair loop empty; only the
    nonnegativity check runs, so `start` is unread.  `duration = [0]` is
    accepted with empty `start`. -/
theorem t10_packsched_disjunctive_singleton_zero_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [], vints [0]] = true := by decide

/-- Same vacuous singleton with a positive duration; accepted. -/
theorem t10_packsched_disjunctive_singleton_positive_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [], vints [5]] = true := by decide

/-- The first task has zero duration, so the first disjunct is true and
    the missing `start` entries are masked; accepted. -/
theorem t10_packsched_disjunctive_zero_masked_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [], vints [0, 5]] = true := by decide

/-- The second task has zero duration; the second disjunct is true and
    the missing `start` entries are masked; accepted. -/
theorem t10_packsched_disjunctive_second_zero_masked_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [], vints [5, 0]] = true := by decide

/-- A zero duration at the second index masks the missing `start[2]`;
    accepted. -/
theorem t10_packsched_disjunctive_short_start_zero_accepts :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [0], vints [2, 0]] = true := by decide

/-- No zero duration and no separation because `start[2]` is missing:
    the raw call is false. -/
theorem t10_packsched_disjunctive_mismatch_rejected :
    fullInterpB ⟨"fzn_disjunctive"⟩
      [vints [0], vints [2, 2]] = false := by decide

/-- Accepted strict non-overlap. -/
theorem t10_packsched_disjunctive_strict_accepts :
    fullInterpB ⟨"fzn_disjunctive_strict"⟩
      [vints [0, 5], vints [2, 2]] = true := by decide

/-- A longer trailing `start` is unused; accepted. -/
theorem t10_packsched_disjunctive_strict_longer_start_accepts :
    fullInterpB ⟨"fzn_disjunctive_strict"⟩
      [vints [0, 5, 7], vints [2, 2]] = true := by decide

/-- A singleton `duration` makes the strict pair loop empty; `start` is
    unread.  `duration = [0]` is accepted with empty `start`. -/
theorem t10_packsched_disjunctive_strict_singleton_zero_accepts :
    fullInterpB ⟨"fzn_disjunctive_strict"⟩
      [vints [], vints [0]] = true := by decide

/-- Same vacuous singleton with a positive duration; accepted. -/
theorem t10_packsched_disjunctive_strict_singleton_positive_accepts :
    fullInterpB ⟨"fzn_disjunctive_strict"⟩
      [vints [], vints [5]] = true := by decide

/-- A `duration` longer than `start` and no zero duration: both
    separation disjuncts read the missing `start[3]`; rejected. -/
theorem t10_packsched_disjunctive_strict_mismatch_rejected :
    fullInterpB ⟨"fzn_disjunctive_strict"⟩
      [vints [0, 5], vints [2, 2, 1]] = false := by decide

/-! ## `fzn_if_then_else_*`

Line 7 of each decomposition accesses `x[i]` only at the first true
`i ∈ index_set(c)`; when all conditions are false no `x` entry is read.
There is therefore no unconditional `c.length ≤ x.length` gate; trailing
`x` entries are unused.
-/

/-- Accepted: the first true condition is index 1 (0-based), selecting
    `x[2] = 20`. -/
theorem t10_packsched_if_then_else_int_accepts :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [false, true], vints [10, 20], vi 20] = true := by decide

/-- A longer trailing `x` is unused; accepted. -/
theorem t10_packsched_if_then_else_int_longer_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [true], vints [10, 99], vi 10] = true := by decide

/-- All conditions false: no `x` entry is read, so `x = []` is accepted. -/
theorem t10_packsched_if_then_else_int_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [false, false], vints [], vi 7] = true := by decide

/-- The first true condition is index 0 and `x[1]` exists; the missing
    `x[2]` is never read, so the call is accepted. -/
theorem t10_packsched_if_then_else_int_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [true, true], vints [10], vi 10] = true := by decide

/-- The first true condition is index 1, which is outside `x`; the read
    `x[2]` is undefined, so the raw call is false. -/
theorem t10_packsched_if_then_else_int_mismatch_rejected :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [false, true], vints [10], vi 10] = false := by decide

/-- The selected branch value is a real equality, not just a shape check. -/
theorem t10_packsched_if_then_else_int_wrong_value_rejected :
    fullInterpB ⟨"fzn_if_then_else_int"⟩
      [vbools [true], vints [10], vi 11] = false := by decide

/-- Accepted: the first true condition selects `x[1] = false`. -/
theorem t10_packsched_if_then_else_bool_accepts :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [true, false], vbools [false, true], vb false] = true := by decide

/-- All conditions false: `x` is unread and may be empty. -/
theorem t10_packsched_if_then_else_bool_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [false], vbools [], vb false] = true := by decide

/-- The first true condition selects `x[1]`; `x[2]` is unread even though
    `c` has length two. -/
theorem t10_packsched_if_then_else_bool_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [true, true], vbools [false], vb false] = true := by decide

/-- The selected index 2 is outside `x`.  For a bool element MiniZinc
    2.10.1 turns the out-of-bounds access into `false` at the
    subexpression level, so the raw body becomes `y = false`: this call is
    accepted, unlike the `int`/`set` rows where the undefined equality is
    false. -/
theorem t10_packsched_if_then_else_bool_missing_selected_defaults_false :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [false, true], vbools [false], vb false] = true := by decide

/-- Same missing selected bool, but `y = true`: the defaulted raw body is
    `y = false`, so this call is false. -/
theorem t10_packsched_if_then_else_bool_missing_selected_wrong_value_rejected :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [false, true], vbools [false], vb true] = false := by decide

/-- The selected branch value is a real equality. -/
theorem t10_packsched_if_then_else_bool_wrong_value_rejected :
    fullInterpB ⟨"fzn_if_then_else_bool"⟩
      [vbools [true], vbools [true], vb false] = false := by decide

/-- Accepted: the first true condition selects the set `{1}`. -/
theorem t10_packsched_if_then_else_set_accepts :
    fullInterpB ⟨"fzn_if_then_else_set"⟩
      [vbools [true], vsets [[1]], vset [1]] = true := by decide

/-- All conditions false: no set is read and `x = []` is accepted. -/
theorem t10_packsched_if_then_else_set_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_set"⟩
      [vbools [false], vsets [], vset [9]] = true := by decide

/-- The first true index is 0, so `x[2]` is not read; accepted. -/
theorem t10_packsched_if_then_else_set_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_set"⟩
      [vbools [true, true], vsets [[1]], vset [1]] = true := by decide

/-- The first true index is 1 and `x[2]` is missing; the raw call is
    false. -/
theorem t10_packsched_if_then_else_set_mismatch_rejected :
    fullInterpB ⟨"fzn_if_then_else_set"⟩
      [vbools [false, true], vsets [[1]], vset [1]] = false := by decide

/-- The selected branch set is a real equality. -/
theorem t10_packsched_if_then_else_set_wrong_value_rejected :
    fullInterpB ⟨"fzn_if_then_else_set"⟩
      [vbools [true], vsets [[1]], vset [2]] = false := by decide

/-- Accepted `_var_int` twin. -/
theorem t10_packsched_if_then_else_var_int_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_int"⟩
      [vbools [false, true], vints [10, 20], vi 20] = true := by decide

/-- `_var_int` with all conditions false and `x = []`; accepted. -/
theorem t10_packsched_if_then_else_var_int_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_int"⟩
      [vbools [false], vints [], vi 7] = true := by decide

/-- `_var_int` with the first true at index 0; `x[2]` is unread and the
    call is accepted. -/
theorem t10_packsched_if_then_else_var_int_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_int"⟩
      [vbools [true, true], vints [10], vi 10] = true := by decide

/-- `_var_int` with the first true index outside `x`; rejected. -/
theorem t10_packsched_if_then_else_var_int_mismatch_rejected :
    fullInterpB ⟨"fzn_if_then_else_var_int"⟩
      [vbools [false, true], vints [10], vi 10] = false := by decide

/-- Accepted `_var_bool` twin. -/
theorem t10_packsched_if_then_else_var_bool_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_bool"⟩
      [vbools [false], vbools [false], vb false] = true := by decide

/-- `_var_bool` with all conditions false and `x = []`; accepted. -/
theorem t10_packsched_if_then_else_var_bool_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_bool"⟩
      [vbools [false], vbools [], vb true] = true := by decide

/-- `_var_bool` with the first true at index 0; accepted. -/
theorem t10_packsched_if_then_else_var_bool_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_bool"⟩
      [vbools [true, true], vbools [true], vb true] = true := by decide

/-- `_var_bool` with the first true index outside `x`: the missing bool
    defaults to `false`, so `y = false` is accepted. -/
theorem t10_packsched_if_then_else_var_bool_missing_selected_defaults_false :
    fullInterpB ⟨"fzn_if_then_else_var_bool"⟩
      [vbools [false, true], vbools [], vb false] = true := by decide

/-- The same missing selected bool with `y = true` is rejected, since the
    defaulted raw body is `y = false`. -/
theorem t10_packsched_if_then_else_var_bool_missing_selected_wrong_value_rejected :
    fullInterpB ⟨"fzn_if_then_else_var_bool"⟩
      [vbools [false, true], vbools [true], vb true] = false := by decide

/-- Accepted `_var_set` twin. -/
theorem t10_packsched_if_then_else_var_set_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_set"⟩
      [vbools [false], vsets [[1]], vset [1]] = true := by decide

/-- `_var_set` with all conditions false and `x = []`; accepted. -/
theorem t10_packsched_if_then_else_var_set_all_false_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_set"⟩
      [vbools [false], vsets [], vset [9]] = true := by decide

/-- `_var_set` with the first true at index 0; `x[2]` is unread. -/
theorem t10_packsched_if_then_else_var_set_first_true_short_x_accepts :
    fullInterpB ⟨"fzn_if_then_else_var_set"⟩
      [vbools [true, true], vsets [[1]], vset [1]] = true := by decide

/-- `_var_set` with the first true index outside `x`; rejected. -/
theorem t10_packsched_if_then_else_var_set_mismatch_rejected :
    fullInterpB ⟨"fzn_if_then_else_var_set"⟩
      [vbools [false, true], vsets [[1]], vset [1]] = false := by decide

/-! ## Decodability gate (`packSchedDecodes`)

The T14 gate is a *decodability* gate: it accepts every argument shape
that the interpreter's decoder can read, and rejects only malformed
value kinds/arities.  The value-dependent and vacuous shape conditions of
`diffn`, `geost_nonoverlap_k`, `disjunctive` and the `if_then_else_*`
predicates stay in the interpreter, so a well-typed short parallel array
is still decodable even when the constraint itself is false.
-/

theorem t10_packsched_decodes_bin_packing_empty_bin :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing"
      [vi (-3), vints [], vints [1, 2]] = true := by decide

theorem t10_packsched_decodes_bin_packing_mismatch :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing"
      [vi 5, vints [1], vints [3, 2]] = false := by decide

theorem t10_packsched_decodes_bin_packing_capa_longer_weight :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing_capa"
      [vints [5], vints [1], vints [3, 99]] = true := by decide

theorem t10_packsched_decodes_bin_packing_capa_mismatch :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing_capa"
      [vints [5], vints [1, 2], vints [3]] = false := by decide

theorem t10_packsched_decodes_bin_packing_load_longer_weight :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing_load"
      [vints [3], vints [1], vints [3, 0]] = true := by decide

theorem t10_packsched_decodes_bin_packing_load_mismatch :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_bin_packing_load"
      [vints [4, 0], vints [1, 2], vints [4]] = false := by decide

theorem t10_packsched_decodes_knapsack_longer_xs :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_knapsack"
      [vints [2], vints [4], vints [1, 0, 7], vi 2, vi 4] = true := by decide

theorem t10_packsched_decodes_knapsack_profit_mismatch :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_knapsack"
      [vints [2], vints [4, 5], vints [1], vi 2, vi 4] = false := by decide

theorem t10_packsched_decodes_diffn_longer_trailing :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_diffn"
      [vints [0], vints [0, 0], vints [2, 2], vints [2, 2]] = true := by decide

/-- A short `y` is a well-typed shape: the interpreter may reject the
    particular values, but the decoder accepts the call. -/
theorem t10_packsched_decodes_diffn_short_y :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_diffn"
      [vints [0, 5], vints [0], vints [2, 2], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_diffn_wrong_arity :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_diffn"
      [vints [0], vints [], vints []] = false := by decide

theorem t10_packsched_decodes_diffn_nonstrict_short_y :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_diffn_nonstrict"
      [vints [0, 1], vints [0], vints [2, 2], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_geost_longer_trailing :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_geost_nonoverlap_k"
      [vints [0], vints [2, 2], vints [5, 5], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_geost_short_w1 :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_geost_nonoverlap_k"
      [vints [0, 5], vints [2], vints [5, 0], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_disjunctive_longer_start :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_disjunctive"
      [vints [0, 5, 9], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_disjunctive_short_start :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_disjunctive"
      [vints [0], vints [2, 2]] = true := by decide

theorem t10_packsched_decodes_disjunctive_wrong_arity :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_disjunctive"
      [vints [0, 5]] = false := by decide

theorem t10_packsched_decodes_disjunctive_strict_short_start :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_disjunctive_strict"
      [vints [0, 5], vints [2, 2, 1]] = true := by decide

theorem t10_packsched_decodes_if_then_else_int_longer_x :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_int"
      [vbools [true], vints [10, 99], vi 10] = true := by decide

/-- The selected `x[2]` is missing, but the argument shape is still
    decodable; the interpreter returns `false` for this value. -/
theorem t10_packsched_decodes_if_then_else_int_short_x :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_int"
      [vbools [false, true], vints [10], vi 10] = true := by decide

theorem t10_packsched_decodes_if_then_else_int_wrong_kind :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_int"
      [vbools [], vi 0, vi 0] = false := by decide

theorem t10_packsched_decodes_if_then_else_bool_short_x :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_bool"
      [vbools [true], vbools [], vb false] = true := by decide

theorem t10_packsched_decodes_if_then_else_set_longer_x :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_set"
      [vbools [true], vsets [[1], [2]], vset [1]] = true := by decide

theorem t10_packsched_decodes_if_then_else_set_wrong_kind :
    LeanFzn.Semantics.Globals.PackSched.packSchedDecodes "fzn_if_then_else_set"
      [vbools [], vints [1], vset []] = false := by decide

end Tests.Semantics.ConformanceT10PackSched
