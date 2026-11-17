/-
Purpose: SC-04 (T10) ABI-level regression witnesses for the counting globals
  (`fzn_distribute`, the `fzn_global_cardinality` family) and the builtin
  linear relations (`int_lin_*`, `bool_lin_*`) whose shape/partiality gates
  were repaired in this task.
Dependencies: `LeanFzn.Semantics.Globals` (which re-exports `StdLib` and
  `Globals.Counting`).
Why: The expected Boolean results are read off the pinned upstream text
  (`fzn_distribute.mzn`, `fzn_global_cardinality*.mzn`, and the MiniZinc
  2.10.1 FlatZinc handbook entries for the linear builtins), independently of
  the `Prop`/Boolean agreement proofs.  The `_rejected` cases for the reified
  linear relations and for `gcc_low_up` used to be accepted by the silent
  `getElem!` default / the `r = false` branch of a missing dot product; they
  are the direct regressions for the code changes.
DAG: Semantic families -> these kernel-evaluated regressions; no runtime
  imports them.
-/
import LeanFzn.Semantics.Globals

open LeanFzn LeanFzn.Semantics
open LeanFzn.Semantics.Globals

namespace Tests.Semantics.ConformanceT10Counting

/-! ## Argument helpers (exact FlatZinc shapes) -/

abbrev vi (x : Int) : Value := .int x
abbrev vints (xs : List Int) : Value := .array (xs.map .int)

/-! ## `fzn_distribute`

Upstream `fzn_distribute.mzn` line 7:
`forall (i in index_set(count)) (count(xs, cover[i], count[i]))`.
The loop is over `index_set(count)`, and `cover[i]` is read on every
iteration.  So a `count` longer than `cover` reads `cover` outside its index
set (undefined, false), while a `cover` longer than `count` is permitted
(the extra entries are never read). -/

/-- The canonical accepted call: `count[i]` counts occurrences of
    `cover[i]` in `xs`. -/
theorem t10_counting_distribute_accepts :
    fullInterpB ⟨"fzn_distribute"⟩
      [vints [2, 1], vints [1, 2], vints [1, 1, 2]] = true := by decide

/-- Upstream loops over `index_set(count)`, so the second `cover` entry
    (`2`) is never read: the longer `cover` is permitted. -/
theorem t10_counting_distribute_longer_cover_accepts :
    fullInterpB ⟨"fzn_distribute"⟩
      [vints [2], vints [1, 2], vints [1, 1, 2]] = true := by decide

/-- A `count` longer than `cover` makes the loop read `cover[2]` outside
    its index set; upstream is undefined there, hence false.  (Regression:
    the old code looped over `cover.length` and read `count[2]! = 0`.) -/
theorem t10_counting_distribute_longer_count_rejected :
    fullInterpB ⟨"fzn_distribute"⟩
      [vints [2, 0], vints [1], vints [1, 1, 2]] = false := by decide

/-- A wrong count in range is rejected (the loop body is a real
    equality, not just a shape check). -/
theorem t10_counting_distribute_wrong_count_rejected :
    fullInterpB ⟨"fzn_distribute"⟩
      [vints [1, 2], vints [1, 2], vints [1, 1, 2]] = false := by decide

/-! ## `fzn_global_cardinality`

Upstream `fzn_global_cardinality.mzn` line 8:
`forall (i in index_set(cover)) (count(xs, cover[i], count[i]))`
conjoined with the implied `length(xs) >= sum(count)` (line 10), where the
sum ranges over all of `count`.  A shorter `count` reads outside its index
set (undefined, false); extra `count` entries are not read by the forall but
are summed. -/

/-- Accepted: each cover value occurs the stated number of times and
    `length(xs) = 3 = sum(count)`. -/
theorem t10_counting_gcc_accepts :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [vints [1, 1, 2], vints [1, 2], vints [2, 1]] = true := by decide

/-- A short `count` is undefined (`count[2]` read while `index_set(cover)` is
    `1..2`) and therefore false. -/
theorem t10_counting_gcc_short_counts_rejected :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [vints [1, 1, 2], vints [1, 2], vints [2]] = false := by decide

/-- Extra `count` entries are not read by the forall; an extra `0` keeps the
    implied sum at `length(xs) = 3`, so the longer `count` is permitted. -/
theorem t10_counting_gcc_longer_counts_accepts :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [vints [1, 1, 2], vints [1, 2], vints [2, 1, 0]] = true := by decide

/-- The implied `length(xs) >= sum(count)` is a real conjunct: with the
    duplicated cover `[1, 1]`, `sum(count) = 4 > length(xs) = 2`. -/
theorem t10_counting_gcc_duplicate_cover_sum_rejected :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [vints [1, 1], vints [1, 1], vints [2, 2]] = false := by decide

/-! ## `fzn_global_cardinality_closed`

Upstream `fzn_global_cardinality_closed.mzn` lines 7-8 conjoin the closed
cover condition `forall (i in index_set(xs)) (xs[i] in cover)` with the
global-cardinality condition.  The shape gate is inherited from
`fzn_global_cardinality`. -/

theorem t10_counting_gcc_closed_accepts :
    fullInterpB ⟨"fzn_global_cardinality_closed"⟩
      [vints [1, 1, 2], vints [1, 2], vints [2, 1]] = true := by decide

/-- `3` is outside `cover = [1, 2]`, which the closed variant forbids. -/
theorem t10_counting_gcc_closed_outside_cover_rejected :
    fullInterpB ⟨"fzn_global_cardinality_closed"⟩
      [vints [1, 3], vints [1, 2], vints [1, 1]] = false := by decide

/-- A short `count` is rejected here too (the closed conjunct must not
    mask the cardinality shape gate). -/
theorem t10_counting_gcc_closed_short_counts_rejected :
    fullInterpB ⟨"fzn_global_cardinality_closed"⟩
      [vints [1, 1], vints [1, 2], vints [2]] = false := by decide

/-! ## `fzn_global_cardinality_low_up`

Upstream `fzn_global_cardinality_low_up.mzn` line 9:
`forall (i in index_set(cover)) (... lower_bound[i] ... upper_bound[i])`.
Both bound arrays are read at every `i` in `index_set(cover)`, so `cover`
must be no longer than `low` and no longer than `up`; extra bound entries
are never read.  The three upstream `if` branches are equivalent to
`low[i] <= count <= up[i]`, because `upper_bound[i] >= length(xs)` makes the
upper inequality automatic and `lower_bound[i] <= 0` makes the lower one
automatic. -/

theorem t10_counting_gcc_low_up_accepts :
    fullInterpB ⟨"fzn_global_cardinality_low_up"⟩
      [vints [1, 1, 2], vints [1, 2], vints [1, 0], vints [2, 1]] = true := by
  decide

/-- A short `low` reads `lower_bound[2]` outside its index set: undefined,
    hence false.  (Regression: the old code used `low[2]! = 0`, which
    accepted this call.) -/
theorem t10_counting_gcc_low_up_short_low_rejected :
    fullInterpB ⟨"fzn_global_cardinality_low_up"⟩
      [vints [1, 1, 2], vints [1, 2], vints [1], vints [2, 1]] = false := by
  decide

/-- A short `up` is symmetrical: undefined, hence false.  (Regression: the
    old code used `up[2]! = 0`, which accepted this call.) -/
theorem t10_counting_gcc_low_up_short_up_rejected :
    fullInterpB ⟨"fzn_global_cardinality_low_up"⟩
      [vints [1, 1], vints [1, 2], vints [1, 0], vints [2]] = false := by
  decide

/-- Extra bound entries are never read, so longer `low`/`up` arrays are
    permitted. -/
theorem t10_counting_gcc_low_up_longer_bounds_accepts :
    fullInterpB ⟨"fzn_global_cardinality_low_up"⟩
      [vints [1, 1, 2], vints [1, 2], vints [1, 0, 9], vints [2, 1, 9]] =
        true := by decide

/-! ## `fzn_global_cardinality_low_up_closed`

Upstream `fzn_global_cardinality_low_up_closed.mzn` lines 7-10 conjoin the
closed cover condition with `global_cardinality_low_up`; the shape gate is
inherited. -/

theorem t10_counting_gcc_low_up_closed_accepts :
    fullInterpB ⟨"fzn_global_cardinality_low_up_closed"⟩
      [vints [1, 1, 2], vints [1, 2], vints [1, 0], vints [2, 1]] = true := by
  decide

theorem t10_counting_gcc_low_up_closed_outside_cover_rejected :
    fullInterpB ⟨"fzn_global_cardinality_low_up_closed"⟩
      [vints [1, 3], vints [1, 2], vints [1, 0], vints [2, 1]] = false := by
  decide

/-- The closed variant rejects a short `low` as well. -/
theorem t10_counting_gcc_low_up_closed_short_low_rejected :
    fullInterpB ⟨"fzn_global_cardinality_low_up_closed"⟩
      [vints [1, 1], vints [1, 2], vints [1], vints [2, 1]] = false := by
  decide

/-! ## Builtin linear relations

The handbook (`lib-flatzinc-int.html#int-lin-eq` and siblings) defines
`int_lin_eq(as, xs, y)` as `y = Σ_i as[i]*xs[i]`, with the reified forms
`b ↔ (...)`; `bool_lin_eq`/`bool_lin_le`
(`lib-flatzinc-bool.html`) are the same with Booleans read as 0/1.  The sum
`Σ_i` needs one common index set for `as` and `xs`, so a length mismatch is
undefined: every form below -- including the `b = false` branch of the
reified ones -- must be false on mismatched lengths. -/

theorem t10_stdlin_int_lin_eq_accepts :
    stdInterpB ⟨"int_lin_eq"⟩
      [vints [1, 2], vints [3, 4], vi 11] = true := by decide

/-- A shorter `xs` is a length mismatch: undefined, hence false. -/
theorem t10_stdlin_int_lin_eq_short_values_rejected :
    stdInterpB ⟨"int_lin_eq"⟩
      [vints [1, 2], vints [3], vi 3] = false := by decide

/-- The mismatch is rejected in the other direction too (a longer `xs`). -/
theorem t10_stdlin_int_lin_eq_long_values_rejected :
    stdInterpB ⟨"int_lin_eq"⟩
      [vints [1, 2], vints [3, 4, 5], vi 11] = false := by decide

theorem t10_stdlin_int_lin_le_accepts :
    stdInterpB ⟨"int_lin_le"⟩
      [vints [1, 2], vints [3, 4], vi 11] = true := by decide

/-- A length mismatch makes the sum undefined, so `int_lin_le` is false
    (not vacuously true through the missing dot product). -/
theorem t10_stdlin_int_lin_le_mismatch_rejected :
    stdInterpB ⟨"int_lin_le"⟩
      [vints [1, 2], vints [3], vi 3] = false := by decide

theorem t10_stdlin_int_lin_ne_accepts :
    stdInterpB ⟨"int_lin_ne"⟩
      [vints [1, 2], vints [3, 4], vi 10] = true := by decide

/-- A length mismatch is not a disequality of defined sums: false. -/
theorem t10_stdlin_int_lin_ne_mismatch_rejected :
    stdInterpB ⟨"int_lin_ne"⟩
      [vints [1, 2], vints [3], vi 3] = false := by decide

theorem t10_stdlin_int_lin_eq_reif_accepts_true :
    stdInterpB ⟨"int_lin_eq_reif"⟩
      [vints [1, 2], vints [3, 4], vi 11, .bool true] = true := by decide

theorem t10_stdlin_int_lin_eq_reif_accepts_false :
    stdInterpB ⟨"int_lin_eq_reif"⟩
      [vints [1, 2], vints [3, 4], vi 10, .bool false] = true := by decide

/-- Regression: with a length mismatch the old interpretation accepted
    `b = false` because `dotProduct = none ≠ some 10`; upstream needs a
    defined dot product, so the call is false. -/
theorem t10_stdlin_int_lin_eq_reif_mismatch_false_rejected :
    stdInterpB ⟨"int_lin_eq_reif"⟩
      [vints [1, 2], vints [3], vi 10, .bool false] = false := by decide

/-- The same regression through the combined dispatcher `fullInterpB`
    (which routes `int_lin_*_reif` to `Evaluation.interpB`). -/
theorem t10_stdlin_int_lin_eq_reif_fullInterpB_mismatch_false_rejected :
    fullInterpB ⟨"int_lin_eq_reif"⟩
      [vints [1, 2], vints [3], vi 10, .bool false] = false := by decide

theorem t10_stdlin_int_lin_le_reif_accepts_false :
    stdInterpB ⟨"int_lin_le_reif"⟩
      [vints [1, 2], vints [3, 4], vi 10, .bool false] = true := by decide

/-- Regression: the `b = false` branch of `int_lin_le_reif` used to accept
    the mismatched call (`dotLe` is `false` on `none`). -/
theorem t10_stdlin_int_lin_le_reif_mismatch_false_rejected :
    stdInterpB ⟨"int_lin_le_reif"⟩
      [vints [1, 2], vints [3], vi 10, .bool false] = false := by decide

/-- The same regression through `fullInterpB`. -/
theorem t10_stdlin_int_lin_le_reif_fullInterpB_mismatch_false_rejected :
    fullInterpB ⟨"int_lin_le_reif"⟩
      [vints [1, 2], vints [3], vi 10, .bool false] = false := by decide

theorem t10_stdlin_int_lin_ne_reif_accepts_false :
    stdInterpB ⟨"int_lin_ne_reif"⟩
      [vints [1, 2], vints [3, 4], vi 11, .bool false] = true := by decide

/-- Regression: the `b = false` branch of `int_lin_ne_reif` used to accept
    the mismatched call (`dotNe` is `false` on `none`). -/
theorem t10_stdlin_int_lin_ne_reif_mismatch_false_rejected :
    stdInterpB ⟨"int_lin_ne_reif"⟩
      [vints [1, 2], vints [3], vi 11, .bool false] = false := by decide

/-- The same regression through `fullInterpB`. -/
theorem t10_stdlin_int_lin_ne_reif_fullInterpB_mismatch_false_rejected :
    fullInterpB ⟨"int_lin_ne_reif"⟩
      [vints [1, 2], vints [3], vi 11, .bool false] = false := by decide

theorem t10_stdlin_bool_lin_eq_accepts :
    stdInterpB ⟨"bool_lin_eq"⟩
      [vints [1, 2], .array [.bool true, .bool false], vi 1] = true := by decide

/-- Booleans read as 0/1: `1*1 + 2*0 = 1`, so the mismatched-length call is
    undefined once `xs` has one fewer entry. -/
theorem t10_stdlin_bool_lin_eq_mismatch_rejected :
    stdInterpB ⟨"bool_lin_eq"⟩
      [vints [1, 2], .array [.bool true], vi 1] = false := by decide

theorem t10_stdlin_bool_lin_le_accepts :
    stdInterpB ⟨"bool_lin_le"⟩
      [vints [1, 2], .array [.bool true, .bool false], vi 1] = true := by decide

theorem t10_stdlin_bool_lin_le_mismatch_rejected :
    stdInterpB ⟨"bool_lin_le"⟩
      [vints [1, 2], .array [.bool true], vi 1] = false := by decide

end Tests.Semantics.ConformanceT10Counting
