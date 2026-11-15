/-
Purpose: Regression witnesses from the pinned FlatZinc semantic-conformance review.
Dependencies: PackSched, Sched2 and SetMath provide the reviewed interpretations.
Why: Expected results come from upstream duration guards and machine-bound lookup,
  independently of the Boolean/Prop agreement proofs.
DAG: Semantic families -> these kernel-evaluated regressions; no runtime imports them.
-/
import LeanFzn.Semantics.Globals
import LeanFzn.Semantics.Globals.PackSched
import LeanFzn.Semantics.Globals.Sched2
import LeanFzn.Semantics.Globals.SetMath

open LeanFzn LeanFzn.Semantics
open LeanFzn.Semantics.Globals

-- Both pinned decompositions explicitly require duration[i] >= 0,
-- even when a singleton has no pairwise-overlap checks to perform.
theorem disjunctive_negative_duration_rejected :
    PackSched.disjunctiveB [0] [-1] = false := by decide

theorem disjunctive_strict_negative_duration_rejected :
    PackSched.disjunctiveStrictB [0] [-1] = false := by decide

-- Non-strict zero-duration tasks may occur inside another task;
-- the strict version forbids that placement.
theorem disjunctive_zero_duration_allowed :
    PackSched.disjunctiveB [0, 1] [3, 0] = true := by decide

theorem disjunctive_strict_zero_duration_inside_rejected :
    PackSched.disjunctiveStrictB [0, 1] [3, 0] = false := by decide

-- Task 1 uses machine 2. Its resource 2 exceeds bound[2] = 1;
-- looking up bound[task=1] = 10 would incorrectly accept it.
theorem cumulatives_uses_machine_bound :
    Sched2.cumulativesB [0] [1] [2] [2] [10, 1] true = false := by decide

-- The inverse asymmetry ensures task-index lookup cannot merely reject more.
theorem cumulatives_accepts_machine_bound :
    Sched2.cumulativesB [0] [1] [2] [2] [1, 10] true = true := by decide

theorem cumulatives_lower_bound_uses_machine :
    Sched2.cumulativesB [0] [1] [2] [2] [1, 10] false = false := by decide

-- Machine ids retain their original lower bound at the native FlatZinc
-- interface: the first entry of bound corresponds to min_machine = 5.
theorem cumulatives_original_machine_offset :
    Sched2.sched2InterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 1], .array [.int 2],
       .array [.int 6], .array [.int 10, .int 1], .bool true, .int 5] = false := by
  decide

theorem cumulatives_empty_tasks_vacuous :
    Sched2.cumulativesB [] [] [] [] [] true = true := by decide

-- The pinned partiality predicate contains only implications guarded by a
-- true selected condition. With none selected, neither Boolean is forced.
theorem partiality_no_true_condition_unrestricted :
    Sched2.itePartialityB [false] [false] true = true := by decide

theorem partiality_selected_false_rejects_true :
    Sched2.itePartialityB [true] [false] true = false := by decide

theorem partiality_first_true_wins :
    Sched2.itePartialityB [true, true] [false, true] false = true := by decide

-- The raw native knapsack predicate has nonnegativity guards in addition
-- to its two dot-product equalities.
theorem knapsack_negative_count_rejected :
    PackSched.knapsackB [0] [0] [-1] 0 0 = false := by decide

theorem knapsack_negative_weight_total_rejected :
    PackSched.knapsackB [-1] [1] [1] (-1) 1 = false := by decide

theorem knapsack_negative_profit_total_rejected :
    PackSched.knapsackB [1] [-1] [1] 1 (-1) = false := by decide

theorem knapsack_nonnegative_solution_accepted :
    PackSched.knapsackB [2] [3] [4] 8 12 = true := by decide

-- Enumeration lists represent sets: duplicates cannot increase intersection
-- cardinality or repeat a coefficient in a sum indexed by a set.
theorem at_most_one_intersection_ignores_enumeration_duplicates :
    SetMath.atMost1B [.enumeration [1], .enumeration [1, 1]] = true := by decide

theorem at_most_one_intersection_rejects_two_distinct_elements :
    SetMath.atMost1B [.enumeration [1, 2], .enumeration [1, 1, 2]] = false := by decide

theorem sum_pred_indices_are_a_set :
    SetMath.sumPredB 1 [.enumeration [1, 1]] [7] 7 = true ∧
    SetMath.sumPredB 1 [.enumeration [1, 2]] [7, 7] 14 = true := by decide

theorem sum_pred_does_not_double_count_an_index :
    SetMath.sumPredB 1 [.enumeration [1, 1]] [7] 14 = false := by decide

-- ## SC-07 (T1): sliding windows with width ≤ 0
-- Upstream `fzn_sliding_sum.mzn` generates `i in lx-1..ux-window_size`
-- with lx = 1 (1-based FlatZinc), so the window set is `0 .. n-w`.
-- w = 0 gives n+1 empty windows (need `low ≤ 0 ≤ up`); w < 0 reads
-- S[0+w] outside its declared index set, which is undefined and makes
-- the constraint false; w > n gives an empty generator (true).

theorem sliding_sum_zero_width_positive_low_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 1, .int 1, .int 0, .array [.int 5]] = false := by decide

theorem sliding_sum_zero_width_zero_interval_accepted :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 0, .int 0, .int 0, .array [.int 5]] = true := by decide

theorem sliding_sum_zero_width_empty_xs_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 1, .int 1, .int 0, .array ([] : List Value)] = false := by decide

theorem sliding_sum_zero_width_empty_xs_wide_interval_accepted :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int (-1), .int 1, .int 0, .array ([] : List Value)] = true := by decide

theorem sliding_sum_negative_width_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 0, .int 5, .int (-1), .array [.int 1, .int 2]] = false := by decide

theorem sliding_sum_width_exceeds_length_accepted :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 0, .int 0, .int 3, .array [.int 1, .int 2]] = true := by decide

theorem sliding_sum_width_two_accepted :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 3, .int 3, .int 2, .array [.int 1, .int 2, .int 1]] = true := by decide

theorem sliding_sum_width_two_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 3, .int 3, .int 2, .array [.int 1, .int 2, .int 2]] = false := by decide

-- `fzn_sliding_among_int` is `sliding_sum` on the 0/1 membership
-- indicator array, so zero width counts 0 elements in the empty window.
theorem sliding_among_int_zero_width_accepted :
    fullInterpB ⟨"fzn_sliding_among_int"⟩
      [.int 0, .int 0, .int 0, .array [.int 7], .setOfInt (.enumeration [7])] = true := by
  decide

theorem sliding_among_bool_zero_width_rejected :
    fullInterpB ⟨"fzn_sliding_among_bool"⟩
      [.int 1, .int 1, .int 0, .array [.bool true], .bool true] = false := by decide

-- ## SC-08 (T2): sum_pred with invalid coefficient indices
-- Upstream `fzn_sum_pred.mzn` builds `sums` for every `j in index_set(sets)`
-- (a par comprehension, evaluated eagerly), so an out-of-range index in
-- ANY set is undefined and makes the constraint false, not just one in
-- the `idx`-th set. The old `coeffsAt` silently filtered such indices.

theorem sum_pred_out_of_range_in_selected_set_rejected :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1, .array [.setOfInt (.enumeration [2])], .array [.int 7], .int 0] =
        false := by decide

theorem sum_pred_out_of_range_in_other_set_rejected :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1,
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [3])],
       .array [.int 7], .int 7] = false := by decide

theorem sum_pred_all_indices_in_range_accepted :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1, .array [.setOfInt (.enumeration [1, 2])],
       .array [.int 3, .int 4], .int 7] = true := by decide

theorem sum_pred_empty_unselected_set_accepted :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 2,
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [])],
       .array [.int 3], .int 0] = true := by decide

-- ## SC-10 (T3): global cardinality with duplicate cover values
-- `fzn_global_cardinality.mzn` conjoins `count(xs, cover[i], count[i])` for
-- every i with the implied `length(xs) >= sum(count)`, where sum ranges over
-- all of `count`. `global_cardinality.mzn` asserts that cover and count have
-- the same index set, so a short `count` is undefined and false.

theorem gcc_duplicate_cover_sum_exceeds_length_rejected :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [.array [.int 1], .array [.int 1, .int 1], .array [.int 1, .int 1]] =
        false := by decide

theorem gcc_duplicate_cover_count_sum_too_large_rejected :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [.array [.int 1, .int 1], .array [.int 1, .int 1],
       .array [.int 2, .int 2]] = false := by decide

theorem gcc_cover_value_outside_cover_accepted :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [.array [.int 1, .int 2], .array [.int 1], .array [.int 1]] = true := by
  decide

theorem gcc_short_count_undefined_rejected :
    fullInterpB ⟨"fzn_global_cardinality"⟩
      [.array [.int 1], .array [.int 1, .int 2], .array [.int 1]] = false := by
  decide

theorem gcc_closed_duplicate_cover_rejected :
    fullInterpB ⟨"fzn_global_cardinality_closed"⟩
      [.array [.int 1], .array [.int 1, .int 1], .array [.int 1, .int 1]] =
        false := by decide

theorem gcc_closed_distinct_cover_accepted :
    fullInterpB ⟨"fzn_global_cardinality_closed"⟩
      [.array [.int 1, .int 2], .array [.int 1, .int 2],
       .array [.int 1, .int 1]] = true := by decide
