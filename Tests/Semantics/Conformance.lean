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

-- ## SC-07 (T1): sliding windows with width ≤ 0, and empty arrays
-- Upstream `fzn_sliding_sum.mzn` sets lx = min(index_set(xs)) and
-- ux = max(index_set(xs)), then generates `i in lx-1..ux-window_size`;
-- with lx = 1 (1-based FlatZinc) the window set is `0 .. n-w`.
-- w = 0 gives n+1 empty windows (need `low ≤ 0 ≤ up`); w < 0 reads
-- S[0+w] outside its declared index set, which is undefined and makes
-- the constraint false; w > n gives an empty generator (true).
-- An empty xs makes `min(index_set(xs))` undefined, so the constraint is
-- false for every width (MiniZinc 2.10.1 with Gecode `-G std` and with
-- Chuffed: "minimum of empty set is undefined", UNSATISFIABLE).

theorem sliding_sum_zero_width_positive_low_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 1, .int 1, .int 0, .array [.int 5]] = false := by decide

theorem sliding_sum_zero_width_zero_interval_accepted :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 0, .int 0, .int 0, .array [.int 5]] = true := by decide

theorem sliding_sum_zero_width_empty_xs_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 1, .int 1, .int 0, .array ([] : List Value)] = false := by decide

-- Empty xs: undefined `min(index_set(xs))`, false even though
-- `low ≤ 0 ≤ up` (an earlier version of this witness expected `true`).
theorem sliding_sum_zero_width_empty_xs_wide_interval_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int (-1), .int 1, .int 0, .array ([] : List Value)] = false := by decide

-- Empty xs with w > n = 0: still undefined, so false (not an empty
-- generator).
theorem sliding_sum_wide_window_empty_xs_rejected :
    fullInterpB ⟨"fzn_sliding_sum"⟩
      [.int 0, .int 0, .int 3, .array ([] : List Value)] = false := by decide

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

theorem sliding_among_bool_zero_width_accepted :
    fullInterpB ⟨"fzn_sliding_among_bool"⟩
      [.int 0, .int 0, .int 0, .array [.bool true], .bool true] = true := by decide

-- `fzn_sliding_among_*` call `sliding_sum` on the indicator array, which
-- is empty when xs is, so the empty-array case is false here too.
theorem sliding_among_int_empty_xs_rejected :
    fullInterpB ⟨"fzn_sliding_among_int"⟩
      [.int 0, .int 0, .int 3, .array ([] : List Value),
        .setOfInt (.enumeration [7])] = false := by decide

theorem sliding_among_bool_empty_xs_rejected :
    fullInterpB ⟨"fzn_sliding_among_bool"⟩
      [.int 0, .int 0, .int 0, .array ([] : List Value), .bool true] = false := by decide

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

-- ## SC-09 (T4): cumulative empty input and nonnegative contract
-- `cumulative.mzn` asserts equal index sets and `duration[i] >= 0`,
-- `resource[i] >= 0`; a violating solution is inadmissible and false.
-- `fzn_cumulative.mzn` selects Tasks by `ub(...) > 0`, which on values is
-- `duration[i] > 0 ∧ resource[i] > 0`. With no selected task the result is
-- `length(start) = 0 ∨ capacity ≥ 0`.

theorem cumulative_empty_negative_capacity_accepted :
    fullInterpB ⟨"fzn_cumulative"⟩
      [.array ([] : List Value), .array ([] : List Value),
       .array ([] : List Value), .int (-1)] = true := by decide

theorem cumulative_no_selected_task_nonempty_rejected :
    fullInterpB ⟨"fzn_cumulative"⟩
      [.array [.int 0], .array [.int 0], .array [.int 3], .int (-1)] = false := by
  decide

theorem cumulative_negative_resource_rejected :
    fullInterpB ⟨"fzn_cumulative"⟩
      [.array [.int 0], .array [.int 2], .array [.int (-1)], .int 5] = false := by
  decide

theorem cumulative_overlap_exceeds_capacity_rejected :
    fullInterpB ⟨"fzn_cumulative"⟩
      [.array [.int 0, .int 0], .array [.int 2, .int 2],
       .array [.int 2, .int 2], .int 3] = false := by decide

theorem cumulative_disjoint_tasks_accepted :
    fullInterpB ⟨"fzn_cumulative"⟩
      [.array [.int 0, .int 2], .array [.int 2, .int 2],
       .array [.int 2, .int 2], .int 2] = true := by decide

-- ## SC-02 (T5): automaton final states, state bounds, NFA union
-- `share/minizinc/std/fzn_regular.mzn` declares `F` as `set of int`
-- (line 11), puts `a : array [m..n] of var 1..Q` (line 22), and has the
-- empty-word branch `q0 in F` only (lines 13-14).  `d` is a flat
-- row-major Q×S matrix under the T9 ABI contract, so a wrong length is
-- rejected by the decoder.  The same reading holds for
-- `fzn_regular_nfa.mzn` and `fzn_cost_regular.mzn`.

-- `a[1]=1`, `a[2]=d[1,1]=2`, and `2∈F={2}`: accepted.
theorem regular_set_final_accepted :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [2])] = true := by decide

-- Same run, but the final state 2 is not in `F={1}`.
theorem regular_set_final_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [1])] = false := by decide

-- `a[2]=d[1,1]=2` is outside `var 1..Q` with `Q=1`; being in `F` does
-- not help because no admissible `a[2]` exists.
theorem regular_transition_above_state_bound_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 2],
       .int 1, .setOfInt (.enumeration [2])] = false := by decide

-- `a[1]=q0=0` is outside `var 1..Q` for a nonempty word.
theorem regular_start_above_state_bound_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 2, .int 1, .array [.int 1, .int 1],
       .int 0, .setOfInt (.enumeration [0])] = false := by decide

-- `xs[1]=2` is outside `1..S` with `S=1` (line 27).
theorem regular_symbol_above_alphabet_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 2], .int 2, .int 1, .array [.int 1, .int 1],
       .int 1, .setOfInt (.enumeration [1])] = false := by decide

-- Empty word: only `q0 in F` (line 14); no state bound is imposed even
-- though `q0=5` is outside `1..Q` with `Q=0`.
theorem regular_empty_word_start_in_final_accepted :
    fullInterpB ⟨"fzn_regular"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [5])] = true := by decide

-- Empty word with `q0=5 ∉ F={4}`.
theorem regular_empty_word_start_not_in_final_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [4])] = false := by decide

-- `F` is a set parameter (line 11); an indicator array does not decode.
theorem regular_indicator_array_final_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 1],
       .int 1, .array [.int 0, .int 1]] = false := by decide

-- The T9 ABI contract requires `length d = Q*S`; here `1 ≠ 2*1`.
theorem regular_d_length_mismatch_rejected :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1], .int 2, .int 1, .array [.int 1],
       .int 1, .setOfInt (.enumeration [1])] = false := by decide

-- Two-step run 1 -> 2 -> 1 with final state 1 in `F={1}`.
theorem regular_two_step_accepted :
    fullInterpB ⟨"fzn_regular"⟩
      [.array [.int 1, .int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [1])] = true := by decide

-- `fzn_regular_nfa.mzn` line 24 existentially quantifies `a[i+1]` in
-- `d[a[i], xs[i]]`; after `xs=[1,1]` the reachable set is
-- `{1,2} ∪ {1} = {1,2}`, which meets `F={2}`.  Keeping only the last
-- state's successors drops the accepting path.
theorem regular_nfa_frontier_union_accepted :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1, .int 1], .int 2, .int 2,
       .array [.setOfInt (.enumeration [1, 2]),
         .setOfInt (.enumeration []),
         .setOfInt (.enumeration [1]),
         .setOfInt (.enumeration [])],
       .int 1, .setOfInt (.enumeration [2])] = true := by decide

-- The only successor of 1 on symbol 1 is 1, which is not in `F={2}`.
theorem regular_nfa_final_state_not_in_final_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1], .int 2, .int 1,
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [])],
       .int 1, .setOfInt (.enumeration [2])] = false := by decide

-- Empty word: only `q0 in F` (line 10), no state bound.
theorem regular_nfa_empty_word_start_in_final_accepted :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [5])] = true := by decide

theorem regular_nfa_empty_word_start_not_in_final_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [4])] = false := by decide

-- `F` is `set of int` (line 7); an indicator array does not decode.
theorem regular_nfa_indicator_array_final_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1], .int 1, .int 1,
       .array [.setOfInt (.enumeration [1])],
       .int 1, .array [.int 0, .int 1]] = false := by decide

-- `length d = 1 ≠ Q*S = 2` (T9 ABI contract).
theorem regular_nfa_d_length_mismatch_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1], .int 2, .int 1,
       .array [.setOfInt (.enumeration [1])],
       .int 1, .setOfInt (.enumeration [1])] = false := by decide

-- `a[1]=q0=3` is outside `var 1..Q` for a nonempty word.
theorem regular_nfa_start_above_state_bound_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1], .int 2, .int 1,
       .array [.setOfInt (.enumeration [3]), .setOfInt (.enumeration [3])],
       .int 3, .setOfInt (.enumeration [3])] = false := by decide

-- The successor set contains 2, but `a[2] : var 1..Q = 1..1`, so the
-- run ends in state 1, which is not in `F={2}`.
theorem regular_nfa_out_of_range_successor_rejected :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1], .int 1, .int 1,
       .array [.setOfInt (.enumeration [1, 2])],
       .int 1, .setOfInt (.enumeration [2])] = false := by decide

-- `fzn_cost_regular.mzn`: run 1 -> 1, `cc=[0,7]`, total 7, `1∈F={1}`.
theorem cost_regular_set_final_accepted :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 1],
       .int 1, .setOfInt (.enumeration [1]), .array [.int 7],
       .int 7] = true := by decide

-- Same run, but the accumulated cost is 7, not 6.
theorem cost_regular_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 1],
       .int 1, .setOfInt (.enumeration [1]), .array [.int 7],
       .int 6] = false := by decide

-- Two-step run 1 -> 2 -> 1 with costs 3 and 4: `cc=[0,3,7]`.
theorem cost_regular_two_step_sum_accepted :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1, .int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [1]), .array [.int 3, .int 4],
       .int 7] = true := by decide

theorem cost_regular_two_step_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1, .int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [1]), .array [.int 3, .int 4],
       .int 6] = false := by decide

-- Empty word: `total_cost = 0 ∧ q0 ∈ F` (line 12), with no state bound.
theorem cost_regular_empty_word_zero_total_accepted :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [5]), .array ([] : List Value),
       .int 0] = true := by decide

theorem cost_regular_empty_word_nonzero_total_rejected :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array ([] : List Value), .int 0, .int 0, .array ([] : List Value),
       .int 5, .setOfInt (.enumeration [5]), .array ([] : List Value),
       .int 1] = false := by decide

-- `F` is `set of int` (line 7); an indicator array does not decode.
theorem cost_regular_indicator_array_final_rejected :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 1],
       .int 1, .array [.int 0, .int 1], .array [.int 7],
       .int 7] = false := by decide

-- `length cost = 0 ≠ Q*S = 1` (T9 ABI contract; `d` also has length 1).
theorem cost_regular_cost_length_mismatch_rejected :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1], .int 1, .int 1, .array [.int 1],
       .int 1, .setOfInt (.enumeration [1]), .array ([] : List Value),
       .int 0] = false := by decide

-- Independent probe X1 (attempted empty-word state-bound trap): `Q=1` is
-- non-vacuous, but `fzn_regular.mzn` lines 13-14 create no state array on
-- the empty word, so `q0=5 ∈ F={5}` is accepted without `q0 ≤ Q`.
theorem regular_empty_word_nonvacuous_state_bound_accepted :
    fullInterpB ⟨"fzn_regular"⟩
      [.array ([] : List Value), .int 1, .int 1, .array [.int 0],
       .int 5, .setOfInt (.enumeration [5])] = true := by decide

-- Independent probe X2: acceptance comes only from the *first* frontier
-- element.  `d[1,1]={2,3}` (line 24) gives frontier `{2,3}` after step 1;
-- then `d[2,1]={1}` and `d[3,1]={}`, so the union is `{1}`, meeting
-- `F={1}`.  A last-state-only fold would keep `succ(3)={}` and say false.
theorem regular_nfa_union_first_frontier_accepted :
    fullInterpB ⟨"fzn_regular_nfa"⟩
      [.array [.int 1, .int 1], .int 3, .int 1,
       .array [.setOfInt (.enumeration [2, 3]),
         .setOfInt (.enumeration [1]),
         .setOfInt (.enumeration [])],
       .int 1, .setOfInt (.enumeration [1])] = true := by decide

-- Independent probe X3: `cost` entries are plain ints (line 8), so a
-- negative transition cost is allowed.  Run 1 -> 2 -> 1 costs -3 + 5 = 2
-- (`cc=[0,-3,2]`, lines 24 and 30); final state 1 is in `F={1}`.
theorem cost_regular_negative_cost_accepted :
    fullInterpB ⟨"fzn_cost_regular"⟩
      [.array [.int 1, .int 1], .int 2, .int 1, .array [.int 2, .int 1],
       .int 1, .setOfInt (.enumeration [1]), .array [.int (-3), .int 5],
       .int 2] = true := by decide

-- ## SC-06 (T6): deterministic and cost MDD

-- M1: the reviewer's SC-06 counterexample.  P4 puts exactly one of nodes 2
-- and 3 on level 2; P2 forces the incoming edge from node 1, and P1 then
-- forces *both* matching level-1 edges, activating both nodes and
-- contradicting P4.  Upstream conjunction false (the old walk search true).
theorem mdd_reviewer_counterexample_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 1], .int 3, .array [.int 1, .int 2, .int 2],
       .int 4, .array [.int 1, .int 1, .int 2, .int 3],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1]),
         .setOfInt (.enumeration [1]), .setOfInt (.enumeration [1])],
       .array [.int 2, .int 3, .int 0, .int 0]] = false := by decide

-- M2: genuinely deterministic diagram 1 -( {1} )-> 2 -( {2} )-> 0 for
-- xs=[1,2].  All conjuncts hold.
theorem mdd_deterministic_accepts :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 2, .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = true := by decide

-- M3: the same diagram with xs=[2,1]; edge 1 labels {1}, so T4 forbids it
-- while T1 at the root requires an active outgoing edge.
theorem mdd_deterministic_wrong_word_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 2, .int 1], .int 2, .array [.int 1, .int 2],
       .int 2, .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- M4: the upstream relation does not require levels to increase along an
-- edge.  bn[0]=bn[1]=bn[2]=true and all three edges active satisfy every
-- conjunct, although the edge 1->1 self-loop makes an increasing-level
-- walk search fail.
theorem mdd_self_loop_back_edge_accepted :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 3, .array [.int 1, .int 2, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]),
         .setOfInt (.enumeration [2])],
       .array [.int 1, .int 2, .int 0]] = true := by decide

-- M5: N=0 is outside the upstream index sets (`bn[1]`, `ln[1]`).
theorem mdd_node_count_zero_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1], .int 0, .array ([] : List Value), .int 0,
       .array ([] : List Value), .array ([] : List Value),
       .array ([] : List Value)] = false := by decide

-- M6: E=0 passes the range gate but T1 needs an edge out of node 1.
theorem mdd_edge_count_zero_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 0,
       .array ([] : List Value), .array ([] : List Value),
       .array ([] : List Value)] = false := by decide

-- M7: from[1]=2 is outside `bn`'s index set 0..N=1.
theorem mdd_from_out_of_range_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 1,
       .array [.int 2], .array [.setOfInt (.enumeration [1])],
       .array [.int 0]] = false := by decide

-- M8: to[1]=2 is outside `bn`'s index set 0..N=1.
theorem mdd_to_out_of_range_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 1,
       .array [.int 1], .array [.setOfInt (.enumeration [1])],
       .array [.int 2]] = false := by decide

-- M9: level[from[1]]=2 is outside `xs`'s index set 1..L=1.
theorem mdd_level_from_out_of_range_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 2], .int 1,
       .array [.int 1], .array [.setOfInt (.enumeration [1])],
       .array [.int 0]] = false := by decide

-- C1: canonical cost MDD for xs=[1,2], costs 4 and 7, ln[1]=11.
theorem cost_mdd_canonical_accepts :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 2, .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4, .int 7], .array [.int 2, .int 0],
       .int 11] = true := by decide

-- C2: same model, total_cost = 10 ≠ ln[1] = 11.
theorem cost_mdd_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 2, .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4, .int 7], .array [.int 2, .int 0],
       .int 10] = false := by decide

-- C3: two matching edges at the only level, costs 5 and 3; upstream ln
-- takes the minimum, so total_cost = 3.
theorem cost_mdd_multiple_matching_min_accepted :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 2,
       .array [.int 1, .int 1],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1])],
       .array [.int 5, .int 3], .array [.int 0, .int 0],
       .int 3] = true := by decide

-- C4: the same model cannot use total_cost = 5 (the non-minimal edge).
theorem cost_mdd_multiple_matching_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 2,
       .array [.int 1, .int 1],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [1])],
       .array [.int 5, .int 3], .array [.int 0, .int 0],
       .int 5] = false := by decide

-- C5: the inactive edge costs -100, but the upstream penalty
-- `(not be[e]) * (maxcost + 1 - cost[e])` makes its ln term 6, so the
-- active edge cost 5 wins: total_cost = 5.
theorem cost_mdd_negative_inactive_edge_accepted :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 2,
       .array [.int 1, .int 1],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 5, .int (-100)], .array [.int 0, .int 0],
       .int 5] = true := by decide

-- C6: dropping the penalty would accept total_cost = 6; upstream rejects.
theorem cost_mdd_negative_inactive_edge_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 2,
       .array [.int 1, .int 1],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 5, .int (-100)], .array [.int 0, .int 0],
       .int 6] = false := by decide

-- C7: N=3 with L=2 is outside the canonical cost gate (even though the
-- call would otherwise have a terminal edge from node 2).
theorem cost_mdd_noncanonical_shape_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 3, .array [.int 1, .int 2, .int 3],
       .int 2, .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4, .int 7], .array [.int 2, .int 0],
       .int 11] = false := by decide

-- C8: length(cost)=0 < E=1; cost[e] is undefined.
theorem cost_mdd_short_cost_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 1,
       .array [.int 1], .array [.setOfInt (.enumeration [1])],
       .array ([] : List Value), .array [.int 0],
       .int 0] = false := by decide

-- C9: COST = sum(minlevelcost)..L*(maxcost+1) is empty for a single
-- edge of cost -2: -2..-1, so ln[0]=0 is outside COST.
theorem cost_mdd_empty_cost_interval_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1], .int 1, .array [.int 1], .int 1,
       .array [.int 1], .array [.setOfInt (.enumeration [1])],
       .array [.int (-2)], .array [.int 0],
       .int (-2)] = false := by decide

-- C10: canonical shape with level-1 max -5 and a non-matching level-2
-- edge of cost 10.  Upstream gives ln[2] = min(10, maxcost+1 = 6) = 6
-- and ln[1] = 6 + (-5) = 1, so total_cost = 1 is true.  The closed form
-- `Σ_l m_l` would instead give 5; the implementation evaluates the
-- upstream recursion literally.
theorem cost_mdd_negative_level_recursion_accepted :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 3, .array [.int 1, .int 2, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]),
         .setOfInt (.enumeration [9])],
       .array [.int (-5), .int 10, .int 10], .array [.int 2, .int 0, .int 0],
       .int 1] = true := by decide

-- C11: the same model with total_cost = 5 (the closed-form value) is
-- rejected by upstream; this is the regression that caught the closed
-- form.
theorem cost_mdd_negative_level_recursion_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2],
       .int 3, .array [.int 1, .int 2, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2]),
         .setOfInt (.enumeration [9])],
       .array [.int (-5), .int 10, .int 10], .array [.int 2, .int 0, .int 0],
       .int 5] = false := by decide

/-! ## T14: decodability in static well-formedness

These witnesses use the real AST constructors.  The bad-matrix model is
statically type-correct (`SigEnv.matches` is true); only the new
decodability conjunct rejects it. -/

namespace Tests.Semantics.ConformanceT14

abbrev xsId : Ident := ⟨"xs"⟩
abbrev dId : Ident := ⟨"d"⟩
abbrev fId : Ident := ⟨"F"⟩

/-- The reviewed `fzn_regular` call `regular(xs, 2, 2, d, 1, F)`. -/
abbrev regularConstraint : ConstraintItem where
  name := ⟨"fzn_regular"⟩
  args := [.basic (.ident xsId), .basic (.lit (.int 2)),
    .basic (.lit (.int 2)), .basic (.ident dId),
    .basic (.lit (.int 1)), .basic (.ident fId)]
  anns := []

/-- The same call with `F` omitted: a wrong-arity invocation. -/
abbrev badArityConstraint : ConstraintItem where
  name := ⟨"fzn_regular"⟩
  args := [.basic (.ident xsId), .basic (.lit (.int 2)),
    .basic (.lit (.int 2)), .basic (.ident dId),
    .basic (.lit (.int 1))]
  anns := []

/-- `Q = S = 2` and `d` has the required `Q*S = 4` entries. -/
abbrev goodRegularModel : Model where
  predicates := []
  parameters :=
    [ .array ⟨2⟩ .int xsId [.int 0, .int 1],
      .array ⟨4⟩ .int dId [.int 1, .int 2, .int 1, .int 1],
      .basic .setOfInt fId (.set (.intSet [1])) ]
  variables := []
  constraints := [regularConstraint]
  solve := .satisfy []

/-- `Q = S = 2` but `d` has only three entries: statically checked, not
    decodable. -/
abbrev badMatrixModel : Model where
  predicates := []
  parameters :=
    [ .array ⟨2⟩ .int xsId [.int 0, .int 1],
      .array ⟨3⟩ .int dId [.int 1, .int 2, .int 1],
      .basic .setOfInt fId (.set (.intSet [1])) ]
  variables := []
  constraints := [regularConstraint]
  solve := .satisfy []

/-- The correct call is accepted by the extended static checker. -/
theorem t14_regular_good_wf :
    wellFormedB fullSig goodRegularModel = true := by decide

/-- The wrong-arity call is rejected by the static checker. -/
theorem t14_regular_bad_arity_wf_false :
    wellFormedB fullSig
      { goodRegularModel with constraints := [badArityConstraint] } = false := by
  decide

/-- The length-mismatched matrix is rejected by the static checker. -/
theorem t14_regular_bad_matrix_wf_false :
    wellFormedB fullSig badMatrixModel = false := by decide

/-- The bad matrix passes the old type check but fails the new decoder:
    this isolates the new decodability conjunct. -/
theorem t14_regular_bad_matrix_checked_but_undecodable :
    SigEnv.matches fullSig badMatrixModel.staticEnv regularConstraint.name
        regularConstraint.args = true ∧
      fullDecodes "fzn_regular"
        [.array .int (.var (.par .int)), .basic (.par .int),
         .basic (.par .int), .array .int (.par .int),
         .basic (.par .int), .basic (.par .setOfInt)]
        [.array [.int 0, .int 1], .int 2, .int 2,
         .array [.int 1, .int 2, .int 1], .int 1,
         .setOfInt (.enumeration [1])] = false := by
  decide

/-- `WellFormed.constraint_decodes` is exercised on the good `fzn_regular`
    model, with the shape store as the parameter-honest store. -/
theorem t14_constraint_decodes_regular :
    ∃ params ∈ goodRegularModel.sigEnv fullSig regularConstraint.name,
      Forall2 (Expr.checkArg goodRegularModel.staticEnv)
        regularConstraint.args params ∧
      fullDecodes regularConstraint.name.name params
        [.array [.int 0, .int 1], .int 2, .int 2,
         .array [.int 1, .int 2, .int 1, .int 1], .int 1,
         .setOfInt (.enumeration [1])] = true := by
  have hwf : WellFormed fullSig goodRegularModel :=
    (wellFormedB_iff fullSig goodRegularModel).mp (by decide)
  have hc : regularConstraint ∈ goodRegularModel.constraints := by simp
  have hpar : ParamHonest goodRegularModel goodRegularModel.shapeStore := by
    intro d hd
    exact shapeStore_param (List.nodup_append.mp hwf.valueNamesUnique).1 hd
  have hdom : VarsRespect goodRegularModel goodRegularModel.shapeStore := by
    intro d hd
    simp at hd
  have heval : regularConstraint.args.mapM
      (Expr.eval goodRegularModel.shapeStore) =
      some [.array [.int 0, .int 1], .int 2, .int 2,
        .array [.int 1, .int 2, .int 1, .int 1], .int 1,
        .setOfInt (.enumeration [1])] := by rfl
  exact hwf.constraint_decodes hc hpar hdom heval

end Tests.Semantics.ConformanceT14

/-! ## T8: graph and circuit witnesses (SC-01/SC-05) -/

/-
Purpose: ABI-level regression witnesses for the graph/circuit globals rewritten
  in T8 from the pinned MiniZinc 2.10.1 `fzn_*` decompositions.
Dependencies: `LeanFzn.Semantics.Globals.Graph` (via `Globals`).
Why: The expected Boolean results are read off the pinned decompositions and
  the wrapper assertions they call internally, independently of the
  `Prop`/Boolean agreement proofs in `Graph.lean`.
DAG: Semantic families -> these kernel-evaluated regressions; no runtime
  imports them.
-/

open LeanFzn LeanFzn.Semantics
open LeanFzn.Semantics.Globals

-- The two rejected enum path/branch witnesses reduce a deep `decide`
-- search; the default elaborator recursion depth is too small for them.
set_option maxRecDepth 10000

namespace Tests.Semantics.ConformanceGraph

/-! ## Argument helpers (exact FlatZinc shapes) -/

abbrev vi (x : Int) : Value := .int x
abbrev vb (x : Bool) : Value := .bool x
abbrev vints (xs : List Int) : Value := .array (xs.map .int)
abbrev vboolss (xs : List Bool) : Value := .array (xs.map .bool)

/-! ## `fzn_circuit` / `fzn_subcircuit` (behavior preserved) -/

theorem graph_circuit_two_cycle_accepted :
    Graph.graphInterpB ⟨"fzn_circuit"⟩ [vints [2, 1]] = true := by decide

theorem graph_circuit_fixed_point_rejected :
    Graph.graphInterpB ⟨"fzn_circuit"⟩ [vints [1, 2]] = false := by decide

theorem graph_subcircuit_all_fixed_accepted :
    Graph.graphInterpB ⟨"fzn_subcircuit"⟩ [vints [1, 2, 3]] = true := by decide

theorem graph_subcircuit_cycle_with_fixed_point_accepted :
    Graph.graphInterpB ⟨"fzn_subcircuit"⟩ [vints [2, 1, 3]] = true := by decide

theorem graph_subcircuit_two_cycles_rejected :
    Graph.graphInterpB ⟨"fzn_subcircuit"⟩ [vints [2, 1, 4, 3]] = false := by decide

theorem graph_subcircuit_duplicate_value_rejected :
    Graph.graphInterpB ⟨"fzn_subcircuit"⟩ [vints [2, 2]] = false := by decide

/-! ## `fzn_subgraph` (no wrapper gate) -/

-- The mandatory isolated-selected-node witness, `_int` form:
-- `N=2,E=1,from=[1],to=[2],ns=[true,false],es=[false]`.
theorem graph_subgraph_int_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vi 2, vi 1, vints [1], vints [2], vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_subgraph_int_unselected_endpoint_rejected :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vi 2, vi 1, vints [1], vints [2], vboolss [true, false],
       vboolss [true]] = false := by decide

-- `fzn_subgraph_int` loops over `1..E`; a longer `es` is never read.
theorem graph_subgraph_int_unread_extra_edge_accepted :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vi 2, vi 1, vints [1], vints [2], vboolss [true, false],
       vboolss [false, true]] = true := by decide

theorem graph_subgraph_enum_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vints [1], vints [2], vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_subgraph_enum_unselected_endpoint_rejected :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vints [1], vints [2], vboolss [true, false],
       vboolss [true]] = false := by decide

-- `es` is shorter than `from`: the loop over `index_set(from)` reads past
-- `es`, which is undefined and therefore false.
theorem graph_subgraph_enum_short_es_rejected :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vints [1, 2], vints [2, 2], vboolss [true, true],
       vboolss [false]] = false := by decide

-- `fzn_subgraph_enum` has no `dom_array(to)` assertion, so an out-of-range
-- `to` is harmless when the edge is unselected.  The corresponding
-- `fzn_reachable_enum` call is rejected (see
-- `graph_reachable_enum_out_of_range_to_rejected`).
theorem graph_subgraph_enum_out_of_range_to_unselected_accepted :
    Graph.graphInterpB ⟨"fzn_subgraph"⟩
      [vints [1], vints [4], vboolss [true, false, false],
       vboolss [false]] = true := by decide

/-! ## `fzn_dag` (enum-only) -/

-- The mandatory DAG counterexample: the selected edge `1 -> 2` with both
-- nodes unselected forces `dist[1] + 1 <= dist[2]`, i.e. `1 <= 0`.
theorem graph_dag_unselected_endpoints_rejected :
    Graph.graphInterpB ⟨"fzn_dag"⟩
      [vints [1], vints [2], vboolss [false, false],
       vboolss [true]] = false := by decide

theorem graph_dag_selected_edge_accepted :
    Graph.graphInterpB ⟨"fzn_dag"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [true]] = true := by decide

theorem graph_dag_unselected_edge_accepted :
    Graph.graphInterpB ⟨"fzn_dag"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [false]] = true := by decide

-- `fzn_dag` exists only in the enum overload; the 6-argument int form must
-- not decode.
theorem graph_dag_int_form_rejected :
    Graph.graphInterpB ⟨"fzn_dag"⟩
      [vi 2, vi 1, vints [1], vints [2], vboolss [true, true],
       vboolss [true]] = false := by decide

/-! ## `fzn_connected` / `fzn_dconnected` (enum-only) -/

theorem graph_connected_edge_accepted :
    Graph.graphInterpB ⟨"fzn_connected"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [true]] = true := by decide

theorem graph_connected_no_edge_rejected :
    Graph.graphInterpB ⟨"fzn_connected"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [false]] = false := by decide

theorem graph_dconnected_edge_accepted :
    Graph.graphInterpB ⟨"fzn_dconnected"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [true]] = true := by decide

theorem graph_dconnected_no_edge_rejected :
    Graph.graphInterpB ⟨"fzn_dconnected"⟩
      [vints [1], vints [2], vboolss [true, true],
       vboolss [false]] = false := by decide

/-! ## `fzn_reachable` (both overloads) -/

-- `N=2,E=1,from=[1],to=[2],root=1,ns=[true,false],es=[false]` is satisfiable:
-- the non-selected node has `parent = 0` and `dist = 0`.
theorem graph_reachable_int_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1, vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_reachable_int_unreachable_selected_node_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1, vboolss [true, true],
       vboolss [false]] = false := by decide

-- Undirected `1 - 2 - 3` rooted at 1.
theorem graph_reachable_int_undirected_path_accepted :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

-- Same graph, but edge `2 -> 3` is selected while node 3 is not: the
-- `subgraph` call inside `fzn_dreachable` rejects it.
theorem graph_reachable_int_undirected_cut_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, false], vboolss [true, true]] = false := by decide

-- `des = es ++ es` must have length `1..2*E`; a longer `es` is rejected by
-- the let-binding (MiniZinc: "Index set mismatch").
theorem graph_reachable_int_extra_es_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, true], vboolss [true, true, false]] = false := by
  decide

theorem graph_reachable_enum_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vints [1], vints [2], vi 1, vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_reachable_enum_unreachable_selected_node_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vints [1], vints [2], vi 1, vboolss [true, true],
       vboolss [false]] = false := by decide

-- The pre-T8 ABI put `root` last; the new enum ABI puts it before `ns,es`.
theorem graph_reachable_enum_old_abi_root_last_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vints [1], vints [2], vboolss [true, false], vboolss [false],
       vi 1] = false := by decide

-- `fzn_reachable_enum` copies `ns` and `from`/`to` into arrays indexed by
-- `NODE = index_set(ns)`, so an endpoint outside `1..length(ns)` is
-- rejected even when the edge is unselected.
theorem graph_reachable_enum_out_of_range_to_rejected :
    Graph.graphInterpB ⟨"fzn_reachable"⟩
      [vints [1], vints [4], vi 1, vboolss [true, false, false],
       vboolss [false]] = false := by decide

/-! ## `fzn_dreachable` (both overloads) -/

theorem graph_dreachable_int_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1, vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_dreachable_int_unreachable_selected_node_rejected :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1, vboolss [true, true],
       vboolss [false]] = false := by decide

-- `to[e] = 0` is not a node: the selected edge forces `ns[0]`, which is
-- undefined and therefore false.
theorem graph_dreachable_int_terminal_zero_rejected :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vi 2, vi 1, vints [1], vints [0], vi 1, vboolss [true, false],
       vboolss [true]] = false := by decide

theorem graph_dreachable_enum_isolated_selected_node_accepted :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vints [1], vints [2], vi 1, vboolss [true, false],
       vboolss [false]] = true := by decide

theorem graph_dreachable_enum_unreachable_selected_node_rejected :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vints [1], vints [2], vi 1, vboolss [true, true],
       vboolss [false]] = false := by decide

-- `fzn_dreachable_enum` calls `subgraph(from,to,ns,es)`, whose enum assert
-- requires `index_set(from) = index_set(to)`.
theorem graph_dreachable_enum_from_to_length_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vints [1], vints [2, 3], vi 1, vboolss [true, false, false],
       vboolss [false]] = false := by decide

theorem graph_dreachable_enum_out_of_range_to_rejected :
    Graph.graphInterpB ⟨"fzn_dreachable"⟩
      [vints [1], vints [4], vi 1, vboolss [true, false, false],
       vboolss [false]] = false := by decide

/-! ## `fzn_tree` (both overloads) -/

theorem graph_tree_int_path_accepted :
    Graph.graphInterpB ⟨"fzn_tree"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

-- Two selected edges on two nodes: `sum es = 2 != sum ns - 1 = 1`.
theorem graph_tree_int_cycle_rejected :
    Graph.graphInterpB ⟨"fzn_tree"⟩
      [vi 2, vi 2, vints [1, 2], vints [2, 1], vi 1,
       vboolss [true, true], vboolss [true, true]] = false := by decide

-- `fzn_tree_int` reads `es` only over `1..E`, so an extra entry is unused.
theorem graph_tree_int_unread_extra_edge_accepted :
    Graph.graphInterpB ⟨"fzn_tree"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, true], vboolss [true, true, false]] = true := by
  decide

theorem graph_tree_enum_path_accepted :
    Graph.graphInterpB ⟨"fzn_tree"⟩
      [vints [1, 2], vints [2, 3], vi 1, vboolss [true, true, true],
       vboolss [true, true]] = true := by decide

theorem graph_tree_enum_missing_node_selected_edge_rejected :
    Graph.graphInterpB ⟨"fzn_tree"⟩
      [vints [1, 2], vints [2, 3], vi 1, vboolss [true, true, false],
       vboolss [true, true]] = false := by decide

/-! ## `fzn_dtree` (both overloads) -/

theorem graph_dtree_int_path_accepted :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

theorem graph_dtree_int_cycle_rejected :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vi 2, vi 2, vints [1, 2], vints [2, 1], vi 1,
       vboolss [true, true], vboolss [true, true]] = false := by decide

-- `fzn_dtree_int` permits non-selected nodes (`parent = 0`, `dist = 0`);
-- MiniZinc reports this model satisfiable.
theorem graph_dtree_int_nonselected_node_accepted :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1, vboolss [true, false],
       vboolss [false]] = true := by decide

-- The internal `subgraph(N,E,from,to,ns,es)` call asserts
-- `index_set(ns) = 1..N`, so a longer `ns` is rejected.
theorem graph_dtree_int_extra_node_rejected :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vi 2, vi 1, vints [1], vints [2], vi 1,
       vboolss [true, false, true], vboolss [false]] = false := by decide

theorem graph_dtree_enum_path_accepted :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vints [1, 2], vints [2, 3], vi 1, vboolss [true, true, true],
       vboolss [true, true]] = true := by decide

-- `index_set(from) = index_set(to)` fails: 1 != 2.
theorem graph_dtree_enum_length_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_dtree"⟩
      [vints [1], vints [2, 3], vi 1, vboolss [true, false, false],
       vboolss [false]] = false := by decide

/-! ## `fzn_path` (both overloads) -/

theorem graph_path_int_path_accepted :
    Graph.graphInterpB ⟨"fzn_path"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

-- A selected two-cycle: `sum es = 2 != sum ns - 1 = 1`, so the first
-- directed tree is impossible.
theorem graph_path_int_cycle_rejected :
    Graph.graphInterpB ⟨"fzn_path"⟩
      [vi 2, vi 2, vints [1, 2], vints [2, 1], vi 1, vi 2,
       vboolss [true, true], vboolss [true, true]] = false := by decide

theorem graph_path_enum_path_accepted :
    Graph.graphInterpB ⟨"fzn_path"⟩
      [vints [1, 2], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

-- Branch at node 2: the reversed tree rooted at the sink has no incoming
-- edge for node 4.
theorem graph_path_enum_branch_rejected :
    Graph.graphInterpB ⟨"fzn_path"⟩
      [vints [1, 2, 2], vints [2, 3, 4], vi 1, vi 3,
       vboolss [true, true, true, true],
       vboolss [true, true, true]] = false := by decide

-- The pre-T8 ABI put `ns,es` before `source,sink`.
theorem graph_path_enum_old_abi_order_rejected :
    Graph.graphInterpB ⟨"fzn_path"⟩
      [vints [1, 2], vints [2, 3], vboolss [true, true, true],
       vboolss [true, true], vi 1, vi 3] = false := by decide

/-! ## `fzn_dpath` (both overloads) -/

theorem graph_dpath_int_path_accepted :
    Graph.graphInterpB ⟨"fzn_dpath"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

-- Edges `1 -> 2` and `3 -> 2` converge; the tree rooted at `source = 1`
-- has no incoming edge for node 3.
theorem graph_dpath_int_converging_edges_rejected :
    Graph.graphInterpB ⟨"fzn_dpath"⟩
      [vi 3, vi 2, vints [1, 3], vints [2, 2], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = false := by decide

theorem graph_dpath_enum_path_accepted :
    Graph.graphInterpB ⟨"fzn_dpath"⟩
      [vints [1, 2], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = true := by decide

theorem graph_dpath_enum_converging_edges_rejected :
    Graph.graphInterpB ⟨"fzn_dpath"⟩
      [vints [1, 3], vints [2, 2], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true]] = false := by decide

/-! ## `fzn_bounded_path` (both overloads) -/

theorem graph_bounded_path_int_weight_accepted :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 5] = true := by
  decide

theorem graph_bounded_path_int_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 4] = false := by
  decide

-- `w` is read at every `e in 1..E`; a short `w` makes the sum undefined.
theorem graph_bounded_path_int_short_weight_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vints [2], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 2] = false := by
  decide

theorem graph_bounded_path_enum_weight_accepted :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 5] = true := by
  decide

theorem graph_bounded_path_enum_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 4] = false := by
  decide

theorem graph_bounded_path_enum_short_weight_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_path"⟩
      [vints [1, 2], vints [2, 3], vints [2], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 2] = false := by
  decide

/-! ## `fzn_bounded_dpath` (both overloads) -/

theorem graph_bounded_dpath_int_weight_accepted :
    Graph.graphInterpB ⟨"fzn_bounded_dpath"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 5] = true := by
  decide

theorem graph_bounded_dpath_int_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_dpath"⟩
      [vi 3, vi 2, vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 4] = false := by
  decide

theorem graph_bounded_dpath_enum_weight_accepted :
    Graph.graphInterpB ⟨"fzn_bounded_dpath"⟩
      [vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 5] = true := by
  decide

theorem graph_bounded_dpath_enum_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_bounded_dpath"⟩
      [vints [1, 2], vints [2, 3], vints [2, 3], vi 1, vi 3,
       vboolss [true, true, true], vboolss [true, true], vi 4] = false := by
  decide

/-! ## `fzn_steiner` (int-only) -/

-- `N=2,E=0` with only node 1 selected: the existential root is node 1.
theorem graph_steiner_isolated_selected_root_accepted :
    Graph.graphInterpB ⟨"fzn_steiner"⟩
      [vi 2, vi 0, vints [], vints [], vints [], vboolss [true, false],
       vboolss [], vi 0] = true := by decide

theorem graph_steiner_tree_accepted :
    Graph.graphInterpB ⟨"fzn_steiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5],
       vboolss [true, true], vboolss [true], vi 5] = true := by decide

theorem graph_steiner_unselected_node_selected_edge_rejected :
    Graph.graphInterpB ⟨"fzn_steiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5],
       vboolss [true, false], vboolss [true], vi 5] = false := by decide

theorem graph_steiner_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_steiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5],
       vboolss [true, true], vboolss [true], vi 4] = false := by decide

/-! ## `fzn_dsteiner` (int-only) -/

theorem graph_dsteiner_tree_accepted :
    Graph.graphInterpB ⟨"fzn_dsteiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 1,
       vboolss [true, true], vboolss [true], vi 5] = true := by decide

theorem graph_dsteiner_wrong_root_rejected :
    Graph.graphInterpB ⟨"fzn_dsteiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 2,
       vboolss [true, true], vboolss [true], vi 5] = false := by decide

theorem graph_dsteiner_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_dsteiner"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 1,
       vboolss [true, true], vboolss [true], vi 4] = false := by decide

/-! ## `fzn_wst` (int-only, no `ns` argument) -/

theorem graph_wst_tree_accepted :
    Graph.graphInterpB ⟨"fzn_wst"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vboolss [true],
       vi 5] = true := by decide

theorem graph_wst_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_wst"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vboolss [true],
       vi 4] = false := by decide

-- The internal node array is `[true | n in 1..N]`; with `N = 3` a single
-- selected edge cannot span all three nodes.
theorem graph_wst_node_count_change_rejected :
    Graph.graphInterpB ⟨"fzn_wst"⟩
      [vi 3, vi 1, vints [1], vints [2], vints [5], vboolss [true],
       vi 5] = false := by decide

/-! ## `fzn_dwst` (int-only, no `ns` argument) -/

theorem graph_dwst_tree_accepted :
    Graph.graphInterpB ⟨"fzn_dwst"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 1,
       vboolss [true], vi 5] = true := by decide

theorem graph_dwst_wrong_root_rejected :
    Graph.graphInterpB ⟨"fzn_dwst"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 2,
       vboolss [true], vi 5] = false := by decide

theorem graph_dwst_weight_mismatch_rejected :
    Graph.graphInterpB ⟨"fzn_dwst"⟩
      [vi 2, vi 1, vints [1], vints [2], vints [5], vi 1,
       vboolss [true], vi 4] = false := by decide

end Tests.Semantics.ConformanceGraph

/-! ## T9: flat matrix witnesses (SC-03) -/

/-
Purpose: ABI-level (flat FlatZinc argument) witnesses for SC-03 (T9).
Dependencies: LeanFzn.Semantics.Globals supplies `fullInterpB` and the families.
Why: The values are hand-derived from the pinned upstream decompositions in
  tmp/sc-repairs/T9/derivation.md, independently of the Boolean/Prop proofs.
DAG: Semantic families -> these kernel-evaluated regressions; no runtime imports them.

Every theorem goes through the ABI decoder (`fullInterpB`), so it witnesses
both the flat argument shape and the resulting relation.  See
`tmp/sc-repairs/T9/derivation.md` for the per-witness upstream derivation.
-/

open LeanFzn LeanFzn.Semantics
open LeanFzn.Semantics.Globals

/-! ## SC-03 (T9): `fzn_table_int` — flat row-major tuples -/

-- T1: xs = (1,2) is row 1 of the 2x2 table [[1,2],[3,4]]
-- (`fzn_table_int.mzn` lines 8-15: exists a tuple row i with tuples[i,j]=xs[j]).
theorem matrix_table_int_row1_true :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1, .int 2], .array [.int 1, .int 2, .int 3, .int 4]] = true := by
  decide

-- T2: xs = (3,4) is row 2 of the same table.
theorem matrix_table_int_row2_true :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 3, .int 4], .array [.int 1, .int 2, .int 3, .int 4]] = true := by
  decide

-- T3: no row equals (1,3).
theorem matrix_table_int_row_mismatch_false :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1, .int 3], .array [.int 1, .int 2, .int 3, .int 4]] = false := by
  decide

-- T4: SC-03 fix. Empty xs makes `min/max(index_set(xs))` undefined
-- (`fzn_table_int.mzn` lines 8-9), so the constraint is false, not vacuously true.
theorem matrix_table_int_empty_xs_false :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [], .array [.int 1, .int 2]] = false := by
  decide

-- T5: empty xs with an empty table: both `min(index_set(xs))` and
-- `min(index_set_1of2(tuples))` are undefined, hence false.
theorem matrix_table_int_empty_xs_empty_tuples_false :
    fullInterpB ⟨"fzn_table_int"⟩ [.array [], .array []] = false := by
  decide

-- T6: 3 flat tuple entries cannot be a matrix with 2 columns (3 % 2 != 0);
-- upstream has no such 2-D argument, so the call is rejected.
theorem matrix_table_int_nondivisible_false :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1, .int 2], .array [.int 1, .int 2, .int 3]] = false := by
  decide

-- T7: a divisible but differently shaped flat array still decodes: with
-- columns = length(xs) = 4, the table is one 4-row; xs is that row.
theorem matrix_table_int_divisible_wrong_shape_true :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1, .int 2, .int 3, .int 4],
       .array [.int 1, .int 2, .int 3, .int 4, .int 5, .int 6, .int 7, .int 8]] = true := by
  decide

-- T8: the same 4-column decoding rejects a tuple that matches no row.
theorem matrix_table_int_divisible_wrong_shape_false :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1, .int 2, .int 3, .int 5],
       .array [.int 1, .int 2, .int 3, .int 4, .int 5, .int 6, .int 7, .int 8]] = false := by
  decide

-- T9: an empty tuple matrix has no row index `lt = min(index_set_1of2(tuples))`.
theorem matrix_table_int_empty_tuples_false :
    fullInterpB ⟨"fzn_table_int"⟩ [.array [.int 1], .array []] = false := by
  decide

-- T10: a one-column table: xs=(1) is row 1 of [[1],[2],[3]].
theorem matrix_table_int_one_column_true :
    fullInterpB ⟨"fzn_table_int"⟩
      [.array [.int 1], .array [.int 1, .int 2, .int 3]] = true := by
  decide

/-! ## SC-03 (T9): `fzn_geost` — flat k-column matrices

Upstream (`fzn_geost.mzn`): `DIMS = 1..k`, `OBJECTS = index_set(kind)`;
for every pair of objects and every pair of rectangles of the fixed kinds,
some axis is separated (`fzn_geost_nonoverlap_k.mzn` line 8).  Flat ABI:
`C = k`; `xs[o,j]` is `xsFlat[o*k + j]`, `rect[r,j]` is
`rectFlat[(r-1)*k + (j-1)]`. -/

-- G1: two 2x2 objects at (0,0) and (2,0), size 1x1: separated on x.
theorem matrix_geost_2x2_true :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1]] = true := by
  decide

-- G2: both objects at (0,0): no separating axis.
theorem matrix_geost_overlap_false :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.int 1, .int 1]] = false := by
  decide

-- G3: length(xs) = 3 < length(kind)*k = 4: object 2's row x[2,2] is undefined.
theorem matrix_geost_xs_length_false :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2],
       .array [.int 1, .int 1]] = false := by
  decide

-- G4: kind = 2 but shape has one set; shape[2] is undefined.
theorem matrix_geost_kind_out_of_range_false :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0], .array [.int 2]] = false := by
  decide

-- G5: rectangle id 3 is the only shape entry but rect_size has 2 rows
-- (4 / k = 2); rect_size[3,j] is undefined.
theorem matrix_geost_shape_rect_out_of_range_false :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [3])],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.int 1, .int 1]] = false := by
  decide

-- G6: k = 0 gives DIMS = 1..0 = empty; with a single object there is no
-- o1 < o2 pair, so the universal relation is vacuously true and nothing is read.
theorem matrix_geost_k0_single_true :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 0, .array [], .array [], .array [.setOfInt (.enumeration [1])],
       .array [], .array [.int 1]] = true := by
  decide

-- G7: extra rows/entries beyond the used prefix are unread upstream
-- (OBJECTS = index_set(kind) = {1,2}, shape only contains rectangle 1) and accepted.
theorem matrix_geost_extra_entries_true :
    fullInterpB ⟨"fzn_geost"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1, .int 9, .int 9],
       .array [.int 0, .int 0, .int 0, .int 0, .int 7, .int 7],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0, .int 99, .int 99],
       .array [.int 1, .int 1]] = true := by
  decide

/-! ## SC-03 (T9): `fzn_geost_bb` — geost plus bounding box -/

-- G8: object 2's right edge x+offset+size = 3 equals upper_bound[1] exactly.
theorem matrix_geost_bb_boundary_true :
    fullInterpB ⟨"fzn_geost_bb"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1],
       .array [.int 0, .int 0], .array [.int 3, .int 1]] = true := by
  decide

-- G9: upper_bound[1] = 2 < 3, so the right edge violates the box.
theorem matrix_geost_bb_upper_false :
    fullInterpB ⟨"fzn_geost_bb"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1],
       .array [.int 0, .int 0], .array [.int 2, .int 1]] = false := by
  decide

-- G10: lower_bound has only 1 entry but DIMS = 1..2; lower_bound[2] is undefined.
theorem matrix_geost_bb_lower_length_false :
    fullInterpB ⟨"fzn_geost_bb"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1],
       .array [.int 0], .array [.int 3, .int 1]] = false := by
  decide

/-! ## SC-03 (T9): `fzn_geost_smallest_bb` — geost_bb plus tight bounds -/

-- G11: both bounds are touched in both dimensions (0 and 3 on x, 0 and 1 on y).
theorem matrix_geost_smallest_bb_true :
    fullInterpB ⟨"fzn_geost_smallest_bb"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1],
       .array [.int 0, .int 0], .array [.int 3, .int 1]] = true := by
  decide

-- G12: geost_bb holds (3 <= 4) but no right edge equals upper_bound[1] = 4.
theorem matrix_geost_smallest_bb_upper_touch_false :
    fullInterpB ⟨"fzn_geost_smallest_bb"⟩
      [.int 2, .array [.int 1, .int 1, .int 1, .int 1],
       .array [.int 0, .int 0, .int 0, .int 0],
       .array [.setOfInt (.enumeration [1])],
       .array [.int 0, .int 0, .int 2, .int 0],
       .array [.int 1, .int 1],
       .array [.int 0, .int 0], .array [.int 4, .int 1]] = false := by
  decide

/-! ## SC-03 (T9): unsupported rows — a flat FlatZinc call is rejected

The seven rows below have no recoverable matrix width in the FlatZinc
argument list (`index_set_2of2` is not an argument).  The registered
FlatZinc signature is 1-D; the decoder requires the *nested* project
extension, so a flat call decodes to `none` and evaluates to `false`.
Missing dimension parameter is recorded in `tmp/sc-repairs/T9/report.md`. -/

-- U1: `fzn_lex_chain_less_int` needs the column count `index_set_2of2`.
theorem matrix_lex_chain_less_int_flat_false :
    fullInterpB ⟨"fzn_lex_chain_less_int"⟩ [.array [.int 1, .int 2]] = false := by
  decide

-- U2: same missing column count.
theorem matrix_lex_chain_lesseq_int_flat_false :
    fullInterpB ⟨"fzn_lex_chain_lesseq_int"⟩ [.array [.int 1, .int 2]] = false := by
  decide

-- U3: `fzn_lex2` needs the width both for `xs` and for its transpose.
theorem matrix_lex2_flat_false :
    fullInterpB ⟨"fzn_lex2"⟩ [.array [.int 1, .int 2, .int 3, .int 4]] = false := by
  decide

-- U4: `fzn_strict_lex2` has the same missing width.
theorem matrix_strict_lex2_flat_false :
    fullInterpB ⟨"fzn_strict_lex2"⟩
      [.array [.int 1, .int 2, .int 3, .int 4]] = false := by
  decide

-- U5: `_kind` is a row-sum mode, not a matrix width; the width is still missing.
theorem matrix_lex_chain_lesseq_orbitope_flat_false :
    fullInterpB ⟨"fzn_lex_chain_lesseq_orbitope"⟩
      [.array [.int 1, .int 0, .int 0, .int 1], .int 1] = false := by
  decide

-- U6: `fzn_diffn_k` needs `index_set_2of2(box_posn)`; the flat call is rejected.
theorem matrix_diffn_k_flat_false :
    fullInterpB ⟨"fzn_diffn_k"⟩
      [.array [.int 0, .int 5, .int 0, .int 0],
       .array [.int 1, .int 1, .int 1, .int 1]] = false := by
  decide

-- U7: `fzn_diffn_nonstrict_k` has the same missing dimension count.
theorem matrix_diffn_nonstrict_k_flat_false :
    fullInterpB ⟨"fzn_diffn_nonstrict_k"⟩
      [.array [.int 0, .int 5, .int 0, .int 0],
       .array [.int 1, .int 1, .int 1, .int 1]] = false := by
  decide

-- U10-U16: the empty flat array is ambiguous between 0 x n and n x 0
-- native matrices, so every unsupported decoder must reject it instead of
-- treating it as an empty nested matrix.  These are the verifier's
-- counterexamples for the T9 empty-flat gap.
theorem matrix_lex_chain_less_int_empty_flat_false :
    fullInterpB ⟨"fzn_lex_chain_less_int"⟩ [.array []] = false := by
  decide

theorem matrix_lex_chain_lesseq_int_empty_flat_false :
    fullInterpB ⟨"fzn_lex_chain_lesseq_int"⟩ [.array []] = false := by
  decide

theorem matrix_lex2_empty_flat_false :
    fullInterpB ⟨"fzn_lex2"⟩ [.array []] = false := by
  decide

theorem matrix_strict_lex2_empty_flat_false :
    fullInterpB ⟨"fzn_strict_lex2"⟩ [.array []] = false := by
  decide

theorem matrix_lex_chain_lesseq_orbitope_empty_flat_false :
    fullInterpB ⟨"fzn_lex_chain_lesseq_orbitope"⟩ [.array [], .int 1] = false := by
  decide

theorem matrix_diffn_k_empty_flat_false :
    fullInterpB ⟨"fzn_diffn_k"⟩ [.array [], .array []] = false := by
  decide

theorem matrix_diffn_nonstrict_k_empty_flat_false :
    fullInterpB ⟨"fzn_diffn_nonstrict_k"⟩ [.array [], .array []] = false := by
  decide

/-! ## Retained nested-extension regressions (not FlatZinc ABI)

These are not claims about real `.fzn` input: they pin the project-internal
nested value representation that the greater-direction extensions use. -/

-- U8: columns (1,2) and (3,4): 1 < 3, so the strict column chain holds.
theorem matrix_lex_chain_less_int_nested_extension_true :
    fullInterpB ⟨"fzn_lex_chain_less_int"⟩
      [.array [.array [.int 1, .int 2], .array [.int 3, .int 4]]] = true := by
  decide

-- U9: nested boxes at (0,0) and (5,0), sizes 1x1: separated on x.
theorem matrix_diffn_k_nested_extension_true :
    fullInterpB ⟨"fzn_diffn_k"⟩
      [.array [.array [.int 0, .int 0], .array [.int 5, .int 0]],
       .array [.array [.int 1, .int 1], .array [.int 1, .int 1]]] = true := by
  decide

/-! ## T10-W1: counting and linear witnesses (SC-04) -/

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

/-! ## T10-W2: set, channeling and sorting witnesses (SC-04) -/

/-
Purpose: T10/SC-04 regression witnesses for the SetMath, Channeling and
  LexSort global constraints: shape (parallel-array length) and
  argument-derived index/partiality gates.
Dependencies: LeanFzn.Semantics.Globals (fullInterpB dispatches to the
  SetMath, Channeling and LexSort family interpretations).
Why: Expected values are read off the pinned raw `fzn_*` decompositions in
  tmp/semantic-conformance/upstream/share/minizinc/std, independently of the
  Boolean/Prop agreement proofs.
DAG: semantic families -> these kernel-evaluated regressions; no runtime
  module imports them.
-/

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals

/-! ## `fzn_sum_set`

Upstream `fzn_sum_set.mzn:6` is
`total == sum (j in index_set(values)) ((values[j] in selected) * weights[j])`:
it reads `weights[j]` for every position of `values`, and `selected` is a set
of *values* (never used as an index). A shorter `weights` is therefore
undefined and must be false; extra positions of a longer `weights` are never
read and are accepted. -/

-- Positive: selected = {3, 7}, so the sum is weights[1] + weights[3] = 40.
theorem t10_set_sum_set_positive :
    fullInterpB ⟨"fzn_sum_set"⟩
      [.array [.int 3, .int 5, .int 7], .array [.int 10, .int 20, .int 30],
       .setOfInt (.enumeration [3, 7]), .int 40] = true := by decide

-- Mismatch: `values` has three positions but `weights` only two, so the
-- upstream `weights[3]` access is undefined, hence false (the old `zip`
-- silently dropped the third position and accepted total = 0).
theorem t10_set_sum_set_weight_mismatch_rejected :
    fullInterpB ⟨"fzn_sum_set"⟩
      [.array [.int 3, .int 5, .int 7], .array [.int 10, .int 20],
       .setOfInt (.enumeration []), .int 0] = false := by decide

-- Longer `weights`: position 3 is never read by the upstream sum, so it is
-- accepted despite the extra `99`.
theorem t10_set_sum_set_extra_weight_ignored :
    fullInterpB ⟨"fzn_sum_set"⟩
      [.array [.int 3, .int 5], .array [.int 10, .int 20, .int 99],
       .setOfInt (.enumeration [5]), .int 20] = true := by decide

-- `selected` is a set of values, not of indices: 99 is outside
-- `index_set(values)` yet selects nothing, so the sum is 0.
theorem t10_set_sum_set_selected_value_not_an_index :
    fullInterpB ⟨"fzn_sum_set"⟩
      [.array [.int 3], .array [.int 10],
       .setOfInt (.enumeration [99]), .int 0] = true := by decide

/-! ## `fzn_sum_pred`

Upstream `fzn_sum_pred.mzn:7-9` builds
`sums = [sum (k in sets[j]) (coefficients[k]) | j in index_set(sets)]`
eagerly for *every* set and then reads `sums[idx]`. Hence `idx` is a valid
1-based index of `sets`, and every element of every set must be a valid
1-based index of `coefficients`; an out-of-range element makes the
constraint undefined and false, even in a set that `idx` does not select. -/

-- Positive: `idx = 1` selects {1, 2}, so the sum is 7 + 5 = 12.
theorem t10_set_sum_pred_positive :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1, .array [.setOfInt (.enumeration [1, 2]),
        .setOfInt (.enumeration [2])],
       .array [.int 7, .int 5], .int 12] = true := by decide

-- Out of range: the second set contains 4, outside `index_set(coefficients)`
-- of length 2, so the eagerly built `sums` is undefined and the whole call
-- is false although the selected first set is in range.
theorem t10_set_sum_pred_out_of_range_rejected :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1, .array [.setOfInt (.enumeration [1]),
        .setOfInt (.enumeration [4])],
       .array [.int 4, .int 6], .int 4] = false := by decide

-- The same out-of-range failure in the selected set itself.
theorem t10_set_sum_pred_selected_out_of_range_rejected :
    fullInterpB ⟨"fzn_sum_pred"⟩
      [.int 1, .array [.setOfInt (.enumeration [3])],
       .array [.int 4, .int 6], .int 6] = false := by decide

/-! ## `fzn_range`

Upstream `fzn_range.mzn:3-7` reads `xs[i]` for every `i` in `domain` and
`xs[j]` for every `j` in `domain` again in the backward direction. Every
element of `domain` must therefore be a valid 1-based position of `xs`
(`1 ≤ i ≤ length(xs)`); an element outside that range makes the decompo-
sition undefined and false, not silently ignored. Elements of `image` are
values, not positions. -/

-- Positive: domain = {1, 3} maps 10 to 10 and 30 to 30.
theorem t10_set_range_positive :
    fullInterpB ⟨"fzn_range"⟩
      [.array [.int 10, .int 20, .int 30], .setOfInt (.enumeration [1, 3]),
       .setOfInt (.enumeration [10, 30])] = true := by decide

-- Out of range: 3 ∈ domain exceeds `length(xs) = 2`, so the forward
-- direction's `xs[3]` is undefined and the call is false. The old code
-- ignored 3 and accepted image = {10}.
theorem t10_set_range_domain_beyond_length_rejected :
    fullInterpB ⟨"fzn_range"⟩
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1, 3]),
       .setOfInt (.enumeration [10])] = false := by decide

-- Backward direction: 20 ∈ image has no preimage in domain = {1}, so the
-- second upstream conjunct is false.
theorem t10_set_range_unmapped_image_rejected :
    fullInterpB ⟨"fzn_range"⟩
      [.array [.int 10, .int 20], .setOfInt (.enumeration [1]),
       .setOfInt (.enumeration [10, 20])] = false := by decide

/-! ## `fzn_write`

Upstream `fzn_write.mzn:2` is
`forall (j in index_set(I)) (O[j] = if j = i then v else I[j] endif)`:
it reads `O[j]` for every position of `I`. A shorter `O` is undefined and
false; extra positions of a longer `O` are never read and are accepted. The
index `i` is not an index premise of the decomposition — if it is outside
`index_set(I)`, no position is updated and `O` must equal `I`. -/

-- Positive: position 2 is replaced by 9.
theorem t10_chan_write_positive :
    fullInterpB ⟨"fzn_write"⟩
      [.array [.int 1, .int 2, .int 3], .int 2, .int 9,
       .array [.int 1, .int 9, .int 3]] = true := by decide

-- Mismatch: `O` is shorter than `I`, so the upstream `O[2]` access is
-- undefined, hence false.
theorem t10_chan_write_short_output_rejected :
    fullInterpB ⟨"fzn_write"⟩
      [.array [.int 1, .int 2], .int 2, .int 9, .array [.int 1]] = false := by decide

-- Longer `O`: position 3 is never read, so the extra `7` is accepted.
theorem t10_chan_write_extra_output_ignored :
    fullInterpB ⟨"fzn_write"⟩
      [.array [.int 1, .int 2], .int 2, .int 9,
       .array [.int 1, .int 9, .int 7]] = true := by decide

-- Out-of-range `i = 5`: no `j ∈ index_set(I)` equals 5, so every position
-- keeps its input value and the call is true (the decomposition is total in
-- `i`; it is not a shape error).
theorem t10_chan_write_index_outside_input_total :
    fullInterpB ⟨"fzn_write"⟩
      [.array [.int 1, .int 2], .int 5, .int 9, .array [.int 1, .int 2]] =
        true := by decide

/-! ## `fzn_writes`

Upstream `fzn_writes.mzn:7-10` is
`forall (j in index_set(P)) (O[P[j]] = V[j]) /\
 forall (i in index_set(I))
   (if forall (j in index_set(P)) (P[j] != i) then O[i] = I[i] else true endif)`.
Hence `P.length ≤ V.length` (the first loop reads `V[j]` for every `j ∈
index_set(P)`), every `P[j]` must be a valid position of `O`
(`1 ≤ P[j] ≤ O.length`), and `I.length ≤ O.length` (the second loop reads
`O[i]` for every `i ∈ index_set(I)`). Extra entries of a longer `V` or `O`
are never read and are accepted. -/

-- Positive: positions 2 and 3 are replaced by 9 and 8, position 1 kept.
theorem t10_chan_writes_positive :
    fullInterpB ⟨"fzn_writes"⟩
      [.array [.int 1, .int 2, .int 3], .array [.int 2, .int 3],
       .array [.int 9, .int 8], .array [.int 1, .int 9, .int 8]] =
        true := by decide

-- Mismatch: `O` has length 1 but `I` has length 3, so the second loop's
-- `O[2]` access is undefined, hence false.
theorem t10_chan_writes_short_output_rejected :
    fullInterpB ⟨"fzn_writes"⟩
      [.array [.int 1, .int 2, .int 3], .array [.int 1], .array [.int 7],
       .array [.int 7]] = false := by decide

-- Mismatch: `P` has length 2 but `V` has length 1, so the first loop's
-- `V[2]` access is undefined, hence false.
theorem t10_chan_writes_short_values_rejected :
    fullInterpB ⟨"fzn_writes"⟩
      [.array [.int 1, .int 2], .array [.int 1, .int 2], .array [.int 5],
       .array [.int 5, .int 2]] = false := by decide

-- Out of range: `P[1] = 3` exceeds `length(O) = 2`, so `O[P[1]]` is
-- undefined, hence false.
theorem t10_chan_writes_index_beyond_output_rejected :
    fullInterpB ⟨"fzn_writes"⟩
      [.array [.int 1, .int 2], .array [.int 3], .array [.int 9],
       .array [.int 1, .int 2]] = false := by decide

-- Longer unused `V` and `O`: `V[2] = 99` and `O[3] = 7` are never read, so
-- the call is accepted.
theorem t10_chan_writes_extra_unused_entries_accepted :
    fullInterpB ⟨"fzn_writes"⟩
      [.array [.int 1, .int 2], .array [.int 1], .array [.int 5, .int 99],
       .array [.int 5, .int 2, .int 7]] = true := by decide

/-! ## `fzn_sort`

Upstream `fzn_sort.mzn:4-7` existentially quantifies
`p : index_set(xs) → index_set(ys)` with `ys[p[i]] = xs[i]` and
`alldifferent(p)`, conjoined with `increasing(ys)`. Such an injective `p`
exists exactly when every value occurs in `ys` at least as often as in `xs`,
so `ys` may be longer than `xs` (extra entries only have to keep `ys`
increasing). A shorter `ys` cannot host an injective `p` and is false. -/

-- Positive: [3, 1] is sorted to [1, 3].
theorem t10_lex_sort_positive :
    fullInterpB ⟨"fzn_sort"⟩
      [.array [.int 3, .int 1], .array [.int 1, .int 3]] = true := by decide

-- Mismatch: `ys` is shorter than `xs`, so no injective `p` exists and the
-- call is false.
theorem t10_lex_sort_short_output_rejected :
    fullInterpB ⟨"fzn_sort"⟩
      [.array [.int 3, .int 1], .array [.int 1]] = false := by decide

-- Longer `ys`: p = [2, 1] maps 3 to ys[2] and 1 to ys[1]; ys is increasing,
-- so the extra 7 is accepted.
theorem t10_lex_sort_extra_output_accepted :
    fullInterpB ⟨"fzn_sort"⟩
      [.array [.int 3, .int 1], .array [.int 1, .int 3, .int 7]] =
        true := by decide

-- A longer `ys` may even repeat a value: p = [1] embeds xs = [1] into
-- ys = [1, 1], and `alldifferent(p)` is vacuous for a singleton.
theorem t10_lex_sort_extra_duplicate_accepted :
    fullInterpB ⟨"fzn_sort"⟩ [.array [.int 1], .array [.int 1, .int 1]] =
      true := by decide

/-! ## `fzn_arg_sort_int`

Upstream `fzn_arg_sort_int.mzn:4-6` is
`all_different(permutation) /\
 forall (j in 1..length(xs) - 1)
   (xs[permutation[j]] <= xs[permutation[j + 1]] /\
    (xs[permutation[j]] == xs[permutation[j + 1]] ->
     permutation[j] < permutation[j + 1]))`.
For `length(xs) ≥ 2` the loop reads `permutation[1..length(xs)]`, so those
entries must exist and be 1-based positions of `xs`; `all_different`
constrains the whole array. The raw text imposes no length equality and no
range on entries beyond position `length(xs)`, so a longer
globally-duplicate-free `permutation` is accepted (the old gate rejected it).
For `length(xs) ≤ 1` the loop range `1..length(xs)-1` is empty, so the loop
is vacuous and only `all_different(permutation)` remains; an empty or
arbitrary-position `permutation` is accepted when duplicate-free. -/

-- Positive: sorting [30, 10] gives the 1-based positions [2, 1].
theorem t10_lex_arg_sort_positive :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 30, .int 10], .array [.int 2, .int 1]] = true := by decide

-- Mismatch: `permutation` is shorter than `xs`, so the loop's
-- `permutation[2]` access is undefined, hence false.
theorem t10_lex_arg_sort_short_output_rejected :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 30, .int 10], .array [.int 2]] = false := by decide

-- Longer `permutation`: the loop only reads positions 1 and 2; the extra
-- distinct entry 3 is unconstrained by the raw decomposition, so it is
-- accepted.
theorem t10_lex_arg_sort_extra_output_accepted :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 30, .int 10], .array [.int 2, .int 1, .int 3]] =
        true := by decide

-- Out of range: `permutation[1] = 3` exceeds `length(xs) = 2`, so the loop's
-- `xs[3]` access is undefined, hence false.
theorem t10_lex_arg_sort_value_beyond_length_rejected :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 30, .int 10], .array [.int 3, .int 1]] = false := by decide

-- Stability: the values are equal, so the raw decomposition requires
-- `permutation[1] < permutation[2]`; 2 < 1 is false.
theorem t10_lex_arg_sort_unstable_tie_rejected :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 10, .int 10], .array [.int 2, .int 1]] = false := by decide

-- `all_different(permutation)` on the whole array: a duplicate entry is
-- rejected even when the loop conditions would hold.
theorem t10_lex_arg_sort_duplicate_entry_rejected :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 10, .int 20], .array [.int 1, .int 1]] = false := by decide

-- Singleton `xs`: the loop `1..length(xs)-1` is empty, so an entry outside
-- `1..length(xs)` is never read and only global distinctness remains.
theorem t10_lex_arg_sort_singleton_any_position_accepted :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 10], .array [.int 7]] = true := by decide

-- Singleton `xs` with an empty `permutation`: the loop is vacuous and
-- `all_different([])` is true, so the raw decomposition accepts it.
theorem t10_lex_arg_sort_singleton_empty_perm_accepted :
    fullInterpB ⟨"fzn_arg_sort_int"⟩
      [.array [.int 10], .array []] = true := by decide

/-! ## T10-W3: packing, scheduling and if-then-else witnesses (SC-04) -/

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

/-! ## T10-W4: extended scheduling, write and MDD witnesses (SC-04/SC-06) -/

/-
Purpose: T10/SC-04 regression witnesses for the extended scheduling,
  geometric, write/partiality and MDD global constraints: shape
  (parallel-array length), argument-derived index and partiality gates.
Dependencies: LeanFzn.Semantics.Globals (fullInterpB dispatches to the
  Sched2 and Regular family interpretations; fullDecodes exposes the
  decoder-side length gates).
Why: Expected values are read off the pinned raw `fzn_*` decompositions
  in tmp/semantic-conformance/upstream/share/minizinc/std, independently
  of the Boolean/Prop agreement proofs, except for the documented
  `restricted` rows (`fzn_cumulatives`, `fzn_cumulatives_decomp`,
  `fzn_mdd_nondet`, `fzn_cost_mdd`): their witnesses pin the restricted
  fragment recorded in the ledger, and the cumulatives comments say so.
DAG: semantic families -> these kernel-evaluated regressions; no runtime
  module imports them.
-/

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals

/-! ## `fzn_cumulatives` / `fzn_cumulatives_decomp`

`fzn_cumulatives_decomp.mzn:11` sets `Tasks = index_set(start)` and all
task reads (`start`, `duration`, `resource`, `machine` at lines 16–42) are
at `i,j ∈ Tasks`; `bound[machine[j]]` is read at lines 44–47.  The machine
value is a 1-based index of `bound`.  `fzn_cumulatives.mzn:3-5` documents
`min_machine` as the first machine of `bound`'s index set, so the decoder
normalizes `machine[i] - min_machine + 1`; `_decomp` has no `min_machine`.

**Restricted rows.** The raw reads of `duration`/`machine`/`bound` are
conditionally masked (`mytask` is false when its reads are undefined, and
an implication with a false antecedent is true).  The implemented
`cumulativesShape` gate is unconditional, so these two rows are recorded
`restricted` in the ledger: the witnesses below pin the documented
restricted fragment.  In particular the short-array rejections are the
gate's restriction, not raw MiniZinc truth. -/

-- Positive upper bound: task 0 covers its start point with load 2 ≤ 5.
theorem t10_cumulatives_upper_positive :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true, .int 1] = true := by decide

-- Upper bound violated: the same load 2 exceeds bound[1] = 1.
theorem t10_cumulatives_upper_bound_violation_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 1], .bool true, .int 1] = false := by decide

-- Positive lower bound: load 2 ≥ bound[1] = 2.
theorem t10_cumulatives_lower_positive :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 2], .bool false, .int 1] = true := by decide

-- Lower bound violated: load 2 < bound[1] = 3.
theorem t10_cumulatives_lower_bound_violation_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 3], .bool false, .int 1] = false := by decide

-- `duration[1]` is missing.  The raw decomposition masks this read; the
-- restricted `cumulativesShape` gate rejects it (the old code silently used 0).
theorem t10_cumulatives_short_duration_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- `resource[1]` is missing.  The raw decomposition masks this read; the
-- restricted `cumulativesShape` gate rejects it.
theorem t10_cumulatives_short_resource_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [], .array [.int 1],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- `machine[1]` is missing.  The raw decomposition masks this read; the
-- restricted `cumulativesShape` gate rejects it.
theorem t10_cumulatives_short_machine_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- Normalized machine 0: outside `1..length(bound) = 1..1`.
theorem t10_cumulatives_machine_zero_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 0],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- Normalized machine 2 with `length(bound) = 1`.
theorem t10_cumulatives_machine_above_bound_rejected :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 2],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- Trailing `duration`, `resource` and `machine` entries are never read.
theorem t10_cumulatives_extra_duration_accepted :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 3, .int 99], .array [.int 2, .int 99],
       .array [.int 1, .int 99], .array [.int 5], .bool true, .int 1] =
      true := by decide

-- `min_machine` normalization: machine 6 with `min_machine = 5` becomes
-- the 1-based machine 2, which is in range for `bound = [1, 2]`.
theorem t10_cumulatives_min_machine_normalized :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [.int 0], .array [.int 1], .array [.int 1], .array [.int 6],
       .array [.int 1, .int 2], .bool true, .int 5] = true := by decide

-- Empty `start`: both upstream `forall (j in Tasks)` loops are vacuous.
theorem t10_cumulatives_empty_start_vacuous :
    fullInterpB ⟨"fzn_cumulatives"⟩
      [.array [], .array [], .array [], .array [], .array [],
       .bool true, .int 1] = true := by decide

-- `_decomp` positive: no `min_machine`, machine values used unchanged.
theorem t10_cumulatives_decomp_positive :
    fullInterpB ⟨"fzn_cumulatives_decomp"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true] = true := by decide

-- `_decomp` with a missing duration; the restricted gate rejects it even
-- though the raw decomposition masks the read.
theorem t10_cumulatives_decomp_short_duration_rejected :
    fullInterpB ⟨"fzn_cumulatives_decomp"⟩
      [.array [.int 0], .array [], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true] = false := by decide

-- `_decomp` with a missing machine; the restricted gate rejects it even
-- though the raw decomposition masks the read.
theorem t10_cumulatives_decomp_short_machine_rejected :
    fullInterpB ⟨"fzn_cumulatives_decomp"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [],
       .array [.int 5], .bool true] = false := by decide

-- `_decomp` machine 0 is not a 1-based index of `bound`.
theorem t10_cumulatives_decomp_machine_zero_rejected :
    fullInterpB ⟨"fzn_cumulatives_decomp"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 0],
       .array [.int 5], .bool true] = false := by decide

-- `_decomp` trailing duration entries are unused.
theorem t10_cumulatives_decomp_longer_duration_accepted :
    fullInterpB ⟨"fzn_cumulatives_decomp"⟩
      [.array [.int 0], .array [.int 3, .int 99], .array [.int 2, .int 99],
       .array [.int 1, .int 99], .array [.int 5], .bool true] =
      true := by decide

/-! ## `fzn_writes_seq`

`fzn_writes_seq.mzn:9-14` loops over `index_set(I)` and reads `O[i]`,
and builds `Vi`/`Pi` over `index_set(V)`.  `Pi` compares `P[j] == i` for
every `j ∈ index_set(V)`: a missing `P[j]` is undefined in a Boolean
context, which MiniZinc turns into `false` (no matching write).  The
outer loop is vacuous for `I = []`.  The only unconditional read is
`O[i]` at `i ∈ index_set(I)`, so `I.length ≤ O.length` is the only
length gate.  Upstream `Pi` is `reverse([P[j] == i | j in index_set(V)])
++ [true]`, and `specification/minizinc-2.10.1/lib-globals-math.html`
§arg_max states "When breaking ties the least index is returned": the
least `Pi` index is the **largest** `j ∈ index_set(V)`, i.e. the last
write wins.  The Lean `filter … |>.reverse.head?` returns exactly that
largest `j`. -/

-- Positive: the single write 7 at position 1 is copied to `O[1]`.
theorem t10_writes_seq_positive :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 5], .array [.int 1], .array [.int 7],
       .array [.int 7]] = true := by decide

-- Trailing `O` and `P` entries are never read.
theorem t10_writes_seq_longer_output_accepted :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 5], .array [.int 1, .int 0], .array [.int 7, .int 0],
       .array [.int 7, .int 99]] = true := by decide

-- A `P` value outside `index_set(I)` writes nowhere: `O` keeps `I`.
theorem t10_writes_seq_position_outside_input_range_accepted :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 5], .array [.int 3], .array [.int 7],
       .array [.int 5]] = true := by decide

-- `P` has a second entry equal to position 1, but `V` is shorter:
-- upstream scans only `index_set(V)`, so the trailing `P` entry is
-- invisible and the last (only) write is `V[1] = 7`.  The old
-- `List.range p.length` scan was wrong here: it selected the phantom
-- `V[2]` default 0.
theorem t10_writes_seq_trailing_write_ignored :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 5], .array [.int 1, .int 1], .array [.int 7],
       .array [.int 7]] = true := by decide

-- `I` has two positions but `O` only one: `O[2]` is undefined upstream.
theorem t10_writes_seq_short_output_rejected :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 5, .int 0], .array [], .array [],
       .array [.int 5]] = false := by decide

-- `V` has one position but `P` is empty.  The comparison `P[1] == 1`
-- is undefined and becomes false: no write happens and `O[1] = I[1]`.
theorem t10_writes_seq_short_position_no_write_accepted :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 7], .array [], .array [.int 7],
       .array [.int 7]] = true := by decide

-- `V` has two positions but `P` only one.  The missing `P[2]` compares
-- false, so only the write `V[1] = 3` at position 1 is seen.
theorem t10_writes_seq_short_position_masked_ignored :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 7], .array [.int 1], .array [.int 3, .int 4],
       .array [.int 3]] = true := by decide

-- The same call with `O` holding `I[1]` is false: the visible first
-- write still wins.
theorem t10_writes_seq_short_position_value_rejected :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 7], .array [.int 1], .array [.int 3, .int 4],
       .array [.int 7]] = false := by decide

-- Two writes to position 1: the last one (`V[2] = 9`) wins.
theorem t10_writes_seq_last_write_wins :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 0], .array [.int 1, .int 1],
       .array [.int 7, .int 9], .array [.int 9]] = true := by decide

-- The first write is not the value of `O[1]` when a later write exists.
theorem t10_writes_seq_first_write_not_last_rejected :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [.int 0], .array [.int 1, .int 1],
       .array [.int 7, .int 9], .array [.int 7]] = false := by decide

-- Empty `I`: the outer `forall` is vacuous, so neither `O` nor `P` is
-- read even though `V` is longer than `P`.
theorem t10_writes_seq_empty_input_vacuous :
    fullInterpB ⟨"fzn_writes_seq"⟩
      [.array [], .array [], .array [.int 3, .int 4],
       .array []] = true := by decide

/-! ## `fzn_if_then_else_partiality`

`fzn_if_then_else_partiality.mzn:8-12` computes `d[i]` from the earlier
conditions and reads `def[i]` only in the two implications.  `d[i]` is
true exactly until the first true `c` index: earlier `c` entries are
false and later `d` entries are false, so every `def` read except the
selected one is masked.  A missing selected `def` entry is undefined in
a Boolean context and reads as `false`; there is no length gate. -/

-- Positive with a true condition at the second position.
theorem t10_ite_partiality_true_condition_positive :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false, .bool true],
       .array [.bool true, .bool false], .bool false] = true := by decide

-- Positive with no true condition: `b` is unrestricted (`true` here).
theorem t10_ite_partiality_no_condition_positive :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false], .array [.bool false], .bool true] =
      true := by decide

-- `c` has two positions but `def` only one.  The selected index is 2,
-- where the missing `def` entry reads as `false`, matching `b = false`.
theorem t10_ite_partiality_short_def_false_accepted :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false, .bool true], .array [.bool false],
       .bool false] = true := by decide

-- The same call with `b = true` is false: the selected missing entry
-- reads as `false`.
theorem t10_ite_partiality_short_def_true_rejected :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false, .bool true], .array [.bool false],
       .bool true] = false := by decide

-- Empty `def` with a selected index: `false` reads as the default.
theorem t10_ite_partiality_empty_def_false_accepted :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool true], .array [], .bool false] = true := by decide

-- Empty `def` with `b = true`: rejected by the `false` default.
theorem t10_ite_partiality_empty_def_true_rejected :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool true], .array [], .bool true] = false := by decide

-- The two false conditions before the selected index need no `def`
-- entry: those reads are masked.
theorem t10_ite_partiality_earlier_def_masked :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false, .bool false, .bool true], .array [],
       .bool false] = true := by decide

-- The same call with `b = true` is false at the selected index.
theorem t10_ite_partiality_earlier_def_masked_true_rejected :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool false, .bool false, .bool true], .array [],
       .bool true] = false := by decide

-- Trailing `def` entries are never read.
theorem t10_ite_partiality_longer_def_accepted :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool true],
       .array [.bool false, .bool true, .bool false], .bool false] =
      true := by decide

-- After the first true condition, `d` is false, so a missing later
-- `def` entry is masked.
theorem t10_ite_partiality_later_def_masked :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [.bool true, .bool true], .array [.bool true],
       .bool true] = true := by decide

-- Empty `c`: both `forall` loops are vacuous and `b` is unrestricted.
theorem t10_ite_partiality_empty_condition_positive :
    fullInterpB ⟨"fzn_if_then_else_partiality"⟩
      [.array [], .array [], .bool true] = true := by decide

/-! ## `fzn_diffn_nonoverlap_k`

`fzn_diffn_k.mzn:21` is
`exists (j in index_set(x1)) (x1[j] + w1[j] <= x2[j] \/
 x2[j] + w2[j] <= x1[j])`.
At each `j` a disjunct is evaluated only when all of its own reads are
in range; a missing entry makes that disjunct undefined and hence false.
An early true witness makes the existential true without reading the
later entries, so there is no unconditional length gate. -/

-- Positive: the intervals [0,2) and [5,7) are separated on the axis.
theorem t10_diffn_nonoverlap_positive :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0], .array [.int 2], .array [.int 5],
       .array [.int 2]] = true := by decide

-- Negative: the intervals [0,3) and [2,5) overlap.
theorem t10_diffn_nonoverlap_overlap_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0], .array [.int 3], .array [.int 2],
       .array [.int 3]] = false := by decide

-- `x1` has two axes but `w1` only one.  Axis 1 separates the boxes, so
-- the existential is true before the missing `w1[2]` read is reached.
theorem t10_diffn_nonoverlap_short_w1_accepted :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [.int 2],
       .array [.int 5, .int 10], .array [.int 2, .int 2]] =
      true := by decide

-- Missing second axis of `x2`, masked by the first-axis witness.
theorem t10_diffn_nonoverlap_short_x2_accepted :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [.int 2, .int 2],
       .array [.int 5], .array [.int 2, .int 2]] = true := by decide

-- Missing second axis of `w2`: only the second disjunct of axis 2 reads
-- it, and axis 1 already separates, so the call is true.
theorem t10_diffn_nonoverlap_short_w2_accepted :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [.int 2, .int 2],
       .array [.int 5, .int 10], .array [.int 2]] = true := by decide

-- A missing `w1` entry with no separating axis is false.
theorem t10_diffn_nonoverlap_short_w1_no_witness_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [],
       .array [.int 5, .int 10], .array [.int 2, .int 2]] =
      false := by decide

-- A missing `x2` entry with no separating axis is false.
theorem t10_diffn_nonoverlap_short_x2_no_witness_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [.int 2, .int 2],
       .array [], .array [.int 2, .int 2]] = false := by decide

-- A missing `w2` entry with no separating axis: both first disjuncts
-- fail, and neither second disjunct can be read.
theorem t10_diffn_nonoverlap_short_w2_no_witness_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [.int 5, .int 5],
       .array [.int 0, .int 0], .array []] = false := by decide

-- A later witness can be true even when an earlier `w1` entry is
-- missing: axis 2 satisfies the second disjunct.
theorem t10_diffn_nonoverlap_later_witness_masks_missing_w1 :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 10], .array [],
       .array [.int 5, .int 5], .array [.int 2, .int 5]] =
      true := by decide

-- No axis separates either pair of boxes.
theorem t10_diffn_nonoverlap_no_witness_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0, .int 1], .array [.int 2, .int 2],
       .array [.int 1, .int 2], .array [.int 2, .int 2]] =
      false := by decide

-- Empty `x1`: the existential has no witness.
theorem t10_diffn_nonoverlap_empty_x1_rejected :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [], .array [], .array [], .array []] = false := by decide

-- Trailing `w1`/`w2` entries are never read.
theorem t10_diffn_nonoverlap_longer_trailing_accepted :
    fullInterpB ⟨"fzn_diffn_nonoverlap_k"⟩
      [.array [.int 0], .array [.int 2, .int 99], .array [.int 5],
       .array [.int 2, .int 99]] = true := by decide

/-! ## `fzn_mdd`

`fzn_mdd.mzn:16-35` reads `level[from[e]]`, `from[e]`, `to[e]` and
`label[e]` for `e ∈ 1..E`, with `from[e] ∈ 1..N`, `to[e] ∈ 0..N` and
`level[from[e]] ∈ 1..length(xs)`.  `mddGate` (G1–G7) is exactly this
readability gate; all witnesses below differ from the positive call in
one gated array or index. -/

-- Positive diamond: xs = [1,2], edge 1: 1 --{1}--> 2, edge 2: 2 --{2}--> T.
theorem t10_mdd_positive :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = true := by decide

-- `level[2]` would be read by the second edge, but `level` has length 1.
theorem t10_mdd_short_level_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- `from[2]` is read for edge 2, but `from` has length 1.
theorem t10_mdd_short_from_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- `label[2]` is read for edge 2, but `label` has length 1.
theorem t10_mdd_short_label_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2], .array [.setOfInt (.enumeration [1])],
       .array [.int 2, .int 0]] = false := by decide

-- `to[2]` is read for edge 2, but `to` has length 1.
theorem t10_mdd_short_to_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2]] = false := by decide

-- `from[e] = 0` is outside the node set `1..N`.
theorem t10_mdd_from_zero_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 0, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- `from[e] = N + 1` is outside `1..N`.
theorem t10_mdd_from_above_n_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 3, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- `to[e] = -1` is outside `0..N`.
theorem t10_mdd_to_negative_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int (-1), .int 0]] = false := by decide

-- `to[e] = N + 1` is outside `0..N`.
theorem t10_mdd_to_above_n_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 3]] = false := by decide

-- `level[from[1]] = 0` is outside `1..L`.
theorem t10_mdd_level_zero_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 0, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

-- `level[from[1]] = L + 1 = 3` is outside `1..L`.
theorem t10_mdd_level_above_l_rejected :
    fullInterpB ⟨"fzn_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 3, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = false := by decide

/-! ## `fzn_mdd_nondet`

The restricted walk search uses the same `mddGate`; its own witness is a
short `to` array, rejected by G4c before `walkFrom` runs. -/

-- Positive: the same diamond admits the walk 1 --{1}--> 2 --{2}--> T.
theorem t10_mdd_nondet_positive :
    fullInterpB ⟨"fzn_mdd_nondet"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2, .int 0]] = true := by decide

-- Short `to` array: G4c rejects the call.
theorem t10_mdd_nondet_short_arrays_rejected :
    fullInterpB ⟨"fzn_mdd_nondet"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 2]] = false := by decide

/-! ## `fzn_cost_mdd`

`fzn_cost_mdd.mzn:18-22` reads `cost[e]` for every `e ∈ 1..E`;
`costMddGate` adds G8 (`E ≤ length(cost)`, no default) and the canonical
layered conditions used by the restricted `ln`/`un` recursion.  The
positive call has costs 4 and 7 on the two edges, hence `ln[1] = 11`. -/

-- Positive canonical fragment: total cost 4 + 7 = 11.
theorem t10_cost_mdd_positive :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4, .int 7], .array [.int 2, .int 0], .int 11] =
      true := by decide

-- `cost[2]` is read for edge 2, but `cost` has length 1 (G8).
theorem t10_cost_mdd_short_cost_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4], .array [.int 2, .int 0], .int 11] = false := by decide

-- Wrong total: the canonical equations force `total_cost = ln[1] = 11`.
theorem t10_cost_mdd_wrong_total_rejected :
    fullInterpB ⟨"fzn_cost_mdd"⟩
      [.array [.int 1, .int 2], .int 2, .array [.int 1, .int 2], .int 2,
       .array [.int 1, .int 2],
       .array [.setOfInt (.enumeration [1]), .setOfInt (.enumeration [2])],
       .array [.int 4, .int 7], .array [.int 2, .int 0], .int 10] =
      false := by decide

/-! ## Decoder-side gates (`fullDecodes`)

`fullInterpB` tests the mathematical gates; `fullDecodes` additionally
exposes the ABI decodability gate `Sched2.sched2Decodes`.  It keeps the
unconditional length conjuncts (`cumulatives`, `writes_seq`) and, for the
masked-read families (`diffn_nonoverlap_k`,
`if_then_else_partiality`), only decodability.  The machine-value range
stays in the semantic gate because `ArgsAgree` does not fix
variable-argument values. -/

-- Positive `fzn_writes_seq` decoding.
theorem t10_sched2_decodes_writes_seq_positive :
    fullDecodes "fzn_writes_seq" []
      [.array [.int 5], .array [.int 3], .array [.int 7],
       .array [.int 5]] = true := by decide

-- `I` longer than `O`: `writesSeqArgShapeB` rejects at decoding.
theorem t10_sched2_decodes_writes_seq_short_output_rejected :
    fullDecodes "fzn_writes_seq" []
      [.array [.int 5, .int 0], .array [], .array [],
       .array [.int 5]] = false := by decide

-- A missing `P` entry is a masked Boolean read, so decoding accepts it.
theorem t10_sched2_decodes_writes_seq_short_position_accepted :
    fullDecodes "fzn_writes_seq" []
      [.array [.int 7], .array [], .array [.int 7],
       .array [.int 7]] = true := by decide

-- Empty `I` is vacuous regardless of the other lengths.
theorem t10_sched2_decodes_writes_seq_empty_input_accepted :
    fullDecodes "fzn_writes_seq" []
      [.array [], .array [], .array [.int 3], .array []] = true := by decide

-- Positive `fzn_cumulatives` decoding.
theorem t10_sched2_decodes_cumulatives_positive :
    fullDecodes "fzn_cumulatives" []
      [.array [.int 0], .array [.int 3], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true, .int 1] = true := by decide

-- `start` longer than `duration`: `cumulativesArgShapeB` rejects.
theorem t10_sched2_decodes_cumulatives_short_duration_rejected :
    fullDecodes "fzn_cumulatives" []
      [.array [.int 0], .array [], .array [.int 2], .array [.int 1],
       .array [.int 5], .bool true, .int 1] = false := by decide

-- The decoder no longer rejects short parallel arrays for the
-- masked-read `diffn_nonoverlap_k` family.
theorem t10_sched2_decodes_diffn_nonoverlap_short_w1_accepted :
    fullDecodes "fzn_diffn_nonoverlap_k" []
      [.array [.int 0, .int 10], .array [.int 2],
       .array [.int 5, .int 10], .array [.int 2, .int 2]] =
      true := by decide

-- A missing `def` entry is a masked read: decoding accepts it.
theorem t10_sched2_decodes_ite_short_def_accepted :
    fullDecodes "fzn_if_then_else_partiality" []
      [.array [.bool false, .bool true], .array [.bool false],
       .bool false] = true := by decide

-- A malformed third argument is still rejected by the decoder.
theorem t10_sched2_decodes_ite_malformed_rejected :
    fullDecodes "fzn_if_then_else_partiality" []
      [.array [.bool false], .array [.bool false],
       .int 0] = false := by decide
