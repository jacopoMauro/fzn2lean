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
import LeanFzn.Semantics.Globals

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
