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
import LeanFzn.Semantics.Globals

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
