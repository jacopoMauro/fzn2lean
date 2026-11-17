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
import LeanFzn.Semantics.Globals

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
