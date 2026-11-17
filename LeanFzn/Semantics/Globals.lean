import Std.Data.HashMap.Lemmas
import LeanFzn.Semantics.StdLib
import LeanFzn.Semantics.Evaluation
import LeanFzn.Semantics.Globals.AllDiffCounting
import LeanFzn.Semantics.Globals.LexSort
import LeanFzn.Semantics.Globals.PackSched
import LeanFzn.Semantics.Globals.Counting
import LeanFzn.Semantics.Globals.Channeling
import LeanFzn.Semantics.Globals.SetMath
import LeanFzn.Semantics.Globals.LexChain
import LeanFzn.Semantics.Globals.Graph
import LeanFzn.Semantics.Globals.Regular
import LeanFzn.Semantics.Globals.Sched2
open LeanFzn.Semantics


/-!
# Global constraints (FlatZinc `fzn_*` LeanFzn.Solver predicates)

The MiniZinc standard library decomposes each global constraint into a
`fzn_<name>_<type>` LeanFzn.Solver predicate that appears verbatim in compiled
FlatZinc (the library layout of MiniZinc >= 2.3).  This module adds, for
the non-float fragment of the pinned MiniZinc 2.10.1 tree (commit
`c3448c48e7f05f13805616cfd1b9e94972eef58c`, `share/minizinc/std/`):

* `globalsSig` — a `SigEnv` with the FlatZinc signatures of all
  `fzn_*` global-constraint predicates of the fragment, so models using
  them pass static checking (`wellFormedB`);
* `globalsInterp`/`globalsInterpB` — the combined mathematical
  interpretation and its executable Boolean twin, dispatching each of
  the 138 supported `fzn_*` names to its family module
  (following the library's decomposition semantics);
* `globalsInterpB_iff` — the master agreement theorem relating the
  combined twin to the combined declarative meaning, which together
  with `checkSolutionFull_correct` (the correctness theorem of the full
  solution checker `checkSolutionFull`) extends the checker's
  correctness to global constraints.

The interpretive decision behind every family member's meaning —
1-based positions, tie-breaking, partiality, closedness, corner
cases — is recorded in
`specification/flatzinc_specification_assumptions.md`, G-series
(G1–G33), with per-predicate handbook quotations and `.mzn`
decomposition citations in the family module docstrings.

Excluded from the fragment (and therefore not in `globalsNames`): every
`_reif`, float, and opt (`var opt`) variant, the string-regexp form
of `regular` (the integer `fzn_regular` family is supported),
`fzn_neural_net`/`fzn_piecewise_linear`/`fzn_piecewise_linear_non_continuous`
(floats), and `fzn_alternative`/`fzn_span` (optional variables).  The
five core out-of-fragment names — `fzn_alternative`, `fzn_span`,
`fzn_neural_net`, `fzn_piecewise_linear`,
`fzn_piecewise_linear_non_continuous` — are listed in
`globalsUnsupported` so the checker *reports* them rather than silently
mis-checking; other excluded variants are reported as unknown names.

## Conventions

All array arguments are 1-based (FlatZinc arrays are `array [1..n]`),
which the `List.getElem`-based twins realize with 0-based `List`
indices plus a `+1` shift in wrapper helpers.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals

open LeanFzn

/-! ## Small helpers -/

/-- 1-based lookup in a list of values; `none` out of bounds. -/
private def get1 (xs : List Value) (i : Int) : Option Value :=
  if 1 ≤ i ∧ i ≤ xs.length then xs[i.toNat - 1]? else none

/-- 1-based lookup in a list of integers; `none` out of bounds or if the
    entry is not an integer. -/
private def getInt1 (xs : List Value) (i : Int) : Option Int :=
  match get1 xs i with
  | some (.int v) => some v
  | _ => none

/-- 1-based lookup in a list of booleans. -/
private def getBool1 (xs : List Value) (i : Int) : Option Bool :=
  match get1 xs i with
  | some (.bool v) => some v
  | _ => none

/-- 1-based lookup in a list of sets. -/
private def getSet1 (xs : List Value) (i : Int) : Option IntSetValue :=
  match get1 xs i with
  | some (.setOfInt v) => some v
  | _ => none

/-- The integers of a value list (`none` if any element is not an
    integer). -/
private def asInts : List Value → Option (List Int)
  | [] => some []
  | .int x :: rest => (asInts rest).map (x :: ·)
  | _ => none

/-- The booleans of a value list. -/
private def asBools : List Value → Option (List Bool)
  | [] => some []
  | .bool x :: rest => (asBools rest).map (x :: ·)
  | _ => none

/-- The sets of a value list. -/
private def asSets : List Value → Option (List IntSetValue)
  | [] => some []
  | .setOfInt x :: rest => (asSets rest).map (x :: ·)
  | _ => none

/-- The range `l..u` of an interval set. -/
private def intervalOf (s : IntSetValue) : Option (Int × Int) :=
  match s with
  | .interval lo hi => some (lo, hi)
  | _ => none

/-- All integers possibly contained in a set (an upper bound of the
    domain); for a closed under approximation we use the elements of the
    representation itself. -/
private def setBound (s : IntSetValue) : List Int := LeanFzn.Semantics.Evaluation.setElems s

/-! ## The signatures -/

/-- The FlatZinc signatures of the supported global constraints. -/
def globalsSig : LeanFzn.Semantics.SigEnv := fun x =>
  match x.name with
  -- all-different family
  | "fzn_all_different_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_all_different_set" =>
      [[.array .int (.var (.par .setOfInt))]]
  | "fzn_all_disjoint" =>
      [[.array .int (.var (.par .setOfInt))]]
  | "fzn_all_equal_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_all_equal_set" =>
      [[.array .int (.var (.par .setOfInt))]]
  | "fzn_alldifferent_except" =>
      [[.array .int (.var (.par .int)), .basic (.par .setOfInt)]]
  | "fzn_alldifferent_except_0" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_symmetric_all_different" =>
      [[.array .int (.var (.par .int))]]
  -- counting
  | "fzn_nvalue" =>
      [[.basic (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_among" =>
      [[.basic (.var (.par .int)), .array .int (.var (.par .int)),
        .basic (.par .setOfInt)]]
  | "fzn_at_least_int" =>
      [[.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]]
  | "fzn_at_most_int" =>
      [[.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]]
  | "fzn_exactly_int" =>
      [[.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]]
  | "fzn_count_eq" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_eq_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_count_geq" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_geq_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_count_gt" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_gt_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_count_leq" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_leq_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_count_lt" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_lt_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_count_neq" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_count_neq_par" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]]
  | "fzn_distribute" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_global_cardinality" =>
      [[.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.var (.par .int))]]
  | "fzn_global_cardinality_closed" =>
      [[.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.var (.par .int))]]
  | "fzn_global_cardinality_low_up" =>
      [[.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .int)]]
  | "fzn_global_cardinality_low_up_closed" =>
      [[.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .int)]]
  -- set counting
  | "fzn_count_eq_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_count_eq_set_par" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt), .basic (.par .int)]]
  | "fzn_count_geq_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_count_gt_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_count_leq_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_count_lt_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_count_neq_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_at_least_set" =>
      [[.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]]
  | "fzn_at_most_set" =>
      [[.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]]
  | "fzn_exactly_set" =>
      [[.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]]
  -- lex (1-D int only; the flat ones)
  | "fzn_lex_less_int" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_lex_lesseq_int" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  -- sorting
  | "fzn_increasing_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_increasing_bool" =>
      [[.array .int (.var (.par .bool))]]
  | "fzn_strictly_increasing_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_sort" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_arg_sort_int" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_maximum_arg_int" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int))]]
  | "fzn_minimum_arg_int" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int))]]
  -- channeling
  | "fzn_inverse" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_inverse_in_range" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_int_set_channel" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .setOfInt))]]
  | "fzn_link_set_to_booleans" =>
      [[.basic (.var (.par .setOfInt)),
        .array .int (.var (.par .bool))]]
  -- array-related
  | "fzn_member_int" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int))]]
  | "fzn_member_bool" =>
      [[.array .int (.var (.par .bool)), .basic (.var (.par .bool))]]
  | "fzn_member_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_arg_val_int" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_arg_val_bool" =>
      [[.array .int (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_write" =>
      [[.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_writes" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  -- set-related
  | "fzn_disjoint" =>
      [[.basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_set_member" =>
      [[.basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_partition_set" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]]
  | "fzn_at_most1" =>
      [[.array .int (.var (.par .setOfInt))]]
  -- mathematical
  | "fzn_sum_set" =>
      [[.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]]
  | "fzn_sum_pred" =>
      [[.basic (.var (.par .int)), .array .int (.par .setOfInt),
        .array .int (.par .int), .basic (.var (.par .int))]]
  | "fzn_range" =>
      [[.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_roots" =>
      [[.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_array_int_union" =>
      [[.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_array_set_union" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_array_set_intersect" =>
      [[.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  | "fzn_sliding_sum" =>
      [[.basic (.par .int), .basic (.par .int),
        .basic (.par .int), .array .int (.var (.par .int))]]
  | "fzn_sliding_among_int" =>
      [[.basic (.par .int), .basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .int)), .basic (.par .setOfInt)]]
  | "fzn_sliding_among_bool" =>
      [[.basic (.par .int), .basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .bool)), .basic (.par .bool)]]
  -- packing
  | "fzn_bin_packing" =>
      [[.basic (.par .int), .array .int (.var (.par .int)),
        .array .int (.par .int)]]
  | "fzn_bin_packing_capa" =>
      [[.array .int (.par .int),
        .array .int (.var (.par .int)), .array .int (.par .int)]]
  | "fzn_bin_packing_load" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.par .int)]]
  | "fzn_knapsack" =>
      [[.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_diffn" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_diffn_nonstrict" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_geost_nonoverlap_k" =>
      [[.array .int (.var (.par .int)),
        .array .int (.par .int),
        .array .int (.var (.par .int)),
        .array .int (.par .int)]]
  -- scheduling
  | "fzn_disjunctive" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_disjunctive_strict" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_cumulative" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .basic (.var (.par .int))]]
  -- if-then-else (table-like)
  | "fzn_if_then_else_int" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.par .int), .basic (.var (.par .int))]]
  | "fzn_if_then_else_bool" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.par .bool), .basic (.var (.par .bool))]]
  | "fzn_if_then_else_set" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.par .setOfInt),
        .basic (.var (.par .setOfInt))]]
  | "fzn_if_then_else_var_int" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.var (.par .int)),
        .basic (.var (.par .int))]]
  | "fzn_if_then_else_var_bool" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]]
  | "fzn_if_then_else_var_set" =>
      [[.array .int (.var (.par .bool)),
        .array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]]
  -- extensional
  | "fzn_table_int" =>
      [[.array .int (.var (.par .int)),
        .array .int (.par .int)]]
  -- value precedence
  | "fzn_value_precede_int" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .int))]]
  | "fzn_value_precede_chain_int" =>
      [[.array .int (.par .int),
        .array .int (.var (.par .int))]]
  | "fzn_seq_precede_chain_int" =>
      [[.array .int (.var (.par .int))]]
  -- LexChain family (G24)
  | "fzn_lex_greater_int" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_lex_greatereq_int" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_lex_chain_less_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_lex_chain_lesseq_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_lex2" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_strict_lex2" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_lex_chain_lesseq_orbitope" =>
      [[.array .int (.var (.par .int)), .basic (.par .int)]]
  | "fzn_lex_chain_greater_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_lex_chain_greatereq_int" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_lex_chain_greatereq_orbitope" =>
      [[.array .int (.var (.par .int)), .basic (.par .int)]]
  -- Graph family (G25/G29)
  | "fzn_circuit" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_subcircuit" =>
      [[.array .int (.var (.par .int))]]
  | "fzn_subgraph" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_dag" =>
      [[.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_connected" =>
      [[.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_dconnected" =>
      [[.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_reachable" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_dreachable" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_tree" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_dtree" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_path" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_dpath" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))],
       [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]]
  | "fzn_bounded_path" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))],
       [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_bounded_dpath" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))],
       [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)), .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_steiner" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_dsteiner" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_wst" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  | "fzn_dwst" =>
      [[.basic (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int),
        .basic (.var (.par .int)),
        .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]]
  -- Regular family (G27/G28)
  | "fzn_regular" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .int), .basic (.par .int),
        .basic (.par .setOfInt)]]
  | "fzn_regular_nfa" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .setOfInt), .basic (.par .int),
        .basic (.par .setOfInt)]]
  | "fzn_cost_regular" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .int), .basic (.par .int),
        .basic (.par .setOfInt), .array .int (.par .int),
        .basic (.var (.par .int))]]
  | "fzn_mdd" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int)]]
  | "fzn_mdd_nondet" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int)]]
  | "fzn_cost_mdd" =>
      [[.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int))]]
  -- Sched2 family (G26/G30/G31/G32)
  | "fzn_cumulatives" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .basic (.par .bool),
        .basic (.par .int)]]
  | "fzn_cumulatives_decomp" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .basic (.par .bool)]]
  | "fzn_geost" =>
      [[.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_geost_bb" =>
      [[.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_geost_smallest_bb" =>
      [[.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_diffn_nonoverlap_k" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_diffn_k" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_diffn_nonstrict_k" =>
      [[.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]]
  | "fzn_writes_seq" =>
      [[.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]]
  | "fzn_if_then_else_partiality" =>
      [[.array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]]
  | _ => []

/-- The combined signature environment: the standard FlatZinc
    builtins plus the global constraints. -/
def fullSig : LeanFzn.Semantics.SigEnv := fun x =>
  match globalsSig x with
  | [] => LeanFzn.Semantics.stdSig x
  | ps => ps

/-! ## The unsupported global constraints

These `fzn_*` names exist in the pinned tree but are not executable
here (`fzn_alternative`/`fzn_span` need optional variables
(`var opt int`) for their span starts, and the neural-net and
piecewise-linear predicates need `var float` arguments).  The checker
reports them rather than guessing; the remaining out-of-fragment names
(`_reif`/float/opt variants of supported predicates) are reported as
unknown names by the same front-door path. -/
def globalsUnsupported : List String :=
  [ "fzn_alternative", "fzn_span"
  , "fzn_neural_net"
  , "fzn_piecewise_linear", "fzn_piecewise_linear_non_continuous"
  ]

/-! ## Combined interpretation

The 138 supported `fzn_*` names are partitioned without overlap across
ten family modules, each providing a total mathematical interpretation
(`<family>Interp : PredicateInterpretation`) and a total Boolean twin
(`<family>InterpB`) with per-name agreement theorems
`fzn_<name>_iff`.  The lists below enumerate each family's names; the
combined twin `globalsInterpB` dispatches on them, and the master
agreement theorem `globalsInterpB_iff` chains the per-family
dispatchers. -/

/-- The 8 names of the all-different family
    (`AllDiffCounting.lean`). -/
def allDiffNames : List String :=
  ["fzn_all_different_int", "fzn_all_different_set", "fzn_all_disjoint",
   "fzn_all_equal_int", "fzn_all_equal_set", "fzn_alldifferent_except",
   "fzn_alldifferent_except_0", "fzn_symmetric_all_different"]

/-- The 12 names of the lex/sort/value-precedence family
    (`LexSort.lean`). -/
def lexSortNames : List String :=
  ["fzn_lex_less_int", "fzn_lex_lesseq_int", "fzn_increasing_int",
   "fzn_increasing_bool", "fzn_strictly_increasing_int", "fzn_sort",
   "fzn_arg_sort_int", "fzn_maximum_arg_int", "fzn_minimum_arg_int",
   "fzn_value_precede_int", "fzn_value_precede_chain_int",
   "fzn_seq_precede_chain_int"]

/-- The 17 names of the packing/scheduling family
    (`PackSched.lean`). -/
def packSchedNames : List String :=
  ["fzn_bin_packing", "fzn_bin_packing_capa", "fzn_bin_packing_load",
   "fzn_knapsack", "fzn_diffn", "fzn_diffn_nonstrict",
   "fzn_geost_nonoverlap_k", "fzn_disjunctive", "fzn_disjunctive_strict",
   "fzn_cumulative", "fzn_table_int", "fzn_if_then_else_int",
   "fzn_if_then_else_bool", "fzn_if_then_else_set",
   "fzn_if_then_else_var_int", "fzn_if_then_else_var_bool",
   "fzn_if_then_else_var_set"]

/-- The 32 names of the counting family (`Counting.lean`). -/
def countingNames : List String :=
  ["fzn_nvalue", "fzn_among", "fzn_at_least_int", "fzn_at_most_int",
   "fzn_exactly_int", "fzn_count_eq", "fzn_count_eq_par", "fzn_count_geq",
   "fzn_count_geq_par", "fzn_count_gt", "fzn_count_gt_par", "fzn_count_leq",
   "fzn_count_leq_par", "fzn_count_lt", "fzn_count_lt_par", "fzn_count_neq",
   "fzn_count_neq_par", "fzn_distribute", "fzn_global_cardinality",
   "fzn_global_cardinality_closed", "fzn_global_cardinality_low_up",
   "fzn_global_cardinality_low_up_closed", "fzn_count_eq_set",
   "fzn_count_eq_set_par", "fzn_count_geq_set", "fzn_count_gt_set",
   "fzn_count_leq_set", "fzn_count_lt_set", "fzn_count_neq_set",
   "fzn_at_least_set", "fzn_at_most_set", "fzn_exactly_set"]

/-- The 11 names of the channeling family (`Channeling.lean`). -/
def channelingNames : List String :=
  ["fzn_inverse", "fzn_inverse_in_range", "fzn_int_set_channel",
   "fzn_link_set_to_booleans", "fzn_member_int", "fzn_member_bool",
   "fzn_member_set", "fzn_arg_val_int", "fzn_arg_val_bool", "fzn_write",
   "fzn_writes"]

/-- The 14 names of the set/mathematical family (`SetMath.lean`). -/
def setMathNames : List String :=
  ["fzn_disjoint", "fzn_set_member", "fzn_partition_set", "fzn_at_most1",
   "fzn_sum_set", "fzn_sum_pred", "fzn_range", "fzn_roots",
   "fzn_array_int_union", "fzn_array_set_union", "fzn_array_set_intersect",
   "fzn_sliding_sum", "fzn_sliding_among_int", "fzn_sliding_among_bool"]

/-- The 10 names of the reverse/2D lex family (`LexChain.lean`). -/
def lexChainNames : List String :=
  ["fzn_lex_greater_int", "fzn_lex_greatereq_int", "fzn_lex_chain_less_int",
   "fzn_lex_chain_lesseq_int", "fzn_lex2", "fzn_strict_lex2",
   "fzn_lex_chain_lesseq_orbitope", "fzn_lex_chain_greater_int",
   "fzn_lex_chain_greatereq_int", "fzn_lex_chain_greatereq_orbitope"]

/-- The 18 names of the circuit/graph family (`Graph.lean`). -/
def graphNames : List String :=
  ["fzn_circuit", "fzn_subcircuit", "fzn_subgraph", "fzn_dag",
   "fzn_connected", "fzn_dconnected", "fzn_reachable", "fzn_dreachable",
   "fzn_tree", "fzn_dtree", "fzn_path", "fzn_dpath",
   "fzn_bounded_path", "fzn_bounded_dpath", "fzn_steiner", "fzn_dsteiner",
   "fzn_wst", "fzn_dwst"]

/-- The 6 names of the regular/mdd family (`Regular.lean`). -/
def regularNames : List String :=
  ["fzn_regular", "fzn_regular_nfa", "fzn_cost_regular",
   "fzn_mdd", "fzn_mdd_nondet", "fzn_cost_mdd"]

/-- The 10 names of the scheduling/remaining family (`Sched2.lean`). -/
def sched2Names : List String :=
  ["fzn_cumulatives", "fzn_cumulatives_decomp", "fzn_geost", "fzn_geost_bb",
   "fzn_geost_smallest_bb", "fzn_diffn_nonoverlap_k", "fzn_diffn_k",
   "fzn_diffn_nonstrict_k", "fzn_writes_seq", "fzn_if_then_else_partiality"]

/-- The 138 supported global-constraint names (the concatenation of the
     ten family name lists). -/
def globalsNames : List String :=
  allDiffNames ++ lexSortNames ++ packSchedNames ++ countingNames ++
    channelingNames ++ setMathNames ++ lexChainNames ++ graphNames ++
    regularNames ++ sched2Names

/-- The combined global-constraint interpretation: dispatches each of
    the 138 supported `fzn_*` names to its family's interpretation
    (the families are non-overlapping; every other name yields
    falsity, since all family interps return `fun _ => False` on
    unknown names). -/
def globalsInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  if x.name ∈ allDiffNames then AllDiffCounting.allDiffInterp x
  else if x.name ∈ lexSortNames then LexSort.lexSortInterp x
  else if x.name ∈ packSchedNames then PackSched.packSchedInterp x
  else if x.name ∈ countingNames then Counting.countingInterp x
  else if x.name ∈ channelingNames then Channeling.channelingInterp x
  else if x.name ∈ setMathNames then SetMath.setMathInterp x
  else if x.name ∈ lexChainNames then LexChain.lexChainInterp x
  else if x.name ∈ graphNames then Graph.graphInterp x
  else if x.name ∈ regularNames then Regular.regularInterp x
  else if x.name ∈ sched2Names then Sched2.sched2Interp x
  else fun _ => False

/-- **Executable twin of `globalsInterp`**: dispatches each supported
    name to its family's Boolean twin; `false` on any other
    name. -/
def globalsInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  if x.name ∈ allDiffNames then AllDiffCounting.allDiffInterpB x
  else if x.name ∈ lexSortNames then LexSort.lexSortInterpB x
  else if x.name ∈ packSchedNames then PackSched.packSchedInterpB x
  else if x.name ∈ countingNames then Counting.countingInterpB x
  else if x.name ∈ channelingNames then Channeling.channelingInterpB x
  else if x.name ∈ setMathNames then SetMath.setMathInterpB x
  else if x.name ∈ lexChainNames then LexChain.lexChainInterpB x
  else if x.name ∈ graphNames then Graph.graphInterpB x
  else if x.name ∈ regularNames then Regular.regularInterpB x
  else if x.name ∈ sched2Names then Sched2.sched2InterpB x
  else fun _ => false

/-- **Decodability gate of the global fragment.**  For each supported
    name it is the `isSome` of the very decoder the family interpreter
    uses; it is neutral (`true`) on every other name.  The dispatch
    order is exactly that of `globalsInterp`. -/
def globalsDecodes (n : String) (args : List Value) : Bool :=
  if n ∈ allDiffNames then AllDiffCounting.allDiffDecodes n args
  else if n ∈ lexSortNames then LexSort.lexSortDecodes n args
  else if n ∈ packSchedNames then PackSched.packSchedDecodes n args
  else if n ∈ countingNames then Counting.countingDecodes n args
  else if n ∈ channelingNames then Channeling.channelingDecodes n args
  else if n ∈ setMathNames then SetMath.setMathDecodes n args
  else if n ∈ lexChainNames then LexChain.lexChainDecodes n args
  else if n ∈ graphNames then Graph.graphDecodes n args
  else if n ∈ regularNames then Regular.regularDecodes n args
  else if n ∈ sched2Names then Sched2.sched2Decodes n args
  else true

/-- **Full decodability**: the family decoder succeeds and, for the
    `regular` family, the signature's parameter positions satisfy the
    par condition the decoder's agreement proof needs (only `xs` and the
    trailing total-cost output may be variables).  The gate is `true`
    outside `regularNames`. -/
def fullDecodes (n : String) (params : List PredParamType) (args : List Value) : Bool :=
  globalsDecodes n args && Regular.regularGateParB n params

/-- `fullDecodes` is invariant under `ArgsAgree`: no separate parameter
    hypothesis is needed, because the regular gate is a Boolean conjunct
    of the conclusion.  When the gate fails, both sides are `false`. -/
theorem fullDecodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String) :
    fullDecodes n params vs = fullDecodes n params ws := by
  unfold fullDecodes
  cases hgate : Regular.regularGateParB n params with
  | false => simp [hgate]
  | true =>
    simp only [hgate, Bool.and_true]
    unfold globalsDecodes
    repeat' split
    all_goals
      first
      | exact AllDiffCounting.allDiffDecodes_agree h n
      | exact LexSort.lexSortDecodes_agree h n
      | exact PackSched.packSchedDecodes_agree h n
      | exact Counting.countingDecodes_agree h n
      | exact Channeling.channelingDecodes_agree h n
      | exact SetMath.setMathDecodes_agree h n
      | exact LexChain.lexChainDecodes_agree h n
      | exact Graph.graphDecodes_agree h n
      | exact Regular.regularDecodes_agree_gated h n hgate
      | exact Sched2.sched2Decodes_agree h n
      | rfl

/-! ### Family disjointness

Each supported name belongs to exactly one family.  These lemmas let
the master dispatch rewrite away the branches a name does not belong
to.  All proofs are by a `decide` on the closed goal obtained after
`rcases` on the family's literal name list. -/

/-- The all-different names are listed; the proof discharges the
    closed goal after substituting each listed name. -/
private theorem allDiff_not_lexSort {n : String} (h : n ∈ allDiffNames) :
    n ∉ lexSortNames := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem allDiff_not_packSched {n : String} (h : n ∈ allDiffNames) :
    n ∉ packSchedNames := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem allDiff_not_counting {n : String} (h : n ∈ allDiffNames) :
    n ∉ countingNames := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem allDiff_not_channeling {n : String} (h : n ∈ allDiffNames) :
    n ∉ channelingNames := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem allDiff_not_setMath {n : String} (h : n ∈ allDiffNames) :
    n ∉ setMathNames := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- No all-different name is in any other family's list. -/
theorem allDiff_not_other {n : String} (h : n ∈ allDiffNames) :
    n ∉ lexSortNames ∧ n ∉ packSchedNames ∧ n ∉ countingNames ∧
      n ∉ channelingNames ∧ n ∉ setMathNames :=
  ⟨allDiff_not_lexSort h, allDiff_not_packSched h, allDiff_not_counting h,
    allDiff_not_channeling h, allDiff_not_setMath h⟩

private theorem lexSort_not_allDiff {n : String} (h : n ∈ lexSortNames) :
    n ∉ allDiffNames := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals decide

private theorem lexSort_not_packSched {n : String} (h : n ∈ lexSortNames) :
    n ∉ packSchedNames := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals decide

private theorem lexSort_not_counting {n : String} (h : n ∈ lexSortNames) :
    n ∉ countingNames := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals decide

private theorem lexSort_not_channeling {n : String} (h : n ∈ lexSortNames) :
    n ∉ channelingNames := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals decide

private theorem lexSort_not_setMath {n : String} (h : n ∈ lexSortNames) :
    n ∉ setMathNames := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals decide

/-- No lex/sort name is in any other family's list. -/
theorem lexSort_not_other {n : String} (h : n ∈ lexSortNames) :
    n ∉ allDiffNames ∧ n ∉ packSchedNames ∧ n ∉ countingNames ∧
      n ∉ channelingNames ∧ n ∉ setMathNames :=
  ⟨lexSort_not_allDiff h, lexSort_not_packSched h, lexSort_not_counting h,
    lexSort_not_channeling h, lexSort_not_setMath h⟩

private theorem packSched_not_allDiff {n : String} (h : n ∈ packSchedNames) :
    n ∉ allDiffNames := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem packSched_not_lexSort {n : String} (h : n ∈ packSchedNames) :
    n ∉ lexSortNames := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem packSched_not_counting {n : String} (h : n ∈ packSchedNames) :
    n ∉ countingNames := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem packSched_not_channeling {n : String} (h : n ∈ packSchedNames) :
    n ∉ channelingNames := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem packSched_not_setMath {n : String} (h : n ∈ packSchedNames) :
    n ∉ setMathNames := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- No packing/scheduling name is in any other family's list. -/
theorem packSched_not_other {n : String} (h : n ∈ packSchedNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ countingNames ∧
      n ∉ channelingNames ∧ n ∉ setMathNames :=
  ⟨packSched_not_allDiff h, packSched_not_lexSort h, packSched_not_counting h,
    packSched_not_channeling h, packSched_not_setMath h⟩

private theorem counting_not_allDiff {n : String} (h : n ∈ countingNames) :
    n ∉ allDiffNames := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem counting_not_lexSort {n : String} (h : n ∈ countingNames) :
    n ∉ lexSortNames := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem counting_not_packSched {n : String} (h : n ∈ countingNames) :
    n ∉ packSchedNames := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem counting_not_channeling {n : String} (h : n ∈ countingNames) :
    n ∉ channelingNames := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem counting_not_setMath {n : String} (h : n ∈ countingNames) :
    n ∉ setMathNames := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- No counting name is in any other family's list. -/
theorem counting_not_other {n : String} (h : n ∈ countingNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ channelingNames ∧ n ∉ setMathNames :=
  ⟨counting_not_allDiff h, counting_not_lexSort h, counting_not_packSched h,
    counting_not_channeling h, counting_not_setMath h⟩

private theorem channeling_not_allDiff {n : String} (h : n ∈ channelingNames) :
    n ∉ allDiffNames := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals decide

private theorem channeling_not_lexSort {n : String} (h : n ∈ channelingNames) :
    n ∉ lexSortNames := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals decide

private theorem channeling_not_packSched {n : String}
    (h : n ∈ channelingNames) : n ∉ packSchedNames := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals decide

private theorem channeling_not_counting {n : String}
    (h : n ∈ channelingNames) : n ∉ countingNames := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals decide

private theorem channeling_not_setMath {n : String}
    (h : n ∈ channelingNames) : n ∉ setMathNames := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals decide

/-- No channeling name is in any other family's list. -/
theorem channeling_not_other {n : String} (h : n ∈ channelingNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ setMathNames :=
  ⟨channeling_not_allDiff h, channeling_not_lexSort h,
    channeling_not_packSched h, channeling_not_counting h,
    channeling_not_setMath h⟩

private theorem setMath_not_allDiff {n : String} (h : n ∈ setMathNames) :
    n ∉ allDiffNames := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals decide

private theorem setMath_not_lexSort {n : String} (h : n ∈ setMathNames) :
    n ∉ lexSortNames := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals decide

private theorem setMath_not_packSched {n : String} (h : n ∈ setMathNames) :
    n ∉ packSchedNames := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals decide

private theorem setMath_not_counting {n : String} (h : n ∈ setMathNames) :
    n ∉ countingNames := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals decide

private theorem setMath_not_channeling {n : String} (h : n ∈ setMathNames) :
    n ∉ channelingNames := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals decide

/-- No set/mathematical name is in any other family's list. -/
theorem setMath_not_other {n : String} (h : n ∈ setMathNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames :=
  ⟨setMath_not_allDiff h, setMath_not_lexSort h, setMath_not_packSched h,
    setMath_not_counting h, setMath_not_channeling h⟩

/-! ### Per-family dispatchers -/

/-- `allDiffInterpB` agrees with `allDiffInterp` on the all-different
    family names. -/
theorem globalsInterpB_alldiff_iff {n : String} {args : List Value}
    (hn : n ∈ allDiffNames) :
    AllDiffCounting.allDiffInterpB (Ident.mk n) args = true ↔
      AllDiffCounting.allDiffInterp (Ident.mk n) args := by
  simp only [allDiffNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      AllDiffCounting.fzn_all_different_int_iff,
      AllDiffCounting.fzn_all_different_set_iff,
      AllDiffCounting.fzn_all_disjoint_iff,
      AllDiffCounting.fzn_all_equal_int_iff,
      AllDiffCounting.fzn_all_equal_set_iff,
      AllDiffCounting.fzn_alldifferent_except_iff,
      AllDiffCounting.fzn_alldifferent_except_0_iff,
      AllDiffCounting.fzn_symmetric_all_different_iff]

/-- `lexSortInterpB` agrees with `lexSortInterp` on the lex/sort family
    names. -/
theorem globalsInterpB_lexsort_iff {n : String} {args : List Value}
    (hn : n ∈ lexSortNames) :
    LexSort.lexSortInterpB (Ident.mk n) args = true ↔
      LexSort.lexSortInterp (Ident.mk n) args := by
  simp only [lexSortNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals
    simp only [
      LexSort.fzn_lex_less_int_iff,
      LexSort.fzn_lex_lesseq_int_iff,
      LexSort.fzn_increasing_int_iff,
      LexSort.fzn_increasing_bool_iff,
      LexSort.fzn_strictly_increasing_int_iff,
      LexSort.fzn_sort_iff,
      LexSort.fzn_arg_sort_int_iff,
      LexSort.fzn_maximum_arg_int_iff,
      LexSort.fzn_minimum_arg_int_iff,
      LexSort.fzn_value_precede_int_iff,
      LexSort.fzn_value_precede_chain_int_iff,
      LexSort.fzn_seq_precede_chain_int_iff]

/-- `packSchedInterpB` agrees with `packSchedInterp` on the
    packing/scheduling family names. -/
theorem globalsInterpB_packsched_iff {n : String} {args : List Value}
    (hn : n ∈ packSchedNames) :
    PackSched.packSchedInterpB (Ident.mk n) args = true ↔
      PackSched.packSchedInterp (Ident.mk n) args := by
  simp only [packSchedNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      PackSched.bin_packing_iff,
      PackSched.bin_packing_capa_iff,
      PackSched.bin_packing_load_iff,
      PackSched.knapsack_iff,
      PackSched.diffn_iff,
      PackSched.diffn_nonstrict_iff,
      PackSched.geost_nonoverlap_k_iff,
      PackSched.disjunctive_iff,
      PackSched.disjunctive_strict_iff,
      PackSched.cumulative_iff,
      PackSched.table_int_iff,
      PackSched.if_then_else_int_iff,
      PackSched.if_then_else_bool_iff,
      PackSched.if_then_else_set_iff,
      PackSched.if_then_else_var_int_iff,
      PackSched.if_then_else_var_bool_iff,
      PackSched.if_then_else_var_set_iff]

/-- `countingInterpB` agrees with `countingInterp` on the counting
    family names. -/
theorem globalsInterpB_counting_iff {n : String} {args : List Value}
    (hn : n ∈ countingNames) :
    Counting.countingInterpB (Ident.mk n) args = true ↔
      Counting.countingInterp (Ident.mk n) args := by
  simp only [countingNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      Counting.fzn_nvalue_iff,
      Counting.fzn_among_iff,
      Counting.fzn_at_least_int_iff,
      Counting.fzn_at_most_int_iff,
      Counting.fzn_exactly_int_iff,
      Counting.fzn_count_eq_iff,
      Counting.fzn_count_eq_par_iff,
      Counting.fzn_count_geq_iff,
      Counting.fzn_count_geq_par_iff,
      Counting.fzn_count_gt_iff,
      Counting.fzn_count_gt_par_iff,
      Counting.fzn_count_leq_iff,
      Counting.fzn_count_leq_par_iff,
      Counting.fzn_count_lt_iff,
      Counting.fzn_count_lt_par_iff,
      Counting.fzn_count_neq_iff,
      Counting.fzn_count_neq_par_iff,
      Counting.fzn_distribute_iff,
      Counting.fzn_global_cardinality_iff,
      Counting.fzn_global_cardinality_closed_iff,
      Counting.fzn_global_cardinality_low_up_iff,
      Counting.fzn_global_cardinality_low_up_closed_iff,
      Counting.fzn_count_eq_set_iff,
      Counting.fzn_count_eq_set_par_iff,
      Counting.fzn_count_geq_set_iff,
      Counting.fzn_count_gt_set_iff,
      Counting.fzn_count_leq_set_iff,
      Counting.fzn_count_lt_set_iff,
      Counting.fzn_count_neq_set_iff,
      Counting.fzn_at_least_set_iff,
      Counting.fzn_at_most_set_iff,
      Counting.fzn_exactly_set_iff]

/-- `channelingInterpB` agrees with `channelingInterp` on the
    channeling family names. -/
theorem globalsInterpB_channeling_iff {n : String} {args : List Value}
    (hn : n ∈ channelingNames) :
    Channeling.channelingInterpB (Ident.mk n) args = true ↔
      Channeling.channelingInterp (Ident.mk n) args := by
  simp only [channelingNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals
    simp only [
      Channeling.fzn_inverse_iff,
      Channeling.fzn_inverse_in_range_iff,
      Channeling.fzn_int_set_channel_iff,
      Channeling.fzn_link_set_to_booleans_iff,
      Channeling.fzn_member_int_iff,
      Channeling.fzn_member_bool_iff,
      Channeling.fzn_member_set_iff,
      Channeling.fzn_arg_val_int_iff,
      Channeling.fzn_arg_val_bool_iff,
      Channeling.fzn_write_iff,
      Channeling.fzn_writes_iff]

/-- `setMathInterpB` agrees with `setMathInterp` on the set/mathematical
    family names. -/
theorem globalsInterpB_setmath_iff {n : String} {args : List Value}
    (hn : n ∈ setMathNames) :
    SetMath.setMathInterpB (Ident.mk n) args = true ↔
      SetMath.setMathInterp (Ident.mk n) args := by
  simp only [setMathNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    simp only [
      SetMath.fzn_disjoint_iff,
      SetMath.fzn_set_member_iff,
      SetMath.fzn_partition_set_iff,
      SetMath.fzn_at_most1_iff,
      SetMath.fzn_sum_set_iff,
      SetMath.fzn_sum_pred_iff,
      SetMath.fzn_range_iff,
      SetMath.fzn_roots_iff,
      SetMath.fzn_array_int_union_iff,
      SetMath.fzn_array_set_union_iff,
      SetMath.fzn_array_set_intersect_iff,
      SetMath.fzn_sliding_sum_iff,
      SetMath.fzn_sliding_among_int_iff,
      SetMath.fzn_sliding_among_bool_iff]

/-- `lexChainInterpB` agrees with `lexChainInterp` on the lex-chain family
    names. -/
theorem globalsInterpB_lexchain_iff {n : String} {args : List Value}
    (hn : n ∈ lexChainNames) :
    LexChain.lexChainInterpB (Ident.mk n) args = true ↔
      LexChain.lexChainInterp (Ident.mk n) args := by
  simp only [lexChainNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      LexChain.fzn_lex_greater_int_iff,
      LexChain.fzn_lex_greatereq_int_iff,
      LexChain.fzn_lex_chain_less_int_iff,
      LexChain.fzn_lex_chain_lesseq_int_iff,
      LexChain.fzn_lex2_iff,
      LexChain.fzn_strict_lex2_iff,
      LexChain.fzn_lex_chain_lesseq_orbitope_iff,
      LexChain.fzn_lex_chain_greater_int_iff,
      LexChain.fzn_lex_chain_greatereq_int_iff,
      LexChain.fzn_lex_chain_greatereq_orbitope_iff]

/-- `graphInterpB` agrees with `graphInterp` on the graph family
    names. -/
theorem globalsInterpB_graph_iff {n : String} {args : List Value}
    (hn : n ∈ graphNames) :
    Graph.graphInterpB (Ident.mk n) args = true ↔
      Graph.graphInterp (Ident.mk n) args := by
  simp only [graphNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      Graph.fzn_circuit_iff,
      Graph.fzn_subcircuit_iff,
      Graph.fzn_subgraph_iff,
      Graph.fzn_dag_iff,
      Graph.fzn_connected_iff,
      Graph.fzn_dconnected_iff,
      Graph.fzn_reachable_iff,
      Graph.fzn_dreachable_iff,
      Graph.fzn_tree_iff,
      Graph.fzn_dtree_iff,
      Graph.fzn_path_iff,
      Graph.fzn_dpath_iff,
      Graph.fzn_bounded_path_iff,
      Graph.fzn_bounded_dpath_iff,
      Graph.fzn_steiner_iff,
      Graph.fzn_dsteiner_iff,
      Graph.fzn_wst_iff,
      Graph.fzn_dwst_iff]

/-- `regularInterpB` agrees with `regularInterp` on the regular/mdd
    family names. -/
theorem globalsInterpB_regular_iff {n : String} {args : List Value}
    (hn : n ∈ regularNames) :
    Regular.regularInterpB (Ident.mk n) args = true ↔
      Regular.regularInterp (Ident.mk n) args := by
  simp only [regularNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      Regular.fzn_regular_iff,
      Regular.fzn_regular_nfa_iff,
      Regular.fzn_cost_regular_iff,
      Regular.fzn_mdd_iff,
      Regular.fzn_mdd_nondet_iff,
      Regular.fzn_cost_mdd_iff]

/-- `sched2InterpB` agrees with `sched2Interp` on the scheduling/
    remaining family names. -/
theorem globalsInterpB_sched2_iff {n : String} {args : List Value}
    (hn : n ∈ sched2Names) :
    Sched2.sched2InterpB (Ident.mk n) args = true ↔
      Sched2.sched2Interp (Ident.mk n) args := by
  simp only [sched2Names, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [
      Sched2.fzn_cumulatives_iff,
      Sched2.fzn_cumulatives_decomp_iff,
      Sched2.fzn_geost_iff,
      Sched2.fzn_geost_bb_iff,
      Sched2.fzn_geost_smallest_bb_iff,
      Sched2.fzn_diffn_nonoverlap_k_iff,
      Sched2.fzn_diffn_k_iff,
      Sched2.fzn_diffn_nonstrict_k_iff,
      Sched2.fzn_writes_seq_iff,
      Sched2.fzn_if_then_else_partiality_iff]


/-! ### New-family disjointness -/

private theorem lexChain_not_other {n : String} (h : n ∈ lexChainNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames ∧ n ∉ setMathNames ∧
      n ∉ graphNames ∧ n ∉ regularNames ∧ n ∉ sched2Names := by
  simp only [lexChainNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem graph_not_other {n : String} (h : n ∈ graphNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames ∧ n ∉ setMathNames ∧
      n ∉ lexChainNames ∧ n ∉ regularNames ∧ n ∉ sched2Names := by
  simp only [graphNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem regular_not_other {n : String} (h : n ∈ regularNames) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames ∧ n ∉ setMathNames ∧
      n ∉ lexChainNames ∧ n ∉ graphNames ∧ n ∉ sched2Names := by
  simp only [regularNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem sched2_not_other {n : String} (h : n ∈ sched2Names) :
    n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames ∧ n ∉ setMathNames ∧
      n ∉ lexChainNames ∧ n ∉ graphNames ∧ n ∉ regularNames := by
  simp only [sched2Names, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Any new-family non-membership package that covers the six old
    families contradicts membership in one of them. -/
private theorem false_of_old_of_not_old {n : String}
    (hold : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames)
    (hnot : n ∉ allDiffNames ∧ n ∉ lexSortNames ∧ n ∉ packSchedNames ∧
      n ∉ countingNames ∧ n ∉ channelingNames ∧ n ∉ setMathNames) :
    False := by
  rcases hold with h | h | h | h | h | h
  · exact hnot.1 h
  · exact hnot.2.1 h
  · exact hnot.2.2.1 h
  · exact hnot.2.2.2.1 h
  · exact hnot.2.2.2.2.1 h
  · exact hnot.2.2.2.2.2 h

/-- No old-family name is in any of the four new lists: each new family's
    `not_other` lemma already establishes all six old non-memberships, so
    this is pure plumbing with no per-name deciding. -/
private theorem old_not_new {n : String}
    (h : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames) :
    n ∉ lexChainNames ∧ n ∉ graphNames ∧ n ∉ regularNames ∧
      n ∉ sched2Names := by
  refine ⟨fun hf => false_of_old_of_not_old h ⟨(lexChain_not_other hf).1,
    (lexChain_not_other hf).2.1, (lexChain_not_other hf).2.2.1,
    (lexChain_not_other hf).2.2.2.1, (lexChain_not_other hf).2.2.2.2.1,
    (lexChain_not_other hf).2.2.2.2.2.1⟩, ?_, ?_, ?_⟩
  · exact fun hf => false_of_old_of_not_old h ⟨(graph_not_other hf).1,
      (graph_not_other hf).2.1, (graph_not_other hf).2.2.1,
      (graph_not_other hf).2.2.2.1, (graph_not_other hf).2.2.2.2.1,
      (graph_not_other hf).2.2.2.2.2.1⟩
  · exact fun hf => false_of_old_of_not_old h ⟨(regular_not_other hf).1,
      (regular_not_other hf).2.1, (regular_not_other hf).2.2.1,
      (regular_not_other hf).2.2.2.1, (regular_not_other hf).2.2.2.2.1,
      (regular_not_other hf).2.2.2.2.2.1⟩
  · exact fun hf => false_of_old_of_not_old h ⟨(sched2_not_other hf).1,
      (sched2_not_other hf).2.1, (sched2_not_other hf).2.2.1,
      (sched2_not_other hf).2.2.2.1, (sched2_not_other hf).2.2.2.2.1,
      (sched2_not_other hf).2.2.2.2.2.1⟩

/-! ### The master agreement theorem -/

/-- Re-associate a left-nested 10-way disjunction into the right-nested
    form (simp's normal form is left-nested for Or-chains). -/
private theorem or10_assoc {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Prop}
    (h : ((((((((a1 ∨ a2) ∨ a3) ∨ a4) ∨ a5) ∨ a6) ∨ a7) ∨ a8) ∨ a9) ∨ a10) :
    a1 ∨ a2 ∨ a3 ∨ a4 ∨ a5 ∨ a6 ∨ a7 ∨ a8 ∨ a9 ∨ a10 := by
  induction h with
  | inl h9 =>
    induction h9 with
    | inl h8 =>
      induction h8 with
      | inl h7 =>
        induction h7 with
        | inl h6 =>
          induction h6 with
          | inl h5 =>
            induction h5 with
            | inl h4 =>
              induction h4 with
              | inl h3 =>
                induction h3 with
                | inl h2 =>
                  induction h2 with
                  | inl h1 => exact Or.inl h1
                  | inr h2 => exact Or.inr (Or.inl h2)
                | inr h3 => exact Or.inr (Or.inr (Or.inl h3))
              | inr h4 => exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
            | inr h5 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
          | inr h6 =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
        | inr h7 =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl h7))))))
      | inr h8 =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl h8)))))))
    | inr h9 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h9))))))))
  | inr h10 =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr h10))))))))

/-- Re-associate a left-nested 11-way disjunction into the right-nested
    form. -/
private theorem or11_assoc {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Prop}
    (h : (((((((((a1 ∨ a2) ∨ a3) ∨ a4) ∨ a5) ∨ a6) ∨ a7) ∨ a8) ∨ a9) ∨ a10) ∨ a11) :
    a1 ∨ a2 ∨ a3 ∨ a4 ∨ a5 ∨ a6 ∨ a7 ∨ a8 ∨ a9 ∨ a10 ∨ a11 := by
  cases h with
  | inl h10 =>
      rcases or10_assoc h10 with h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h)))))))))
  | inr h11 =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr h11)))))))))

/-- **Master agreement**: on every supported global-constraint name,
    the combined Boolean twin `globalsInterpB` is `true` exactly when
    the combined mathematical interpretation `globalsInterp`
    holds. -/
theorem globalsInterpB_iff {n : String} {args : List Value}
    (hn : n ∈ globalsNames) :
    globalsInterpB (Ident.mk n) args = true ↔ globalsInterp (Ident.mk n) args := by
  have hsplit : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames ∨
      n ∈ lexChainNames ∨ n ∈ graphNames ∨ n ∈ regularNames ∨
      n ∈ sched2Names := by
    rw [show globalsNames = allDiffNames ++ lexSortNames ++ packSchedNames ++
      countingNames ++ channelingNames ++ setMathNames ++ lexChainNames ++
      graphNames ++ regularNames ++ sched2Names from rfl] at hn
    simp only [List.mem_append] at hn
    exact or10_assoc hn
  rcases hsplit with h | h | h | h | h | h | h | h | h | h
  · simp only [globalsInterpB, globalsInterp, if_pos h]
    exact globalsInterpB_alldiff_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := lexSort_not_other h
    obtain ⟨h6, h7, h8, h9⟩ := old_not_new (Or.inr (Or.inl h))
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_lexsort_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := packSched_not_other h
    obtain ⟨h6, h7, h8, h9⟩ := old_not_new (Or.inr (Or.inr (Or.inl h)))
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_packsched_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := counting_not_other h
    obtain ⟨h6, h7, h8, h9⟩ :=
      old_not_new (Or.inr (Or.inr (Or.inr (Or.inl h))))
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_counting_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := channeling_not_other h
    obtain ⟨h6, h7, h8, h9⟩ :=
      old_not_new (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_channeling_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := setMath_not_other h
    obtain ⟨h6, h7, h8, h9⟩ :=
      old_not_new (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_setmath_iff h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := lexChain_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_pos h]
    exact globalsInterpB_lexchain_iff h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := graph_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h]
    exact globalsInterpB_graph_iff h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := regular_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h]
    exact globalsInterpB_regular_iff h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := sched2_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    exact globalsInterpB_sched2_iff h

/-! ## The combined standard-plus-globals interpretation

`fullInterp` interprets every predicate of the full signature
`fullSig`: the 138 `fzn_*` global-constraint names via `globalsInterp`,
every other name via the standard library interpretation
`stdInterp`.  Its executable twin `fullInterpB` dispatches likewise:
`fzn_*` names to `globalsInterpB`, everything else to
`Solution.interpB` (which itself decides the extensional set
predicates and delegates the rest to `stdInterpB`). -/

/-- The combined interpretation of the full fragment: global
    constraints by their family interpretation, standard predicates by
    `stdInterp`. -/
def fullInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  if x.name ∈ globalsNames then globalsInterp x else LeanFzn.Semantics.stdInterp x

/-- **Executable twin of `fullInterp`**. -/
def fullInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  if x.name ∈ globalsNames then globalsInterpB x
  else LeanFzn.Semantics.Evaluation.interpB x

/-- The names of every predicate with an executable, verified twin in
    the combined fragment: the global-constraint names plus the
    standard-library names (including the extensional set predicates). -/
def fullCheckableNames : List String :=
  globalsNames ++ LeanFzn.Semantics.Evaluation.checkableNames

/-! ### Agreement of the combined twin -/

/-- The full twin agrees with the full interpretation on
    global-constraint names (via the master agreement). -/
private theorem fullInterpB_globals_iff {n : String} {args : List Value}
    (h : n ∈ globalsNames) :
    fullInterpB (Ident.mk n) args = true ↔ fullInterp (Ident.mk n) args := by
  simp only [fullInterpB, fullInterp, if_pos h]
  exact globalsInterpB_iff h

/-- The full twin agrees with the full interpretation on
    standard-library names (via `Solution.interpB`, which agrees with
    `stdInterp` there). -/
private theorem fullInterpB_std_iff {n : String} {args : List Value}
    (h : n ∈ LeanFzn.Semantics.Evaluation.checkableNames) (hne : n ∉ globalsNames) :
    fullInterpB (Ident.mk n) args = true ↔ fullInterp (Ident.mk n) args := by
  simp only [fullInterpB, fullInterp, if_neg hne]
  rw [LeanFzn.Semantics.Evaluation.checkableNames, List.mem_append] at h
  rcases h with h | h
  · exact LeanFzn.Semantics.Evaluation.interpB_std_iff h
  · exact LeanFzn.Semantics.Evaluation.interpB_set_iff h

/-- Every checkable standard-library name is outside the ten family
    name lists (no standard name starts with `fzn_`; each family list
    contains only such names). -/
theorem std_name_not_global {n : String}
    (h : n ∈ LeanFzn.Semantics.Evaluation.checkableNames) : n ∉ globalsNames := by
  intro hmem
  rw [LeanFzn.Semantics.Evaluation.checkableNames, List.mem_append] at h
  rcases h with h | h
  · -- standard names: none equals any of the 138 fzn_* names
    simp only [LeanFzn.Semantics.Evaluation.stdNames, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact absurd hmem (by decide)
  · simp only [LeanFzn.Semantics.Evaluation.setNames, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact absurd hmem (by decide)

/-- **Agreement of the combined twin**: for every checkable name, the
    full Boolean twin is `true` exactly when the full interpretation
    holds. -/
theorem fullInterpB_iff {n : String} {args : List Value}
    (h : n ∈ fullCheckableNames) :
    fullInterpB (Ident.mk n) args = true ↔ fullInterp (Ident.mk n) args := by
  rw [fullCheckableNames, List.mem_append] at h
  rcases h with h | h
  · exact fullInterpB_globals_iff h
  · exact fullInterpB_std_iff h (std_name_not_global h)

/-! ### Verified fast dispatch (PLAN item 4)

`fullInterpB` dispatches a constraint call by testing `x.name ∈
globalsNames` and then walking a chain of ten family-list membership
tests (138 `fzn_*` names plus 61+19 standard names in
`fullCheckableNames`) — O(#names) string comparisons per call.  The
fast twin below builds a `Std.HashMap String (Ident → List Value →
Bool)` once, from the *list variables themselves* (each family's names
mapped to its family twin, the standard names to
`Solution.interpB`), so adding a name to a family list automatically
extends the map.  `preparedInterpB` looks up the constraint's name in
the map and applies the result; `preparedInterpB_iff` proves the
returned `Bool` agrees with `fullInterpB` on exactly
`fullCheckableNames` (equality of returned `Bool`s per `(name, args)`;
the function values stored in the map are not themselves comparable),
so consumers that gate on membership (as `checkModelSolution` does
through `firstUnsupported`) inherit `fullInterpB_iff` unchanged. -/

/-! ### Name-list disjointness machinery

The 138 global-constraint names are duplicate-free: each family list is
decided duplicate-free on its own (a small quadratic-in-family decide
instead of one quadratic-in-217 decide, which the kernel evaluates much
more slowly), and the families are pairwise disjoint by the per-family
`not_other` / `X_not_Y` lemmas above, reassembled here as uniform
pairwise facts.  A fold over the family list combines the pieces with
`List.nodup_append`. -/

/-- Membership in a foldr-concatenation of a family list. -/
private theorem mem_foldr_append {ls : List (List String)} {a : String}
    (h : a ∈ ls.foldr (fun (l r : List String) => l ++ r) []) :
    ∃ x ∈ ls, a ∈ x := by
  induction ls with
  | nil => cases h
  | cons x xs ih =>
      simp only [List.foldr_cons, List.mem_append] at h
      rcases h with h | h
      · exact ⟨x, List.mem_cons_self, h⟩
      · obtain ⟨y, hy, hay⟩ := ih h
        exact ⟨y, List.mem_cons_of_mem _ hy, hay⟩

/-- A foldr-concatenation is Nodup when each family is Nodup, the family
    list itself is Nodup (no family repeats), and any two distinct
    families are pointwise-disjoint. -/
private theorem nodup_foldr_append {ls : List (List String)}
    (hnd : ls.Nodup)
    (hfam : ∀ x ∈ ls, x.Nodup)
    (hdisj : ∀ x ∈ ls, ∀ y ∈ ls, x ≠ y → ∀ a ∈ x, a ∉ y) :
    (ls.foldr (fun (l r : List String) => l ++ r) []).Nodup := by
  induction ls with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hxs : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hfx : ∀ y ∈ xs, y.Nodup := fun y hy =>
        hfam y (List.mem_cons_of_mem _ hy)
      have hfdj : ∀ u ∈ xs, ∀ v ∈ xs, u ≠ v → ∀ a ∈ u, a ∉ v := fun u hu v hv huv a ha =>
        hdisj u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv) huv a ha
      simp only [List.foldr_cons]
      refine List.nodup_append.mpr ⟨hfam x List.mem_cons_self,
        ih hxs hfx hfdj, ?_⟩
      intro a ha b hb heq
      obtain ⟨y, hy, hby⟩ := mem_foldr_append (ls := xs) hb
      by_cases hxy : x = y
      · exact absurd (hxy ▸ hy) (List.nodup_cons.mp hnd).1
      · exact hdisj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hxy a ha (heq ▸ hby)

/-- Uniform pairwise facts between the ten family name lists: `X_ne_Y`
    states that no name of family `X` is in family `Y` (both orders
    exist for every pair).  Old-to-old pairs come from the per-pair
    lemmas above; new-to-anything from the `not_other` bundles; old-to-new
    by contraposition of the new family's bundle. -/

private theorem allDiff_ne_lexSort : ∀ a ∈ allDiffNames, a ∉ lexSortNames :=
  fun _ ha => allDiff_not_lexSort ha
private theorem allDiff_ne_packSched : ∀ a ∈ allDiffNames, a ∉ packSchedNames :=
  fun _ ha => allDiff_not_packSched ha
private theorem allDiff_ne_counting : ∀ a ∈ allDiffNames, a ∉ countingNames :=
  fun _ ha => allDiff_not_counting ha
private theorem allDiff_ne_channeling : ∀ a ∈ allDiffNames, a ∉ channelingNames :=
  fun _ ha => allDiff_not_channeling ha
private theorem allDiff_ne_setMath : ∀ a ∈ allDiffNames, a ∉ setMathNames :=
  fun _ ha => allDiff_not_setMath ha
private theorem allDiff_ne_lexChain : ∀ a ∈ allDiffNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inl ha)
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem allDiff_ne_graph : ∀ a ∈ allDiffNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inl ha)
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem allDiff_ne_regular : ∀ a ∈ allDiffNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inl ha)
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem allDiff_ne_sched2 : ∀ a ∈ allDiffNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inl ha)
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem lexSort_ne_allDiff : ∀ a ∈ lexSortNames, a ∉ allDiffNames :=
  fun _ ha => lexSort_not_allDiff ha
private theorem lexSort_ne_packSched : ∀ a ∈ lexSortNames, a ∉ packSchedNames :=
  fun _ ha => lexSort_not_packSched ha
private theorem lexSort_ne_counting : ∀ a ∈ lexSortNames, a ∉ countingNames :=
  fun _ ha => lexSort_not_counting ha
private theorem lexSort_ne_channeling : ∀ a ∈ lexSortNames, a ∉ channelingNames :=
  fun _ ha => lexSort_not_channeling ha
private theorem lexSort_ne_setMath : ∀ a ∈ lexSortNames, a ∉ setMathNames :=
  fun _ ha => lexSort_not_setMath ha
private theorem lexSort_ne_lexChain : ∀ a ∈ lexSortNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inl ha))
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem lexSort_ne_graph : ∀ a ∈ lexSortNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inl ha))
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem lexSort_ne_regular : ∀ a ∈ lexSortNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inl ha))
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem lexSort_ne_sched2 : ∀ a ∈ lexSortNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inl ha))
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem packSched_ne_allDiff : ∀ a ∈ packSchedNames, a ∉ allDiffNames :=
  fun _ ha => packSched_not_allDiff ha
private theorem packSched_ne_lexSort : ∀ a ∈ packSchedNames, a ∉ lexSortNames :=
  fun _ ha => packSched_not_lexSort ha
private theorem packSched_ne_counting : ∀ a ∈ packSchedNames, a ∉ countingNames :=
  fun _ ha => packSched_not_counting ha
private theorem packSched_ne_channeling : ∀ a ∈ packSchedNames, a ∉ channelingNames :=
  fun _ ha => packSched_not_channeling ha
private theorem packSched_ne_setMath : ∀ a ∈ packSchedNames, a ∉ setMathNames :=
  fun _ ha => packSched_not_setMath ha
private theorem packSched_ne_lexChain : ∀ a ∈ packSchedNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inl ha)))
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem packSched_ne_graph : ∀ a ∈ packSchedNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inl ha)))
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem packSched_ne_regular : ∀ a ∈ packSchedNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inl ha)))
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem packSched_ne_sched2 : ∀ a ∈ packSchedNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inl ha)))
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem counting_ne_allDiff : ∀ a ∈ countingNames, a ∉ allDiffNames :=
  fun _ ha => counting_not_allDiff ha
private theorem counting_ne_lexSort : ∀ a ∈ countingNames, a ∉ lexSortNames :=
  fun _ ha => counting_not_lexSort ha
private theorem counting_ne_packSched : ∀ a ∈ countingNames, a ∉ packSchedNames :=
  fun _ ha => counting_not_packSched ha
private theorem counting_ne_channeling : ∀ a ∈ countingNames, a ∉ channelingNames :=
  fun _ ha => counting_not_channeling ha
private theorem counting_ne_setMath : ∀ a ∈ countingNames, a ∉ setMathNames :=
  fun _ ha => counting_not_setMath ha
private theorem counting_ne_lexChain : ∀ a ∈ countingNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem counting_ne_graph : ∀ a ∈ countingNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem counting_ne_regular : ∀ a ∈ countingNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem counting_ne_sched2 : ∀ a ∈ countingNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem channeling_ne_allDiff : ∀ a ∈ channelingNames, a ∉ allDiffNames :=
  fun _ ha => channeling_not_allDiff ha
private theorem channeling_ne_lexSort : ∀ a ∈ channelingNames, a ∉ lexSortNames :=
  fun _ ha => channeling_not_lexSort ha
private theorem channeling_ne_packSched : ∀ a ∈ channelingNames, a ∉ packSchedNames :=
  fun _ ha => channeling_not_packSched ha
private theorem channeling_ne_counting : ∀ a ∈ channelingNames, a ∉ countingNames :=
  fun _ ha => channeling_not_counting ha
private theorem channeling_ne_setMath : ∀ a ∈ channelingNames, a ∉ setMathNames :=
  fun _ ha => channeling_not_setMath ha
private theorem channeling_ne_lexChain : ∀ a ∈ channelingNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem channeling_ne_graph : ∀ a ∈ channelingNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem channeling_ne_regular : ∀ a ∈ channelingNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem channeling_ne_sched2 : ∀ a ∈ channelingNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem setMath_ne_allDiff : ∀ a ∈ setMathNames, a ∉ allDiffNames :=
  fun _ ha => setMath_not_allDiff ha
private theorem setMath_ne_lexSort : ∀ a ∈ setMathNames, a ∉ lexSortNames :=
  fun _ ha => setMath_not_lexSort ha
private theorem setMath_ne_packSched : ∀ a ∈ setMathNames, a ∉ packSchedNames :=
  fun _ ha => setMath_not_packSched ha
private theorem setMath_ne_counting : ∀ a ∈ setMathNames, a ∉ countingNames :=
  fun _ ha => setMath_not_counting ha
private theorem setMath_ne_channeling : ∀ a ∈ setMathNames, a ∉ channelingNames :=
  fun _ ha => setMath_not_channeling ha
private theorem setMath_ne_lexChain : ∀ a ∈ setMathNames, a ∉ lexChainNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ha))))))
      ⟨(lexChain_not_other hmem).1, (lexChain_not_other hmem).2.1, (lexChain_not_other hmem).2.2.1,
      (lexChain_not_other hmem).2.2.2.1, (lexChain_not_other hmem).2.2.2.2.1, (lexChain_not_other hmem).2.2.2.2.2.1⟩
private theorem setMath_ne_graph : ∀ a ∈ setMathNames, a ∉ graphNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ha))))))
      ⟨(graph_not_other hmem).1, (graph_not_other hmem).2.1, (graph_not_other hmem).2.2.1,
      (graph_not_other hmem).2.2.2.1, (graph_not_other hmem).2.2.2.2.1, (graph_not_other hmem).2.2.2.2.2.1⟩
private theorem setMath_ne_regular : ∀ a ∈ setMathNames, a ∉ regularNames :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ha))))))
      ⟨(regular_not_other hmem).1, (regular_not_other hmem).2.1, (regular_not_other hmem).2.2.1,
      (regular_not_other hmem).2.2.2.1, (regular_not_other hmem).2.2.2.2.1, (regular_not_other hmem).2.2.2.2.2.1⟩
private theorem setMath_ne_sched2 : ∀ a ∈ setMathNames, a ∉ sched2Names :=
  fun _ ha hmem =>
    false_of_old_of_not_old (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ha))))))
      ⟨(sched2_not_other hmem).1, (sched2_not_other hmem).2.1, (sched2_not_other hmem).2.2.1,
      (sched2_not_other hmem).2.2.2.1, (sched2_not_other hmem).2.2.2.2.1, (sched2_not_other hmem).2.2.2.2.2.1⟩
private theorem lexChain_ne_allDiff : ∀ a ∈ lexChainNames, a ∉ allDiffNames :=
  fun _ ha => (lexChain_not_other ha).1
private theorem lexChain_ne_lexSort : ∀ a ∈ lexChainNames, a ∉ lexSortNames :=
  fun _ ha => (lexChain_not_other ha).2.1
private theorem lexChain_ne_packSched : ∀ a ∈ lexChainNames, a ∉ packSchedNames :=
  fun _ ha => (lexChain_not_other ha).2.2.1
private theorem lexChain_ne_counting : ∀ a ∈ lexChainNames, a ∉ countingNames :=
  fun _ ha => (lexChain_not_other ha).2.2.2.1
private theorem lexChain_ne_channeling : ∀ a ∈ lexChainNames, a ∉ channelingNames :=
  fun _ ha => (lexChain_not_other ha).2.2.2.2.1
private theorem lexChain_ne_setMath : ∀ a ∈ lexChainNames, a ∉ setMathNames :=
  fun _ ha => (lexChain_not_other ha).2.2.2.2.2.1
private theorem lexChain_ne_graph : ∀ a ∈ lexChainNames, a ∉ graphNames :=
  fun _ ha => (lexChain_not_other ha).2.2.2.2.2.2.1
private theorem lexChain_ne_regular : ∀ a ∈ lexChainNames, a ∉ regularNames :=
  fun _ ha => (lexChain_not_other ha).2.2.2.2.2.2.2.1
private theorem lexChain_ne_sched2 : ∀ a ∈ lexChainNames, a ∉ sched2Names :=
  fun _ ha => (lexChain_not_other ha).2.2.2.2.2.2.2.2
private theorem graph_ne_allDiff : ∀ a ∈ graphNames, a ∉ allDiffNames :=
  fun _ ha => (graph_not_other ha).1
private theorem graph_ne_lexSort : ∀ a ∈ graphNames, a ∉ lexSortNames :=
  fun _ ha => (graph_not_other ha).2.1
private theorem graph_ne_packSched : ∀ a ∈ graphNames, a ∉ packSchedNames :=
  fun _ ha => (graph_not_other ha).2.2.1
private theorem graph_ne_counting : ∀ a ∈ graphNames, a ∉ countingNames :=
  fun _ ha => (graph_not_other ha).2.2.2.1
private theorem graph_ne_channeling : ∀ a ∈ graphNames, a ∉ channelingNames :=
  fun _ ha => (graph_not_other ha).2.2.2.2.1
private theorem graph_ne_setMath : ∀ a ∈ graphNames, a ∉ setMathNames :=
  fun _ ha => (graph_not_other ha).2.2.2.2.2.1
private theorem graph_ne_lexChain : ∀ a ∈ graphNames, a ∉ lexChainNames :=
  fun _ ha => (graph_not_other ha).2.2.2.2.2.2.1
private theorem graph_ne_regular : ∀ a ∈ graphNames, a ∉ regularNames :=
  fun _ ha => (graph_not_other ha).2.2.2.2.2.2.2.1
private theorem graph_ne_sched2 : ∀ a ∈ graphNames, a ∉ sched2Names :=
  fun _ ha => (graph_not_other ha).2.2.2.2.2.2.2.2
private theorem regular_ne_allDiff : ∀ a ∈ regularNames, a ∉ allDiffNames :=
  fun _ ha => (regular_not_other ha).1
private theorem regular_ne_lexSort : ∀ a ∈ regularNames, a ∉ lexSortNames :=
  fun _ ha => (regular_not_other ha).2.1
private theorem regular_ne_packSched : ∀ a ∈ regularNames, a ∉ packSchedNames :=
  fun _ ha => (regular_not_other ha).2.2.1
private theorem regular_ne_counting : ∀ a ∈ regularNames, a ∉ countingNames :=
  fun _ ha => (regular_not_other ha).2.2.2.1
private theorem regular_ne_channeling : ∀ a ∈ regularNames, a ∉ channelingNames :=
  fun _ ha => (regular_not_other ha).2.2.2.2.1
private theorem regular_ne_setMath : ∀ a ∈ regularNames, a ∉ setMathNames :=
  fun _ ha => (regular_not_other ha).2.2.2.2.2.1
private theorem regular_ne_lexChain : ∀ a ∈ regularNames, a ∉ lexChainNames :=
  fun _ ha => (regular_not_other ha).2.2.2.2.2.2.1
private theorem regular_ne_graph : ∀ a ∈ regularNames, a ∉ graphNames :=
  fun _ ha => (regular_not_other ha).2.2.2.2.2.2.2.1
private theorem regular_ne_sched2 : ∀ a ∈ regularNames, a ∉ sched2Names :=
  fun _ ha => (regular_not_other ha).2.2.2.2.2.2.2.2
private theorem sched2_ne_allDiff : ∀ a ∈ sched2Names, a ∉ allDiffNames :=
  fun _ ha => (sched2_not_other ha).1
private theorem sched2_ne_lexSort : ∀ a ∈ sched2Names, a ∉ lexSortNames :=
  fun _ ha => (sched2_not_other ha).2.1
private theorem sched2_ne_packSched : ∀ a ∈ sched2Names, a ∉ packSchedNames :=
  fun _ ha => (sched2_not_other ha).2.2.1
private theorem sched2_ne_counting : ∀ a ∈ sched2Names, a ∉ countingNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.1
private theorem sched2_ne_channeling : ∀ a ∈ sched2Names, a ∉ channelingNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.2.1
private theorem sched2_ne_setMath : ∀ a ∈ sched2Names, a ∉ setMathNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.2.2.1
private theorem sched2_ne_lexChain : ∀ a ∈ sched2Names, a ∉ lexChainNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.2.2.2.1
private theorem sched2_ne_graph : ∀ a ∈ sched2Names, a ∉ graphNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.2.2.2.2.1
private theorem sched2_ne_regular : ∀ a ∈ sched2Names, a ∉ regularNames :=
  fun _ ha => (sched2_not_other ha).2.2.2.2.2.2.2.2

/-- Each family's name list is duplicate-free (small per-family decides,
    far cheaper than one decide over the full 138-name concatenation). -/
private theorem allDiff_nodup : allDiffNames.Nodup := by decide
private theorem lexSort_nodup : lexSortNames.Nodup := by decide
private theorem packSched_nodup : packSchedNames.Nodup := by decide
private theorem counting_nodup : countingNames.Nodup := by decide
private theorem channeling_nodup : channelingNames.Nodup := by decide
private theorem setMath_nodup : setMathNames.Nodup := by decide
private theorem lexChain_nodup : lexChainNames.Nodup := by decide
private theorem graph_nodup : graphNames.Nodup := by decide
private theorem regular_nodup : regularNames.Nodup := by decide
private theorem sched2_nodup : sched2Names.Nodup := by decide

/-- The ten family lists are pairwise-distinct values. -/
private theorem fams_nodup :
    [allDiffNames, lexSortNames, packSchedNames, countingNames,
     channelingNames, setMathNames, lexChainNames, graphNames,
     regularNames, sched2Names].Nodup := by decide

private theorem fams_disj : ∀ x ∈ [allDiffNames, lexSortNames,
    packSchedNames, countingNames, channelingNames, setMathNames,
    lexChainNames, graphNames, regularNames, sched2Names],
    ∀ y ∈ [allDiffNames, lexSortNames, packSchedNames, countingNames,
    channelingNames, setMathNames, lexChainNames, graphNames,
    regularNames, sched2Names],
    x ≠ y → ∀ a ∈ x, a ∉ y := by
  intro x hx y hy hxy a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact allDiff_ne_lexSort a ha
    · exact allDiff_ne_packSched a ha
    · exact allDiff_ne_counting a ha
    · exact allDiff_ne_channeling a ha
    · exact allDiff_ne_setMath a ha
    · exact allDiff_ne_lexChain a ha
    · exact allDiff_ne_graph a ha
    · exact allDiff_ne_regular a ha
    · exact allDiff_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lexSort_ne_allDiff a ha
    · exact absurd rfl hxy
    · exact lexSort_ne_packSched a ha
    · exact lexSort_ne_counting a ha
    · exact lexSort_ne_channeling a ha
    · exact lexSort_ne_setMath a ha
    · exact lexSort_ne_lexChain a ha
    · exact lexSort_ne_graph a ha
    · exact lexSort_ne_regular a ha
    · exact lexSort_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact packSched_ne_allDiff a ha
    · exact packSched_ne_lexSort a ha
    · exact absurd rfl hxy
    · exact packSched_ne_counting a ha
    · exact packSched_ne_channeling a ha
    · exact packSched_ne_setMath a ha
    · exact packSched_ne_lexChain a ha
    · exact packSched_ne_graph a ha
    · exact packSched_ne_regular a ha
    · exact packSched_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact counting_ne_allDiff a ha
    · exact counting_ne_lexSort a ha
    · exact counting_ne_packSched a ha
    · exact absurd rfl hxy
    · exact counting_ne_channeling a ha
    · exact counting_ne_setMath a ha
    · exact counting_ne_lexChain a ha
    · exact counting_ne_graph a ha
    · exact counting_ne_regular a ha
    · exact counting_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact channeling_ne_allDiff a ha
    · exact channeling_ne_lexSort a ha
    · exact channeling_ne_packSched a ha
    · exact channeling_ne_counting a ha
    · exact absurd rfl hxy
    · exact channeling_ne_setMath a ha
    · exact channeling_ne_lexChain a ha
    · exact channeling_ne_graph a ha
    · exact channeling_ne_regular a ha
    · exact channeling_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact setMath_ne_allDiff a ha
    · exact setMath_ne_lexSort a ha
    · exact setMath_ne_packSched a ha
    · exact setMath_ne_counting a ha
    · exact setMath_ne_channeling a ha
    · exact absurd rfl hxy
    · exact setMath_ne_lexChain a ha
    · exact setMath_ne_graph a ha
    · exact setMath_ne_regular a ha
    · exact setMath_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lexChain_ne_allDiff a ha
    · exact lexChain_ne_lexSort a ha
    · exact lexChain_ne_packSched a ha
    · exact lexChain_ne_counting a ha
    · exact lexChain_ne_channeling a ha
    · exact lexChain_ne_setMath a ha
    · exact absurd rfl hxy
    · exact lexChain_ne_graph a ha
    · exact lexChain_ne_regular a ha
    · exact lexChain_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact graph_ne_allDiff a ha
    · exact graph_ne_lexSort a ha
    · exact graph_ne_packSched a ha
    · exact graph_ne_counting a ha
    · exact graph_ne_channeling a ha
    · exact graph_ne_setMath a ha
    · exact graph_ne_lexChain a ha
    · exact absurd rfl hxy
    · exact graph_ne_regular a ha
    · exact graph_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact regular_ne_allDiff a ha
    · exact regular_ne_lexSort a ha
    · exact regular_ne_packSched a ha
    · exact regular_ne_counting a ha
    · exact regular_ne_channeling a ha
    · exact regular_ne_setMath a ha
    · exact regular_ne_lexChain a ha
    · exact regular_ne_graph a ha
    · exact absurd rfl hxy
    · exact regular_ne_sched2 a ha
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sched2_ne_allDiff a ha
    · exact sched2_ne_lexSort a ha
    · exact sched2_ne_packSched a ha
    · exact sched2_ne_counting a ha
    · exact sched2_ne_channeling a ha
    · exact sched2_ne_setMath a ha
    · exact sched2_ne_lexChain a ha
    · exact sched2_ne_graph a ha
    · exact sched2_ne_regular a ha
    · exact absurd rfl hxy

/-- The 138 supported names are duplicate-free. -/
private theorem globalsNames_nodup : globalsNames.Nodup := by
  have hf : ∀ x ∈ [allDiffNames, lexSortNames, packSchedNames,
      countingNames, channelingNames, setMathNames, lexChainNames,
      graphNames, regularNames, sched2Names], x.Nodup := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact allDiff_nodup
    · exact lexSort_nodup
    · exact packSched_nodup
    · exact counting_nodup
    · exact channeling_nodup
    · exact setMath_nodup
    · exact lexChain_nodup
    · exact graph_nodup
    · exact regular_nodup
    · exact sched2_nodup
  have hcomb := nodup_foldr_append fams_nodup hf fams_disj
  rw [show globalsNames = [allDiffNames, lexSortNames, packSchedNames,
    countingNames, channelingNames, setMathNames, lexChainNames, graphNames,
    regularNames, sched2Names].foldr (fun (l r : List String) => l ++ r) []
    from rfl]
  exact hcomb

/-- The combined checkable name list is duplicate-free: the global names
    are, the standard-library names are (one decide over the 79-name
    list), and `std_name_not_global` keeps the two halves apart. -/
private theorem fullCheckableNames_nodup : fullCheckableNames.Nodup := by
  have hstd : (LeanFzn.Semantics.Evaluation.stdNames ++ LeanFzn.Semantics.Evaluation.setNames).Nodup := by
    refine List.nodup_append.mpr ⟨by decide, by decide, ?_⟩
    intro a ha b hb heq
    have hall : LeanFzn.Semantics.Evaluation.stdNames.all
        (fun a => !LeanFzn.Semantics.Evaluation.setNames.contains a) = true := by
      decide
    have h1 : (!LeanFzn.Semantics.Evaluation.setNames.contains a) = true :=
      List.all_eq_true.mp hall a ha
    have h2 : LeanFzn.Semantics.Evaluation.setNames.contains b = true :=
      List.contains_iff_mem.mpr hb
    rw [← heq] at h2
    rw [h2] at h1
    simp at h1
  rw [fullCheckableNames, LeanFzn.Semantics.Evaluation.checkableNames]
  exact List.nodup_append.mpr ⟨globalsNames_nodup, hstd, fun a ha b hb heq =>
    std_name_not_global hb (heq ▸ ha)⟩

/-- The association list behind the dispatch map: each family's names
    paired with that family's Boolean twin, then the standard-library
    names paired with `Solution.interpB` (the `else` branch of
    `fullInterpB`).  Derived from the list variables, not literal
    strings, so it stays correct as the lists grow. -/
def dispatchList : List (String × (LeanFzn.Ident → List Value → Bool)) :=
  (allDiffNames.map (fun n => (n, AllDiffCounting.allDiffInterpB))) ++
  (lexSortNames.map (fun n => (n, LexSort.lexSortInterpB))) ++
  (packSchedNames.map (fun n => (n, PackSched.packSchedInterpB))) ++
  (countingNames.map (fun n => (n, Counting.countingInterpB))) ++
  (channelingNames.map (fun n => (n, Channeling.channelingInterpB))) ++
  (setMathNames.map (fun n => (n, SetMath.setMathInterpB))) ++
  (lexChainNames.map (fun n => (n, LexChain.lexChainInterpB))) ++
  (graphNames.map (fun n => (n, Graph.graphInterpB))) ++
  (regularNames.map (fun n => (n, Regular.regularInterpB))) ++
  (sched2Names.map (fun n => (n, Sched2.sched2InterpB))) ++
  (LeanFzn.Semantics.Evaluation.checkableNames.map (fun n => (n, LeanFzn.Semantics.Evaluation.interpB)))

/-- **The verified hash-map dispatcher.**  Built once from
    `dispatchList`; a lookup is O(1) average instead of the O(#names)
    chain of list-membership tests in `fullInterpB`. -/
def dispatchMap : Std.HashMap String (LeanFzn.Ident → List Value → Bool) :=
  Std.HashMap.ofList dispatchList

/-- The fast dispatch: look the name up in `dispatchMap` and apply.
    Unknown names yield `false` (the same default as `fullInterpB`'s
    branches, since every family twin returns `false` on unknown
    names). -/
def preparedInterpB : LeanFzn.Ident → List Value → Bool :=
  fun x args => (dispatchMap[x.name]?).getD (fun _ _ => false) x args

/-- The name column of `dispatchList` is exactly the combined checkable
    name list (the map is keyed by the same names `fullInterpB`
    dispatches on). -/
private theorem dispatchList_map_fst :
    dispatchList.map Prod.fst = fullCheckableNames := by
  simp only [dispatchList, fullCheckableNames, List.map_append, List.map_map,
    LeanFzn.Semantics.Evaluation.checkableNames, List.map_append]
  rfl

/-- The name column of `dispatchList` has no duplicates (every name of
    `fullCheckableNames` appears exactly once, so the map insertions
    never collide). -/
private theorem dispatchList_nodup_fst :
    (dispatchList.map Prod.fst).Nodup := by
  rw [dispatchList_map_fst]
  exact fullCheckableNames_nodup

/-- A duplicate-free name column makes the pair list `Pairwise` under
    string disequality — the shape `Std.HashMap.getElem?_insertMany_list_of_mem`
    needs. -/
private theorem pairwise_of_nodup_fst
    {l : List (String × (LeanFzn.Ident → List Value → Bool))}
    (h : (l.map Prod.fst).Nodup) :
    l.Pairwise (fun a b => (a.fst == b.fst) = false) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
      refine List.Pairwise.cons (fun a ha => ?_) (ih ((List.nodup_cons.mp h).2))
      have hmem : a.fst ∈ xs.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) ha
      have hxa : x.fst ≠ a.fst := fun heq =>
        (List.nodup_cons.mp h).1 (by rw [heq]; exact hmem)
      cases hb : (x.fst == a.fst) with
      | true => exact absurd (beq_iff_eq.mp hb) hxa
      | false => rfl

/-- The pair list is `Pairwise` under string disequality. -/
private theorem dispatchList_pairwise :
    dispatchList.Pairwise (fun a b => (a.fst == b.fst) = false) :=
  pairwise_of_nodup_fst dispatchList_nodup_fst

/-- Lookup in the dispatch map returns exactly the family twin of the
    name's family (the map is built from duplicate-free keys, so the
    insertion of the matching pair wins). -/
private theorem dispatchMap_get?_of_mem {n : String}
    {fn : LeanFzn.Ident → List Value → Bool}
    (hmem : (n, fn) ∈ dispatchList) :
    dispatchMap[n]? = some fn := by
  rw [dispatchMap, Std.HashMap.ofList_eq_insertMany_empty]
  exact Std.HashMap.getElem?_insertMany_list_of_mem (k := n) (k' := n) (by simp)
    dispatchList_pairwise hmem



section DispatchMem
variable {n : String}

private theorem mem_dispatch_allDiff (h : n ∈ allDiffNames) :
    (n, AllDiffCounting.allDiffInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem (f := fun n => (n, AllDiffCounting.allDiffInterpB)) h)))))))))))


private theorem mem_dispatch_lexSort (h : n ∈ lexSortNames) :
    (n, LexSort.lexSortInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, LexSort.lexSortInterpB)) h)))))))))))


private theorem mem_dispatch_packSched (h : n ∈ packSchedNames) :
    (n, PackSched.packSchedInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, PackSched.packSchedInterpB)) h))))))))))


private theorem mem_dispatch_counting (h : n ∈ countingNames) :
    (n, Counting.countingInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, Counting.countingInterpB)) h)))))))))


private theorem mem_dispatch_channeling (h : n ∈ channelingNames) :
    (n, Channeling.channelingInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, Channeling.channelingInterpB)) h))))))))


private theorem mem_dispatch_setMath (h : n ∈ setMathNames) :
    (n, SetMath.setMathInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, SetMath.setMathInterpB)) h)))))))


private theorem mem_dispatch_lexChain (h : n ∈ lexChainNames) :
    (n, LexChain.lexChainInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, LexChain.lexChainInterpB)) h))))))


private theorem mem_dispatch_graph (h : n ∈ graphNames) :
    (n, Graph.graphInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, Graph.graphInterpB)) h)))))


private theorem mem_dispatch_regular (h : n ∈ regularNames) :
    (n, Regular.regularInterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, Regular.regularInterpB)) h))))


private theorem mem_dispatch_sched2 (h : n ∈ sched2Names) :
    (n, Sched2.sched2InterpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inl (Or.inr (List.mem_map_of_mem (f := fun n => (n, Sched2.sched2InterpB)) h)))


private theorem mem_dispatch_checkable (h : n ∈ LeanFzn.Semantics.Evaluation.checkableNames) :
    (n, LeanFzn.Semantics.Evaluation.interpB) ∈ dispatchList := by
  rw [dispatchList]
  simp only [List.mem_append]
  exact (Or.inr (List.mem_map_of_mem (f := fun n => (n, LeanFzn.Semantics.Evaluation.interpB)) h))


end DispatchMem

/-- Lookup succeeds on every checkable name, returning the family
    twin the slow dispatcher would select. -/
theorem dispatchMap_get?_some_of_mem {n : String}
    (h : n ∈ fullCheckableNames) :
    ∃ fn, dispatchMap[n]? = some fn := by
  have hsplit : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames ∨
      n ∈ lexChainNames ∨ n ∈ graphNames ∨ n ∈ regularNames ∨
      n ∈ sched2Names ∨ n ∈ LeanFzn.Semantics.Evaluation.checkableNames := by
    rw [show fullCheckableNames = allDiffNames ++ lexSortNames ++ packSchedNames ++
      countingNames ++ channelingNames ++ setMathNames ++ lexChainNames ++
      graphNames ++ regularNames ++ sched2Names ++
      LeanFzn.Semantics.Evaluation.checkableNames from rfl] at h
    simp only [List.mem_append] at h
    exact or11_assoc h
  rcases hsplit with h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_allDiff h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_lexSort h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_packSched h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_counting h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_channeling h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_setMath h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_lexChain h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_graph h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_regular h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_sched2 h)⟩
  · exact ⟨_, dispatchMap_get?_of_mem (mem_dispatch_checkable h)⟩

/-- No standard-library name is a global-constraint name (same fact as
    `std_name_not_global`, restated for the dispatch section). -/
private theorem std_set_not_global {n : String}
    (h : n ∈ LeanFzn.Semantics.Evaluation.checkableNames) : n ∉ globalsNames :=
  std_name_not_global h

/-- The global-membership test `fullInterpB` branches on, derived from
    family membership. -/
private theorem globals_mem_of_family {n : String} :
    (n ∈ allDiffNames → n ∈ globalsNames) ∧
    (n ∈ lexSortNames → n ∈ globalsNames) ∧
    (n ∈ packSchedNames → n ∈ globalsNames) ∧
    (n ∈ countingNames → n ∈ globalsNames) ∧
    (n ∈ channelingNames → n ∈ globalsNames) ∧
    (n ∈ setMathNames → n ∈ globalsNames) ∧
    (n ∈ lexChainNames → n ∈ globalsNames) ∧
    (n ∈ graphNames → n ∈ globalsNames) ∧
    (n ∈ regularNames → n ∈ globalsNames) ∧
    (n ∈ sched2Names → n ∈ globalsNames) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl h))))))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr h))))))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inl (Or.inr h))
  · simp only [globalsNames, List.mem_append]
    exact Or.inl (Or.inr h)
  · simp only [globalsNames, List.mem_append]
    exact Or.inr h

/-- Lookup agrees with `fullInterpB` on the global-constraint names. -/
private theorem preparedInterpB_globals_iff {n : String} {args : List Value}
    (h : n ∈ globalsNames) :
    preparedInterpB (Ident.mk n) args = fullInterpB (Ident.mk n) args := by
  have hsplit : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames ∨
      n ∈ lexChainNames ∨ n ∈ graphNames ∨ n ∈ regularNames ∨
      n ∈ sched2Names := by
    rw [show globalsNames = allDiffNames ++ lexSortNames ++ packSchedNames ++
      countingNames ++ channelingNames ++ setMathNames ++ lexChainNames ++
      graphNames ++ regularNames ++ sched2Names from rfl] at h
    simp only [List.mem_append] at h
    exact or10_assoc h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
    globals_mem_of_family (n := n)
  rcases hsplit with h | h | h | h | h | h | h | h | h | h
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_allDiff h)]
    simp only [fullInterpB, if_pos (g1 h), globalsInterpB, if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_lexSort h)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := lexSort_not_other h
    obtain ⟨h6, h7, h8, h9⟩ := old_not_new (Or.inr (Or.inl h))
    simp only [fullInterpB, if_pos (g2 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_packSched h)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := packSched_not_other h
    obtain ⟨h6, h7, h8, h9⟩ := old_not_new (Or.inr (Or.inr (Or.inl h)))
    simp only [fullInterpB, if_pos (g3 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_counting h)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := counting_not_other h
    obtain ⟨h6, h7, h8, h9⟩ := old_not_new (Or.inr (Or.inr (Or.inr (Or.inl h))))
    simp only [fullInterpB, if_pos (g4 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_channeling h)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := channeling_not_other h
    obtain ⟨h6, h7, h8, h9⟩ :=
      old_not_new (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    simp only [fullInterpB, if_pos (g5 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_setMath h)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := setMath_not_other h
    obtain ⟨h6, h7, h8, h9⟩ :=
      old_not_new (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    simp only [fullInterpB, if_pos (g6 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_lexChain h)]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := lexChain_not_other h
    simp only [fullInterpB, if_pos (g7 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_graph h)]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := graph_not_other h
    simp only [fullInterpB, if_pos (g8 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_regular h)]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := regular_not_other h
    simp only [fullInterpB, if_pos (g9 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl
  · rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_sched2 h)]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := sched2_not_other h
    simp only [fullInterpB, if_pos (g10 h), globalsInterpB, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
      if_pos h]
    rfl

/-- Lookup agrees with `fullInterpB` on the standard-library names. -/
private theorem preparedInterpB_std_iff {n : String} {args : List Value}
    (h : n ∈ LeanFzn.Semantics.Evaluation.checkableNames) :
    preparedInterpB (Ident.mk n) args = fullInterpB (Ident.mk n) args := by
  rw [preparedInterpB, dispatchMap_get?_of_mem (mem_dispatch_checkable h)]
  simp only [fullInterpB, if_neg (std_set_not_global h)]
  rfl

/-- **The fast dispatcher agrees with `fullInterpB` on every checkable
    name.**  (Equality of returned `Bool`s per `(name, args)`; the
    function values stored in the map are not themselves comparable,
    so the theorem is stated pointwise.) -/
theorem preparedInterpB_iff {n : String} {args : List Value}
    (h : n ∈ fullCheckableNames) :
    preparedInterpB (Ident.mk n) args = fullInterpB (Ident.mk n) args := by
  rw [fullCheckableNames, List.mem_append] at h
  rcases h with h | h
  · exact preparedInterpB_globals_iff h
  · exact preparedInterpB_std_iff h

/-- The dispatch map contains no key outside `fullCheckableNames`
    (the map is exactly the checkable names). -/
theorem dispatchMap_get?_none_of_not_mem {n : String}
    (h : n ∉ fullCheckableNames) : dispatchMap[n]? = none := by
  rw [dispatchMap, Std.HashMap.ofList_eq_insertMany_empty]
  have hget := Std.HashMap.getElem?_insertMany_list_of_contains_eq_false
    (m := (∅ : Std.HashMap String (LeanFzn.Ident → List Value → Bool)))
    (l := dispatchList) (k := n)
    (by
      simp only [List.contains_eq_mem, dispatchList_map_fst]
      simpa using h)
  simpa using hget

/-- The fast dispatcher evaluates to `false` on names outside
    `fullCheckableNames`. -/
theorem preparedInterpB_false_of_not_mem {n : String} {args : List Value}
    (h : n ∉ fullCheckableNames) :
    preparedInterpB (Ident.mk n) args = false := by
  rw [preparedInterpB, dispatchMap_get?_none_of_not_mem h]
  rfl

/-- The dispatch map holds exactly the checkable names: a lookup
    succeeds precisely on `fullCheckableNames` (the membership test
    `firstUnsupported` performs with a linear list scan). -/
theorem dispatchMap_isSome_iff_mem {n : String} :
    (dispatchMap[n]?).isSome ↔ n ∈ fullCheckableNames := by
  constructor
  · intro hissome
    by_cases hmem : n ∈ fullCheckableNames
    · exact hmem
    · rw [dispatchMap_get?_none_of_not_mem hmem] at hissome
      exact Bool.noConfusion hissome
  · intro hmem
    obtain ⟨fn, hfn⟩ := dispatchMap_get?_some_of_mem hmem
    rw [hfn]
    rfl

end LeanFzn.Semantics.Globals

/-! ## Static well-formedness with decodability

`WellFormed` and its executable twin live here rather than in
`LeanFzn.Semantics.Model`, because the decodability conjunct refers to
the global-constraint decoders, which are downstream of `Model`. -/

namespace LeanFzn.Semantics

open LeanFzn
open LeanFzn.Semantics.Globals

/-- **Static well-formedness** of a model under the external signature
    environment `sig` (R8, A3).  Captures the context-sensitive rules of
    the supported fragment:

    * R4: predicate names are distinct; parameters and variables share
      one value namespace and are distinct; predicate formals are distinct.
    * R18/R20: parameter initializers are literals of the declared type,
      and parameter array lengths match the index set.
    * R22: variable array lengths match the index set.
    * R26/R6: variable initializers (fixings and aliases) have the
      declared type.
    * R7: `minimize`/`maximize` objectives have type `int`.
    * R8/R13-R15: every constraint's predicate is available (declared
      in the model or in `sig`) and its arguments match the signature,
      with par-to-var coercion.
    * H2: every constraint's arguments, evaluated in the shape store,
      are accepted by the decodability gate of a matching signature, so
      a well-formed model never reaches a decoder's "wrong shape" case
      for a parameter-honest store whose variables respect their domains.

    Reversed ranges are deliberately *not* rejected: they denote the
    empty set (R1).  Fixed values outside a variable's domain make a
    model unsatisfiable rather than ill-formed, and parameter data
    outside its type is an instance error (A5), so neither is checked
    here. -/
structure WellFormed (sig : SigEnv) (m : Model) : Prop where
  /-- R4: no duplicate predicate declarations. -/
  predNamesUnique : (m.predicates.map (·.name)).Nodup
  /-- R4: parameters and variables share one value namespace. -/
  valueNamesUnique :
    (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup
  /-- R4: predicate formal parameter names are distinct. -/
  predParamsUnique : ∀ p ∈ m.predicates, (p.params.map (·.name)).Nodup
  /-- R18/R20: parameter types and array lengths. -/
  parameterTypes : ∀ d ∈ m.parameters, match d with
    | .basic t _ v => v.type = t.base
    | .array idx t _ vs => vs.length = idx.length ∧ ∀ v ∈ vs, v.type = t.base
  /-- R22: variable array lengths match the declared index set. -/
  variableArrayLengths : ∀ d ∈ m.variables, match d with
    | .array ty _ _ values => values.length = ty.idx.length
    | _ => True
  /-- R26/R6: variable initializers have the declared type. -/
  variableInitializers : ∀ d ∈ m.variables, match d with
    | .basic t _ _ (some v) => v.hasBaseType m.staticEnv t.base
    | .array ty _ _ values =>
        ∀ v ∈ values, v.hasBaseType m.staticEnv ty.elem.base
    | _ => True
  /-- R7: optimization objectives have type `int`. -/
  objectiveType : match m.solve with
    | .satisfy _ => True
    | .minimize _ e | .maximize _ e => e.hasBaseType m.staticEnv .int
  /-- R8/R13-R15: constraints match one of the available signatures. -/
  constraintsChecked : ∀ c ∈ m.constraints, ∃ params ∈ m.sigEnv sig c.name,
    Forall2 (Expr.checkArg m.staticEnv) c.args params
  /-- H2: the constraint's arguments, evaluated in the shape store, are
      accepted by the decodability gate of a matching signature.  The
      signature is bundled so that a user-declared overload is handled
      by the same gate. -/
  constraintsDecode : ∀ c ∈ m.constraints, ∃ params ∈ m.sigEnv sig c.name,
    ∃ vs, Forall2 (Expr.checkArg m.staticEnv) c.args params ∧
      c.args.mapM (Expr.eval m.shapeStore) = some vs ∧
      fullDecodes c.name.name params vs = true

/-- **Executable static checker**: `wellFormedB sig m` computes the static
    well-formedness of `m` under the signature environment `sig`.
    `wellFormedB_iff` proves it equivalent to the `WellFormed`
    predicate. -/
def wellFormedB (sig : SigEnv) (m : Model) : Bool :=
  nodupIdentB (m.predicates.map (·.name)) &&
  nodupIdentB (m.parameters.map (·.name) ++ m.variables.map (·.name)) &&
  m.predicates.all (fun p => nodupIdentB (p.params.map (·.name))) &&
  m.parameters.all (fun d => parDeclCheckB d) &&
  m.variables.all (fun d => varDeclArrayLenB d) &&
  m.variables.all (fun d => varDeclInitB m.staticEnv d) &&
  solveObjB m.staticEnv m.solve &&
  m.constraints.all (fun c =>
    (m.sigEnv sig c.name).any (fun params =>
      checkArgsB m.staticEnv c.args params &&
      (match c.args.mapM (Expr.eval m.shapeStore) with
       | some vs => fullDecodes c.name.name params vs
       | none => false)))

theorem wellFormedB_iff (sig : SigEnv) (m : Model) :
    wellFormedB sig m = true ↔ WellFormed sig m := by
  unfold wellFormedB
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    refine ⟨nodupIdentB_iff.mp h1, nodupIdentB_iff.mp h2, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro p hp; exact nodupIdentB_iff.mp (h3 p hp)
    · intro d hd; exact parDeclCheckB_iff.mp (h4 d hd)
    · intro d hd; exact varDeclArrayLenB_iff.mp (h5 d hd)
    · intro d hd; exact varDeclInitB_iff.mp (h6 d hd)
    · exact solveObjB_iff.mp h7
    · intro c hc
      obtain ⟨params, hmem, hboth⟩ := List.any_eq_true.mp (h8 c hc)
      have hboth' : checkArgsB m.staticEnv c.args params = true ∧
          (match c.args.mapM (Expr.eval m.shapeStore) with
            | some vs => fullDecodes c.name.name params vs
            | none => false) = true := by
        simpa only [Bool.and_eq_true] using hboth
      have hchk : checkArgsB m.staticEnv c.args params = true := hboth'.1
      have hdec : (match c.args.mapM (Expr.eval m.shapeStore) with
          | some vs => fullDecodes c.name.name params vs
          | none => false) = true := hboth'.2
      exact ⟨params, hmem, checkArgsB_iff.mp hchk⟩
    · intro c hc
      obtain ⟨params, hmem, hboth⟩ := List.any_eq_true.mp (h8 c hc)
      have hboth' : checkArgsB m.staticEnv c.args params = true ∧
          (match c.args.mapM (Expr.eval m.shapeStore) with
            | some vs => fullDecodes c.name.name params vs
            | none => false) = true := by
        simpa only [Bool.and_eq_true] using hboth
      have hchk : checkArgsB m.staticEnv c.args params = true := hboth'.1
      have hdec : (match c.args.mapM (Expr.eval m.shapeStore) with
          | some vs => fullDecodes c.name.name params vs
          | none => false) = true := hboth'.2
      cases hev : c.args.mapM (Expr.eval m.shapeStore) with
      | none => rw [hev] at hdec; simp at hdec
      | some vs =>
        refine ⟨params, hmem, vs, checkArgsB_iff.mp hchk, rfl, ?_⟩
        rw [hev] at hdec
        simpa using hdec
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, _, h9⟩
    refine ⟨⟨⟨⟨⟨⟨⟨nodupIdentB_iff.mpr h1, nodupIdentB_iff.mpr h2⟩,
      fun p hp => nodupIdentB_iff.mpr (h3 p hp)⟩,
      fun d hd => parDeclCheckB_iff.mpr (h4 d hd)⟩,
      fun d hd => varDeclArrayLenB_iff.mpr (h5 d hd)⟩,
      fun d hd => varDeclInitB_iff.mpr (h6 d hd)⟩,
      solveObjB_iff.mpr h7⟩,
      fun c hc => by
        obtain ⟨params, hmem, vs, hpk, hev, hdec⟩ := h9 c hc
        refine List.any_eq_true.mpr ⟨params, hmem, ?_⟩
        simp only [checkArgsB_iff.mpr hpk, hev, hdec, Bool.true_and]⟩

/-- The decodability gate is neutral on every name outside the ten
    global families. -/
theorem fullDecodes_true_of_not_mem_globals {n : String}
    (h : n ∉ globalsNames) (params : List PredParamType) (args : List Value) :
    fullDecodes n params args = true := by
  have h1 : n ∉ allDiffNames := fun hn => h (globals_mem_of_family.1 hn)
  have h2 : n ∉ lexSortNames := fun hn => h (globals_mem_of_family.2.1 hn)
  have h3 : n ∉ packSchedNames := fun hn => h (globals_mem_of_family.2.2.1 hn)
  have h4 : n ∉ countingNames := fun hn => h (globals_mem_of_family.2.2.2.1 hn)
  have h5 : n ∉ channelingNames := fun hn => h (globals_mem_of_family.2.2.2.2.1 hn)
  have h6 : n ∉ setMathNames := fun hn => h (globals_mem_of_family.2.2.2.2.2.1 hn)
  have h7 : n ∉ lexChainNames := fun hn => h (globals_mem_of_family.2.2.2.2.2.2.1 hn)
  have h8 : n ∉ graphNames := fun hn => h (globals_mem_of_family.2.2.2.2.2.2.2.1 hn)
  have h9 : n ∉ regularNames := fun hn => h (globals_mem_of_family.2.2.2.2.2.2.2.2.1 hn)
  have h10 : n ∉ sched2Names := fun hn => h (globals_mem_of_family.2.2.2.2.2.2.2.2.2 hn)
  have hgate : Regular.regularGateParB n params = true := by
    have hreg : n ∉ regularNames := h9
    simp only [regularNames, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hreg
    obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := hreg
    simp [Regular.regularGateParB, hr1, hr2, hr3, hr4, hr5, hr6]
  simp [fullDecodes, globalsDecodes, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, hgate]


/-- A statically checked argument list has a successful shape evaluation. -/
theorem exists_mapM_eval_of_forall2 {m : Model} {args : List Expr}
    {params : List PredParamType}
    (hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup)
    (h : Forall2 (Expr.checkArg m.staticEnv) args params) :
    ∃ vs, args.mapM (Expr.eval m.shapeStore) = some vs := by
  induction args generalizing params with
  | nil =>
      cases params with
      | nil => exact ⟨[], rfl⟩
      | cons p ps => simp [Forall2] at h
  | cons a rest ih =>
      cases params with
      | nil => simp [Forall2] at h
      | cons p ps =>
          simp only [Forall2] at h
          obtain ⟨hhead, htail⟩ := h
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
            (eval_isSome_of_checkArg hnd hhead)
          obtain ⟨vs, hvs⟩ := ih htail
          exact ⟨v :: vs, mapM_cons_some hv hvs⟩


/-- Convenience: static well-formedness under the standard signatures. -/
def stdWellFormed (m : Model) : Bool := wellFormedB stdSig m

/-- `store` satisfies the well-formed model `m` under the predicate
    interpretation `pred`.

    `Satisfies` constrains the store on the model's *variables* only:
    it does not require the store to give each parameter its declared
    value.  A store that rebinds a parameter can therefore satisfy
    constraints that the model's actual parameter values violate.
    Statements about solutions of a FlatZinc instance must add
    `ParamHonest m store` (as `IsSolution` does); the solution checker
    guarantees it for the stores it accepts. -/
def Satisfies (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  WellFormed sig m ∧ SatisfiesDyn pred m store

/-- Optimality among the instance's solutions.  The competing stores
    must be parameter-honest: otherwise a store rebinding a parameter
    could beat the true optimum. -/
def IsOptimal (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  match m.solve with
  | .satisfy _ => True
  | .minimize _ _ => ∀ other i j, Satisfies sig pred m other → ParamHonest m other →
      m.solve.objective store = some i → m.solve.objective other = some j → i ≤ j
  | .maximize _ _ => ∀ other i j, Satisfies sig pred m other → ParamHonest m other →
      m.solve.objective store = some i → m.solve.objective other = some j → j ≤ i

/-- A complete, parameter-honest satisfying assignment which also
    realizes the solve goal. -/
def IsSolution (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  Satisfies sig pred m store ∧ ParamHonest m store ∧ ObjectiveAttained m store ∧
    IsOptimal sig pred m store

/-- Parameters have the same value in every parameter-honest store and in
    the shape store. -/
theorem shapeStore_eq_param {m : Model} {store : Store}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    {d : ParDeclItem} (hd : d ∈ m.parameters) :
    store d.name = m.shapeStore d.name ∧ m.shapeStore d.name = some d.value := by
  have hnd : (m.parameters.map (·.name)).Nodup :=
    (List.nodup_append.mp hwf.valueNamesUnique).1
  exact ⟨(hpar d hd).trans (shapeStore_param hnd hd).symm,
    shapeStore_param hnd hd⟩

/-- A variable's value in a domain-respecting store has the same shape as
    its declared dummy in the shape store. -/
theorem var_value_sameShape_shapeStore {m : Model} {store : Store}
    (hwf : WellFormed sig m) (hdom : VarsRespect m store)
    {d : VarDeclItem} (hd : d ∈ m.variables)
    {v w : Value} (hv : store d.name = some v) (hw : m.shapeStore d.name = some w) :
    v.SameShape w := by
  have hnd := hwf.valueNamesUnique
  have hshape := shapeStore_var hnd hd
  rw [hshape] at hw
  have hwv : d.shapeValue = w := Option.some.inj hw
  rw [← hwv]
  cases d with
  | basic ty n ints init =>
      obtain ⟨v0, hv0, hc⟩ := hdom _ hd
      simp only [VarDeclItem.name] at hv hv0
      rw [hv0] at hv
      have hvv : v0 = v := Option.some.inj hv
      rw [← hvv]
      exact BasicVarType.sameShape_dummy hc
  | array ty n ints init =>
      obtain ⟨vs, hvs, hlen, hc⟩ := hdom _ hd
      simp only [VarDeclItem.name] at hv hvs
      rw [hvs] at hv
      have hvv : Value.array vs = v := Option.some.inj hv
      rw [← hvv]
      exact .array (ListSameShape.replicate vs ty.idx.length hlen
        (fun z hz => BasicVarType.sameShape_dummy (hc z hz)))


/-- Static environment lookup at a parameter: the store and the shape store
    agree definitionally. -/
theorem store_eq_shapeStore_of_param_ident {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store) {x : Ident} {ft : FznType}
    (henv : m.staticEnv x = some (ft, false)) :
    store x = m.shapeStore x := by
  obtain ⟨d, hd, hdname, _⟩ := staticEnv_param henv
  have hnd : (m.parameters.map (·.name)).Nodup :=
    (List.nodup_append.mp hwf.valueNamesUnique).1
  have hs := shapeStore_param hnd hd
  have hp := hpar d hd
  rw [hdname] at hs hp
  rw [hp, hs]

/-- Static environment lookup at a variable: the value in a
    domain-respecting store has the shape of the declared dummy. -/
theorem sameShape_of_var_ident {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hdom : VarsRespect m store) {x : Ident} {ft : FznType}
    (henv : m.staticEnv x = some (ft, true)) {v w : Value}
    (hv : store x = some v) (hw : m.shapeStore x = some w) :
    v.SameShape w := by
  obtain ⟨d, hd, hdname, _⟩ := staticEnv_var henv
  rw [← hdname] at hv hw
  exact var_value_sameShape_shapeStore hwf hdom hd hv hw

/-- Agreement at an identifier occurrence, given the static environment
    says parameter (`false`) or variable (`true`). -/
theorem agree_of_ident_at {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    (hdom : VarsRespect m store) {x : Ident} {ft : FznType} {isVar : Bool}
    (henv : m.staticEnv x = some (ft, isVar)) {par : Bool}
    (hparb : par = true → isVar = false) {v w : Value}
    (hv : store x = some v) (hw : m.shapeStore x = some w) :
    Value.Agree par v w := by
  cases par with
  | true =>
      have hisVar : isVar = false := hparb rfl
      subst hisVar
      have heq := store_eq_shapeStore_of_param_ident hwf hpar henv
      rw [heq] at hv
      exact Option.some.inj (hv.symm.trans hw)
  | false =>
      cases isVar with
      | false =>
          have heq := store_eq_shapeStore_of_param_ident hwf hpar henv
          rw [heq] at hv
          rw [Option.some.inj (hv.symm.trans hw)]
          exact Value.SameShape.refl _
      | true =>
          exact sameShape_of_var_ident hwf hdom henv hv hw

/-- A basic expression that checks against a predicate parameter type has
    agreeing values in a parameter-honest, domain-respecting store and in
    the shape store. -/
theorem agree_of_checkBase {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    (hdom : VarsRespect m store)
    {b : BasicExpr} {bt : BasicPredParamType} (hb : b.checkBase m.staticEnv bt)
    {v w : Value} (hv : b.eval store = some v) (hw : b.eval m.shapeStore = some w) :
    Value.Agree bt.isPar v w := by
  cases b with
  | lit l =>
      simp only [BasicExpr.eval, Option.some.injEq] at hv hw
      subst hv; subst hw
      cases bt.isPar with
      | false => exact Value.SameShape.refl _
      | true => rfl
  | ident x =>
      simp only [BasicExpr.eval] at hv hw
      simp only [BasicExpr.checkBase] at hb
      cases henv : m.staticEnv x with
      | none => rw [henv] at hb; exact hb.elim
      | some info =>
          obtain ⟨ft, isVar⟩ := info
          simp only [henv] at hb
          cases ft with
          | array n t => exact hb.elim
          | base t => exact agree_of_ident_at hwf hpar hdom henv hb.2 hv hw

theorem eval_array_inv {es : List BasicExpr} {store : Store} {v : Value}
    (h : (es.mapM (BasicExpr.eval store)).map Value.array = some v) :
    ∃ vs, es.mapM (BasicExpr.eval store) = some vs ∧ v = .array vs := by
  cases hm : es.mapM (BasicExpr.eval store) with
  | none => rw [hm] at h; simp at h
  | some vs =>
      rw [hm] at h
      change some (Value.array vs) = some v at h
      exact ⟨vs, rfl, (Option.some.inj h).symm⟩

/-- Elementwise agreement for an array literal whose elements all check
    against the same basic parameter type. -/
theorem argsAgree_replicate_of_forall {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    (hdom : VarsRespect m store) {es : List BasicExpr} {bt : BasicPredParamType}
    (hcheck : ∀ b ∈ es, b.checkBase m.staticEnv bt) :
    ∀ {vs ws : List Value},
      es.mapM (BasicExpr.eval store) = some vs →
      es.mapM (BasicExpr.eval m.shapeStore) = some ws →
      ArgsAgree (List.replicate es.length (.basic bt)) vs ws := by
  induction es with
  | nil =>
      intro vs ws hv hw
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hv hw
      subst hv; subst hw
      exact trivial
  | cons e es ih =>
      intro vs ws hv hw
      obtain ⟨v, vs', hve, hvs, rfl⟩ := mapM_cons_inv hv
      obtain ⟨w, ws', hwe, hws, rfl⟩ := mapM_cons_inv hw
      have hhead : e.checkBase m.staticEnv bt := hcheck e List.mem_cons_self
      have htail : ∀ b ∈ es, b.checkBase m.staticEnv bt :=
        fun b hb => hcheck b (List.mem_cons_of_mem _ hb)
      have hag := agree_of_checkBase hwf hpar hdom hhead hve hwe
      have htl := ih htail hvs hws
      simp only [List.length_cons, List.replicate_succ]
      exact ⟨hag, htl⟩

/-- An expression that checks against a predicate parameter type has
    agreeing values in a parameter-honest, domain-respecting store and in
    the shape store. -/
theorem agree_of_checkArg {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    (hdom : VarsRespect m store)
    {e : Expr} {pt : PredParamType} (hc : e.checkArg m.staticEnv pt)
    {v w : Value} (hv : e.eval store = some v) (hw : e.eval m.shapeStore = some w) :
    Value.Agree pt.isPar v w := by
  cases e with
  | basic b =>
      cases pt with
      | basic bt =>
          simp only [Expr.checkArg, Expr.eval] at hc ⊢
          exact agree_of_checkBase hwf hpar hdom hc hv hw
      | array idx bt =>
          cases b with
          | lit l => simp [Expr.checkArg] at hc
          | ident x =>
              simp only [Expr.checkArg, Expr.eval] at hc ⊢
              cases henv : m.staticEnv x with
              | none => rw [henv] at hc; exact hc.elim
              | some info =>
                  obtain ⟨ft, isVar⟩ := info
                  rw [henv] at hc
                  cases ft with
                  | base t => exact hc.elim
                  | array n t =>
                      change store x = some v at hv
                      change m.shapeStore x = some w at hw
                      exact agree_of_ident_at hwf hpar hdom henv hc.2.2 hv hw
  | array es =>
      cases pt with
      | basic bt => simp [Expr.checkArg] at hc
      | array idx bt =>
          simp only [Expr.checkArg, Expr.eval] at hc ⊢
          obtain ⟨hlen, hcheck⟩ := hc
          obtain ⟨vs, hvs, rfl⟩ := eval_array_inv hv
          obtain ⟨ws, hws, rfl⟩ := eval_array_inv hw
          have hag := argsAgree_replicate_of_forall hwf hpar hdom hcheck hvs hws
          cases hparb : bt.isPar with
          | true =>
              have hall : ∀ q ∈ List.replicate es.length (PredParamType.basic bt),
                  q.isPar = true := by
                intro q hq
                simp only [List.mem_replicate] at hq
                rw [hq.2]
                exact hparb
              have hveq : vs = ws := ArgsAgree.eq_of_all_par hag hall
              simp only [PredParamType.isPar, hparb, Value.Agree, hveq]
          | false =>
              simp only [PredParamType.isPar, hparb, Value.Agree]
              exact .array (ArgsAgree.sameShape hag)

/-- A checked argument list agrees with its shape evaluation. -/
theorem argsAgree_of_forall2 {m : Model} {store : Store} {sig}
    (hwf : WellFormed sig m) (hpar : ParamHonest m store)
    (hdom : VarsRespect m store)
    {args : List Expr} {params : List PredParamType}
    (hcheck : Forall2 (Expr.checkArg m.staticEnv) args params) :
    ∀ {vs ws : List Value},
      args.mapM (Expr.eval store) = some vs →
      args.mapM (Expr.eval m.shapeStore) = some ws →
      ArgsAgree params vs ws := by
  induction args generalizing params with
  | nil =>
      intro vs ws hv hw
      cases params with
      | nil =>
          simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hv hw
          subst hv; subst hw
          exact trivial
      | cons pt pts => cases hcheck
  | cons e es ih =>
      intro vs ws hv hw
      cases params with
      | nil => cases hcheck
      | cons pt pts =>
          obtain ⟨hhead, htail⟩ := hcheck
          obtain ⟨v, vs', hve, hvs, rfl⟩ := mapM_cons_inv hv
          obtain ⟨w, ws', hwe, hws, rfl⟩ := mapM_cons_inv hw
          exact ⟨agree_of_checkArg hwf hpar hdom hhead hve hwe,
            ih htail hvs hws⟩



/-- **Decodability from well-formedness.**  In a parameter-honest store
    whose variables respect their declared domains, every constraint's
    evaluated arguments are accepted by the decodability gate of a
    matching signature.  This is the H2 bridge from the static shape
    check to the real values. -/
theorem WellFormed.constraint_decodes
    (h : WellFormed sig m) {c : ConstraintItem} (hc : c ∈ m.constraints)
    (hpar : ParamHonest m store) (hdom : VarsRespect m store) {vs : List Value}
    (heval : c.args.mapM (Expr.eval store) = some vs) :
    ∃ params ∈ m.sigEnv sig c.name,
      Forall2 (Expr.checkArg m.staticEnv) c.args params ∧
      fullDecodes c.name.name params vs = true := by
  obtain ⟨params, hmem, shvs, hcheck, hshape, hdec⟩ := h.constraintsDecode c hc
  have hag : ArgsAgree params vs shvs :=
    argsAgree_of_forall2 h hpar hdom hcheck heval hshape
  exact ⟨params, hmem, hcheck, by
    rw [fullDecodes_agree hag c.name.name]
    exact hdec⟩


end LeanFzn.Semantics
