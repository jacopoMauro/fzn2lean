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
the non-float fragment of the pinned MiniZinc 2.10.0 tree (commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea`, `share/minizinc/std/`):

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
      some [.array .int (.var (.par .int))]
  | "fzn_all_different_set" =>
      some [.array .int (.var (.par .setOfInt))]
  | "fzn_all_disjoint" =>
      some [.array .int (.var (.par .setOfInt))]
  | "fzn_all_equal_int" => some [.array .int (.var (.par .int))]
  | "fzn_all_equal_set" =>
      some [.array .int (.var (.par .setOfInt))]
  | "fzn_alldifferent_except" =>
      some [.array .int (.var (.par .int)), .basic (.par .setOfInt)]
  | "fzn_alldifferent_except_0" =>
      some [.array .int (.var (.par .int))]
  | "fzn_symmetric_all_different" =>
      some [.array .int (.var (.par .int))]
  -- counting
  | "fzn_nvalue" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_among" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int)),
        .basic (.par .setOfInt)]
  | "fzn_at_least_int" =>
      some [.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]
  | "fzn_at_most_int" =>
      some [.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]
  | "fzn_exactly_int" =>
      some [.basic (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int)]
  | "fzn_count_eq" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_eq_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_count_geq" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_geq_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_count_gt" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_gt_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_count_leq" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_leq_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_count_lt" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_lt_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_count_neq" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_count_neq_par" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int)]
  | "fzn_distribute" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_global_cardinality" =>
      some [.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.var (.par .int))]
  | "fzn_global_cardinality_closed" =>
      some [.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.var (.par .int))]
  | "fzn_global_cardinality_low_up" =>
      some [.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .int)]
  | "fzn_global_cardinality_low_up_closed" =>
      some [.array .int (.var (.par .int)), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .int)]
  -- set counting
  | "fzn_count_eq_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_count_eq_set_par" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt), .basic (.par .int)]
  | "fzn_count_geq_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_count_gt_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_count_leq_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_count_lt_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_count_neq_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_at_least_set" =>
      some [.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]
  | "fzn_at_most_set" =>
      some [.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]
  | "fzn_exactly_set" =>
      some [.basic (.par .int), .array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]
  -- lex (1-D int only; the flat ones)
  | "fzn_lex_less_int" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_lex_lesseq_int" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  -- sorting
  | "fzn_increasing_int" => some [.array .int (.var (.par .int))]
  | "fzn_increasing_bool" => some [.array .int (.var (.par .bool))]
  | "fzn_strictly_increasing_int" =>
      some [.array .int (.var (.par .int))]
  | "fzn_sort" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_arg_sort_int" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_maximum_arg_int" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_minimum_arg_int" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int))]
  -- channeling
  | "fzn_inverse" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_inverse_in_range" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_int_set_channel" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .setOfInt))]
  | "fzn_link_set_to_booleans" =>
      some [.basic (.var (.par .setOfInt)),
        .array .int (.var (.par .bool))]
  -- array-related
  | "fzn_member_int" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_member_bool" =>
      some [.array .int (.var (.par .bool)), .basic (.var (.par .bool))]
  | "fzn_member_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_arg_val_int" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_arg_val_bool" =>
      some [.array .int (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_write" =>
      some [.array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_writes" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  -- set-related
  | "fzn_disjoint" =>
      some [.basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_set_member" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_partition_set" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.par .setOfInt)]
  | "fzn_at_most1" =>
      some [.array .int (.var (.par .setOfInt))]
  -- mathematical
  | "fzn_sum_set" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "fzn_sum_pred" =>
      some [.basic (.var (.par .int)), .array .int (.par .setOfInt),
        .array .int (.par .int), .basic (.var (.par .int))]
  | "fzn_range" =>
      some [.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_roots" =>
      some [.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_array_int_union" =>
      some [.array .int (.var (.par .int)),
        .basic (.var (.par .setOfInt))]
  | "fzn_array_set_union" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_array_set_intersect" =>
      some [.array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "fzn_sliding_sum" =>
      some [.basic (.par .int), .basic (.par .int),
        .basic (.par .int), .array .int (.var (.par .int))]
  | "fzn_sliding_among_int" =>
      some [.basic (.par .int), .basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .int)), .basic (.par .setOfInt)]
  | "fzn_sliding_among_bool" =>
      some [.basic (.par .int), .basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .bool)), .basic (.par .bool)]
  -- packing
  | "fzn_bin_packing" =>
      some [.basic (.par .int), .array .int (.var (.par .int)),
        .array .int (.par .int)]
  | "fzn_bin_packing_capa" =>
      some [.array .int (.par .int),
        .array .int (.var (.par .int)), .array .int (.par .int)]
  | "fzn_bin_packing_load" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.par .int)]
  | "fzn_knapsack" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_diffn" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_diffn_nonstrict" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_geost_nonoverlap_k" =>
      some [.array .int (.var (.par .int)),
        .array .int (.par .int),
        .array .int (.var (.par .int)),
        .array .int (.par .int)]
  -- scheduling
  | "fzn_disjunctive" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_disjunctive_strict" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_cumulative" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  -- if-then-else (table-like)
  | "fzn_if_then_else_int" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.par .int), .basic (.var (.par .int))]
  | "fzn_if_then_else_bool" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.par .bool), .basic (.var (.par .bool))]
  | "fzn_if_then_else_set" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.par .setOfInt),
        .basic (.var (.par .setOfInt))]
  | "fzn_if_then_else_var_int" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_if_then_else_var_bool" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "fzn_if_then_else_var_set" =>
      some [.array .int (.var (.par .bool)),
        .array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  -- extensional
  | "fzn_table_int" =>
      some [.array .int (.var (.par .int)),
        .array .int (.par .int)]
  -- value precedence
  | "fzn_value_precede_int" =>
      some [.basic (.par .int), .basic (.par .int),
        .array .int (.var (.par .int))]
  | "fzn_value_precede_chain_int" =>
      some [.array .int (.par .int),
        .array .int (.var (.par .int))]
  | "fzn_seq_precede_chain_int" =>
      some [.array .int (.var (.par .int))]
  -- LexChain family (G24)
  | "fzn_lex_greater_int" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_lex_greatereq_int" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_lex_chain_less_int" =>
      some [.array .int (.var (.par .int))]
  | "fzn_lex_chain_lesseq_int" =>
      some [.array .int (.var (.par .int))]
  | "fzn_lex2" =>
      some [.array .int (.var (.par .int))]
  | "fzn_strict_lex2" =>
      some [.array .int (.var (.par .int))]
  | "fzn_lex_chain_lesseq_orbitope" =>
      some [.array .int (.var (.par .int)), .basic (.par .int)]
  | "fzn_lex_chain_greater_int" =>
      some [.array .int (.var (.par .int))]
  | "fzn_lex_chain_greatereq_int" =>
      some [.array .int (.var (.par .int))]
  | "fzn_lex_chain_greatereq_orbitope" =>
      some [.array .int (.var (.par .int)), .basic (.par .int)]
  -- Graph family (G25/G29)
  | "fzn_circuit" => some [.array .int (.var (.par .int))]
  | "fzn_subcircuit" => some [.array .int (.var (.par .int))]
  | "fzn_subgraph" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "fzn_dag" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "fzn_connected" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "fzn_dconnected" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "fzn_reachable" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_dreachable" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_tree" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_dtree" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_path" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_dpath" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_bounded_path" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)), .basic (.var (.par .int)),
        .basic (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_bounded_dpath" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)), .basic (.var (.par .int)),
        .basic (.var (.par .int)), .basic (.var (.par .int))]
  | "fzn_steiner" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_dsteiner" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .array .int (.var (.par .bool)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "fzn_wst" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .basic (.var (.par .int))]
  | "fzn_dwst" =>
      some [.array .int (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.var (.par .bool)),
        .basic (.var (.par .int)), .basic (.var (.par .int))]
  -- Regular family (G27/G28)
  | "fzn_regular" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int)]
  | "fzn_regular_nfa" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .setOfInt), .basic (.par .int),
        .array .int (.par .int)]
  | "fzn_cost_regular" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .basic (.par .int), .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int))]
  | "fzn_mdd" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int)]
  | "fzn_mdd_nondet" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int)]
  | "fzn_cost_mdd" =>
      some [.array .int (.var (.par .int)), .basic (.par .int),
        .array .int (.par .int), .basic (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.par .int), .array .int (.par .int),
        .basic (.var (.par .int))]
  -- Sched2 family (G26/G30/G31/G32)
  | "fzn_cumulatives" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .basic (.par .bool),
        .basic (.par .int)]
  | "fzn_cumulatives_decomp" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .basic (.par .bool)]
  | "fzn_geost" =>
      some [.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_geost_bb" =>
      some [.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_geost_smallest_bb" =>
      some [.basic (.par .int), .array .int (.par .int),
        .array .int (.par .int), .array .int (.par .setOfInt),
        .array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_diffn_nonoverlap_k" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_diffn_k" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_diffn_nonstrict_k" =>
      some [.array .int (.var (.par .int)),
        .array .int (.var (.par .int))]
  | "fzn_writes_seq" =>
      some [.array .int (.var (.par .int)), .array .int (.var (.par .int)),
        .array .int (.var (.par .int)), .array .int (.var (.par .int))]
  | "fzn_if_then_else_partiality" =>
      some [.array .int (.var (.par .bool)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | _ => none

/-- The combined signature environment: the standard FlatZinc
    builtins plus the global constraints. -/
def fullSig : LeanFzn.Semantics.SigEnv := fun x =>
  match globalsSig x with
  | some ps => some ps
  | none => LeanFzn.Semantics.stdSig x

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
private theorem std_name_not_global {n : String}
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
