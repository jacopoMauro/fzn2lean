import LeanFzn.FznStdLib
import LeanFzn.FznSolution
import LeanFzn.FznGlobals.AllDiffCounting
import LeanFzn.FznGlobals.LexSort
import LeanFzn.FznGlobals.PackSched
import LeanFzn.FznGlobals.Counting
import LeanFzn.FznGlobals.Channeling
import LeanFzn.FznGlobals.SetMath

/-!
# Global constraints (FlatZinc `fzn_*` solver predicates)

The MiniZinc standard library decomposes each global constraint into a
`fzn_<name>_<type>` solver predicate that appears verbatim in compiled
FlatZinc (the library layout of MiniZinc >= 2.3).  This module adds, for
the non-float fragment of the pinned MiniZinc 2.10.0 tree (commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea`, `share/minizinc/std/`):

* `globalsSig` — a `SigEnv` with the FlatZinc signatures of all
  `fzn_*` global-constraint predicates of the fragment, so models using
  them pass static checking (`wellFormedB`);
* `globalsInterp`/`globalsInterpB` — the combined mathematical
  interpretation and its executable Boolean twin, dispatching each of
  the 94 supported `fzn_*` names to its family module
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
(G1–G23), with per-predicate handbook quotations and `.mzn`
decomposition citations in the family module docstrings.

Excluded from the fragment: float and opt (`var opt`) variants, reified
variants (`_reif`), the 2D-array predicates (they never appear in the
1-dimensional FlatZinc output this project parses — the compiler always
flattens to `fzn_*_k` or decomposes further), string-regexp `regular`,
`neural_net` (floats), and the graph predicates whose decomposition
requires auxiliary opt/dtree reasoning (`fzn_dag`, `fzn_connected`,
`fzn_*reachable`, `fzn_*path`, `fzn_*tree`, `fzn_*steiner`, `fzn_*wst`,
`fzn_dwst`, `fzn_alternative`, `fzn_span`, `fzn_subgraph`,
`fzn_cumulatives*`, `fzn_geost*`, `fzn_diffn_k`, `fzn_lex2`,
`fzn_strict_lex2`, `fzn_*_orbitope`, `fzn_writes_seq`,
`fzn_if_then_else_partiality`) — these are listed in `globalsUnsupported`
so the checker *reports* them rather than silently mis-checking.

## Conventions

All array arguments are 1-based (FlatZinc arrays are `array [1..n]`),
which the `List.getElem`-based twins realize with 0-based `List`
indices plus a `+1` shift in wrapper helpers.
-/

namespace LeanFzn.Globals

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
private def setBound (s : IntSetValue) : List Int := LeanFzn.Solution.setElems s

/-! ## The signatures -/

/-- The FlatZinc signatures of the supported global constraints. -/
def globalsSig : LeanFzn.SigEnv := fun x =>
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
  | _ => none

/-- The combined signature environment: the standard FlatZinc
    builtins plus the global constraints. -/
def fullSig : LeanFzn.SigEnv := fun x =>
  match globalsSig x with
  | some ps => some ps
  | none => LeanFzn.stdSig x

/-! ## The unsupported global constraints

These `fzn_*` names exist in the pinned tree but are not executable
here (float/opt/2D-array/graph-decomposition dependent).  The checker
reports them rather than guessing. -/
def globalsUnsupported : List String :=
  [ "fzn_lex_greater_int", "fzn_lex_greatereq_int"
  , "fzn_lex_chain_less_int", "fzn_lex_chain_lesseq_int"
  , "fzn_lex2", "fzn_strict_lex2", "fzn_lex_chain_lesseq_orbitope"
  , "fzn_circuit", "fzn_subcircuit"
  , "fzn_cumulatives", "fzn_cumulatives_decomp"
  , "fzn_dag", "fzn_connected", "fzn_dconnected"
  , "fzn_dpath", "fzn_path", "fzn_bounded_path", "fzn_bounded_dpath"
  , "fzn_dreachable", "fzn_reachable"
  , "fzn_dtree", "fzn_tree", "fzn_dsteiner", "fzn_steiner"
  , "fzn_dwst", "fzn_wst"
  , "fzn_alternative", "fzn_span", "fzn_subgraph"
  , "fzn_geost", "fzn_geost_bb", "fzn_geost_smallest_bb"
  , "fzn_diffn_k", "fzn_diffn_nonstrict_k", "fzn_diffn_nonoverlap_k"
  , "fzn_writes_seq", "fzn_if_then_else_partiality"
  , "fzn_mdd", "fzn_mdd_nondet", "fzn_cost_mdd"
  , "fzn_regular", "fzn_regular_nfa", "fzn_cost_regular"
  , "fzn_neural_net"
  , "fzn_piecewise_linear", "fzn_piecewise_linear_non_continuous"
  ]

/-! ## Combined interpretation

The 94 supported `fzn_*` names are partitioned without overlap across
six family modules, each providing a total mathematical interpretation
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

/-- The 94 supported global-constraint names (the concatenation of the
    six family name lists). -/
def globalsNames : List String :=
  allDiffNames ++ lexSortNames ++ packSchedNames ++ countingNames ++
    channelingNames ++ setMathNames

/-- The combined global-constraint interpretation: dispatches each of
    the 94 supported `fzn_*` names to its family's interpretation
    (the families are non-overlapping; every other name yields
    falsity, since all family interps return `fun _ => False` on
    unknown names). -/
def globalsInterp : LeanFzn.PredicateInterpretation := fun x =>
  if x.name ∈ allDiffNames then AllDiffCounting.allDiffInterp x
  else if x.name ∈ lexSortNames then LexSort.lexSortInterp x
  else if x.name ∈ packSchedNames then PackSched.packSchedInterp x
  else if x.name ∈ countingNames then Counting.countingInterp x
  else if x.name ∈ channelingNames then Channeling.channelingInterp x
  else if x.name ∈ setMathNames then SetMath.setMathInterp x
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
    first
    | exact AllDiffCounting.fzn_all_different_int_iff args
    | exact AllDiffCounting.fzn_all_different_set_iff args
    | exact AllDiffCounting.fzn_all_disjoint_iff args
    | exact AllDiffCounting.fzn_all_equal_int_iff args
    | exact AllDiffCounting.fzn_all_equal_set_iff args
    | exact AllDiffCounting.fzn_alldifferent_except_iff args
    | exact AllDiffCounting.fzn_alldifferent_except_0_iff args
    | exact AllDiffCounting.fzn_symmetric_all_different_iff args

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
    first
    | exact LexSort.fzn_lex_less_int_iff args
    | exact LexSort.fzn_lex_lesseq_int_iff args
    | exact LexSort.fzn_increasing_int_iff args
    | exact LexSort.fzn_increasing_bool_iff args
    | exact LexSort.fzn_strictly_increasing_int_iff args
    | exact LexSort.fzn_sort_iff args
    | exact LexSort.fzn_arg_sort_int_iff args
    | exact LexSort.fzn_maximum_arg_int_iff args
    | exact LexSort.fzn_minimum_arg_int_iff args
    | exact LexSort.fzn_value_precede_int_iff args
    | exact LexSort.fzn_value_precede_chain_int_iff args
    | exact LexSort.fzn_seq_precede_chain_int_iff args

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
    first
    | exact PackSched.bin_packing_iff args
    | exact PackSched.bin_packing_capa_iff args
    | exact PackSched.bin_packing_load_iff args
    | exact PackSched.knapsack_iff args
    | exact PackSched.diffn_iff args
    | exact PackSched.diffn_nonstrict_iff args
    | exact PackSched.geost_nonoverlap_k_iff args
    | exact PackSched.disjunctive_iff args
    | exact PackSched.disjunctive_strict_iff args
    | exact PackSched.cumulative_iff args
    | exact PackSched.table_int_iff args
    | exact PackSched.if_then_else_int_iff args
    | exact PackSched.if_then_else_bool_iff args
    | exact PackSched.if_then_else_set_iff args
    | exact PackSched.if_then_else_var_int_iff args
    | exact PackSched.if_then_else_var_bool_iff args
    | exact PackSched.if_then_else_var_set_iff args

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
    first
    | exact Counting.fzn_nvalue_iff args
    | exact Counting.fzn_among_iff args
    | exact Counting.fzn_at_least_int_iff args
    | exact Counting.fzn_at_most_int_iff args
    | exact Counting.fzn_exactly_int_iff args
    | exact Counting.fzn_count_eq_iff args
    | exact Counting.fzn_count_eq_par_iff args
    | exact Counting.fzn_count_geq_iff args
    | exact Counting.fzn_count_geq_par_iff args
    | exact Counting.fzn_count_gt_iff args
    | exact Counting.fzn_count_gt_par_iff args
    | exact Counting.fzn_count_leq_iff args
    | exact Counting.fzn_count_leq_par_iff args
    | exact Counting.fzn_count_lt_iff args
    | exact Counting.fzn_count_lt_par_iff args
    | exact Counting.fzn_count_neq_iff args
    | exact Counting.fzn_count_neq_par_iff args
    | exact Counting.fzn_distribute_iff args
    | exact Counting.fzn_global_cardinality_iff args
    | exact Counting.fzn_global_cardinality_closed_iff args
    | exact Counting.fzn_global_cardinality_low_up_iff args
    | exact Counting.fzn_global_cardinality_low_up_closed_iff args
    | exact Counting.fzn_count_eq_set_iff args
    | exact Counting.fzn_count_eq_set_par_iff args
    | exact Counting.fzn_count_geq_set_iff args
    | exact Counting.fzn_count_gt_set_iff args
    | exact Counting.fzn_count_leq_set_iff args
    | exact Counting.fzn_count_lt_set_iff args
    | exact Counting.fzn_count_neq_set_iff args
    | exact Counting.fzn_at_least_set_iff args
    | exact Counting.fzn_at_most_set_iff args
    | exact Counting.fzn_exactly_set_iff args

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
    first
    | exact Channeling.fzn_inverse_iff args
    | exact Channeling.fzn_inverse_in_range_iff args
    | exact Channeling.fzn_int_set_channel_iff args
    | exact Channeling.fzn_link_set_to_booleans_iff args
    | exact Channeling.fzn_member_int_iff args
    | exact Channeling.fzn_member_bool_iff args
    | exact Channeling.fzn_member_set_iff args
    | exact Channeling.fzn_arg_val_int_iff args
    | exact Channeling.fzn_arg_val_bool_iff args
    | exact Channeling.fzn_write_iff args
    | exact Channeling.fzn_writes_iff args

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
    first
    | exact SetMath.fzn_disjoint_iff args
    | exact SetMath.fzn_set_member_iff args
    | exact SetMath.fzn_partition_set_iff args
    | exact SetMath.fzn_at_most1_iff args
    | exact SetMath.fzn_sum_set_iff args
    | exact SetMath.fzn_sum_pred_iff args
    | exact SetMath.fzn_range_iff args
    | exact SetMath.fzn_roots_iff args
    | exact SetMath.fzn_array_int_union_iff args
    | exact SetMath.fzn_array_set_union_iff args
    | exact SetMath.fzn_array_set_intersect_iff args
    | exact SetMath.fzn_sliding_sum_iff args
    | exact SetMath.fzn_sliding_among_int_iff args
    | exact SetMath.fzn_sliding_among_bool_iff args

/-! ### The master agreement theorem -/

/-- **Master agreement**: on every supported global-constraint name,
    the combined Boolean twin `globalsInterpB` is `true` exactly when
    the combined mathematical interpretation `globalsInterp`
    holds. -/
theorem globalsInterpB_iff {n : String} {args : List Value}
    (hn : n ∈ globalsNames) :
    globalsInterpB (Ident.mk n) args = true ↔ globalsInterp (Ident.mk n) args := by
  have hsplit : n ∈ allDiffNames ∨ n ∈ lexSortNames ∨ n ∈ packSchedNames ∨
      n ∈ countingNames ∨ n ∈ channelingNames ∨ n ∈ setMathNames := by
    unfold globalsNames at hn
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append,
      List.mem_append] at hn
    rcases hn with (((((h | h) | h) | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rcases hsplit with h | h | h | h | h | h
  · simp only [globalsInterpB, globalsInterp, if_pos h]
    exact globalsInterpB_alldiff_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := lexSort_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_pos h]
    exact globalsInterpB_lexsort_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := packSched_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_pos h]
    exact globalsInterpB_packsched_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := counting_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_pos h]
    exact globalsInterpB_counting_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := channeling_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_pos h]
    exact globalsInterpB_channeling_iff h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := setMath_not_other h
    simp only [globalsInterpB, globalsInterp, if_neg h1, if_neg h2, if_neg h3,
      if_neg h4, if_neg h5, if_pos h]
    exact globalsInterpB_setmath_iff h

/-! ## The combined standard-plus-globals interpretation

`fullInterp` interprets every predicate of the full signature
`fullSig`: the 94 `fzn_*` global-constraint names via `globalsInterp`,
every other name via the standard library interpretation
`stdInterp`.  Its executable twin `fullInterpB` dispatches likewise:
`fzn_*` names to `globalsInterpB`, everything else to
`Solution.interpB` (which itself decides the extensional set
predicates and delegates the rest to `stdInterpB`). -/

/-- The combined interpretation of the full fragment: global
    constraints by their family interpretation, standard predicates by
    `stdInterp`. -/
def fullInterp : LeanFzn.PredicateInterpretation := fun x =>
  if x.name ∈ globalsNames then globalsInterp x else LeanFzn.stdInterp x

/-- **Executable twin of `fullInterp`**. -/
def fullInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  if x.name ∈ globalsNames then globalsInterpB x
  else LeanFzn.Solution.interpB x

/-- The names of every predicate with an executable, verified twin in
    the combined fragment: the global-constraint names plus the
    standard-library names (including the extensional set predicates). -/
def fullCheckableNames : List String :=
  globalsNames ++ LeanFzn.Solution.checkableNames

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
    (h : n ∈ LeanFzn.Solution.checkableNames) (hne : n ∉ globalsNames) :
    fullInterpB (Ident.mk n) args = true ↔ fullInterp (Ident.mk n) args := by
  simp only [fullInterpB, fullInterp, if_neg hne]
  rw [LeanFzn.Solution.checkableNames, List.mem_append] at h
  rcases h with h | h
  · exact LeanFzn.Solution.interpB_std_iff h
  · exact LeanFzn.Solution.interpB_set_iff h

/-- Every checkable standard-library name is outside the six family
    name lists (no standard name starts with `fzn_`; each family list
    contains only such names). -/
private theorem std_name_not_global {n : String}
    (h : n ∈ LeanFzn.Solution.checkableNames) : n ∉ globalsNames := by
  intro hmem
  rw [LeanFzn.Solution.checkableNames, List.mem_append] at h
  rcases h with h | h
  · -- standard names: none equals any of the 94 fzn_* names
    simp only [LeanFzn.Solution.stdNames, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact absurd hmem (by decide)
  · simp only [LeanFzn.Solution.setNames, List.mem_cons, List.not_mem_nil,
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

/-! ## The full solution checker -/

/-- Evaluate a constraint's arguments and check the predicate under
    the combined twin (executable counterpart of
    `ConstraintItem.Holds fullInterp`). -/
private def constraintHoldsFullB (store : Store) (c : ConstraintItem) : Bool :=
  match c.args.mapM (Expr.eval store) with
  | some args => fullInterpB c.name args
  | none => false

/-- `constraintHoldsFullB` decides `Holds fullInterp` for checkable
    predicates. -/
private theorem constraintHoldsFullB_iff {store : Store} {c : ConstraintItem}
    (hname : c.name.name ∈ fullCheckableNames) :
    constraintHoldsFullB store c = true ↔ c.Holds fullInterp store := by
  unfold constraintHoldsFullB ConstraintItem.Holds
  cases hargs : c.args.mapM (Expr.eval store) with
  | none =>
      constructor
      · intro hfalse
        exact absurd hfalse (by intro hc; cases hc)
      · rintro ⟨args, hnone, _⟩
        cases hnone
  | some args =>
      constructor
      · intro h
        refine ⟨args, rfl, ?_⟩
        have hred : fullInterpB c.name args = true := h
        cases hc : c.name with
        | mk n' =>
            rw [hc] at hred hname
            exact (fullInterpB_iff (n := n') hname).mp hred
      · rintro ⟨args', hargs', hinterp⟩
        have hargs_eq : args = args' := Option.some.inj hargs'
        subst hargs_eq
        show fullInterpB c.name args = true
        cases hc : c.name with
        | mk n' =>
            rw [hc] at hinterp hname
            exact (fullInterpB_iff (n := n') hname).mpr hinterp

/-- The top-level solution checker for the full fragment: parse the
    solution string, build the candidate store, and check every
    dynamic condition of `Satisfies fullSig fullInterp` — variable
    domains, initializers, and constraints (both standard and global)
    — with executable Boolean twins. -/
def checkSolutionFull (m : Model) (sol : String) : Bool :=
  match LeanFzn.Solution.parseSolution
      (LeanFzn.Solution.stripSeparators sol) with
  | .error _ => false
  | .ok es =>
      let box := LeanFzn.Solution.completedBox m es
      LeanFzn.Solution.allAssignedB box.f m.variables &&
      LeanFzn.Solution.varDeclsOkB box.f m.variables &&
      m.constraints.all (fun c => constraintHoldsFullB box.f c)

/-! ### The correctness theorem

The checker decides the *dynamic* conditions of
`Satisfies fullSig fullInterp`: `checkSolutionFull m sol = true`
exactly when the solution string parses and the candidate store it
describes satisfies every variable-domain, initializer, and constraint
condition.  Static well-formedness (`WellFormed fullSig m`) is a
*precondition* of the theorem (`hwf`), not re-decided by the checker;
combining `hwf` with the right-hand side yields `Satisfies`. -/

/-- The dynamic conditions of `Satisfies sig pred m store`: constraints,
    variable domains, and initializers (everything but static
    well-formedness). -/
def SatisfiesDyn (pred : LeanFzn.PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  (∀ c ∈ m.constraints, c.Holds pred store) ∧
  (∀ d ∈ m.variables, match d with
    | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
    | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
        vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) ∧
  (∀ d ∈ m.variables, d.initializerHolds store)

/-- **Correctness of the full checker.**  For a model whose
    constraints all use checkable predicates (the 94 `fzn_*` global
    constraints or the standard library), `checkSolutionFull` returns
    `true` if and only if the solution string parses and the candidate
    store it describes satisfies every dynamic condition of
    `Satisfies fullSig fullInterp`: the constraint reading of `Holds`,
    the variable-domain conditions, and the initializer conditions. -/
theorem checkSolutionFull_correct (m : Model) (sol : String)
    (hnames : ∀ c ∈ m.constraints, c.name.name ∈ fullCheckableNames) :
    checkSolutionFull m sol = true ↔
      ∃ es, LeanFzn.Solution.parseSolution
          (LeanFzn.Solution.stripSeparators sol) = .ok es ∧
        SatisfiesDyn fullInterp m (LeanFzn.Solution.completedStore m es) := by
  constructor
  · intro htrue
    unfold checkSolutionFull at htrue
    cases hparse : LeanFzn.Solution.parseSolution
        (LeanFzn.Solution.stripSeparators sol) with
    | error _ =>
        rw [hparse] at htrue
        exact absurd htrue (by simp)
    | ok es =>
        rw [hparse] at htrue
        simp only [Bool.and_eq_true, List.all_eq_true] at htrue
        obtain ⟨⟨hassign, hvars⟩, hcons⟩ := htrue
        rw [LeanFzn.Solution.allAssignedB, List.all_eq_true] at hassign
        rw [LeanFzn.Solution.varDeclsOkB, List.all_eq_true] at hvars
        refine ⟨es, hparse.symm ▸ rfl, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          exact (constraintHoldsFullB_iff (hnames c hc)).mp (hcons c hc)
        · -- variable-domain conditions from allAssignedB + varDeclsOkB
          intro d hd
          have hall := hassign d hd
          have hok := hvars d hd
          cases d with
          | basic ty n _anns _opt =>
              cases hstore : (LeanFzn.Solution.completedStore m es) n with
              | none =>
                  have hred : (LeanFzn.Solution.completedStore m es n).isSome = true := hall
                  rw [hstore] at hred
                  exact absurd hred (by simp)
              | some v =>
                  have hred : (match LeanFzn.Solution.completedStore m es n with
                      | some v => LeanFzn.Solution.varTypeContainsB ty v &&
                          LeanFzn.Solution.initializerHoldsB
                            (LeanFzn.Solution.completedStore m es)
                            (VarDeclItem.basic ty n _anns _opt)
                      | none => false) = true := hok
                  rw [hstore] at hred
                  simp only [Bool.and_eq_true] at hred
                  exact ⟨v, hstore, LeanFzn.Solution.varTypeContainsB_iff.mp hred.1⟩
          | array ty n _anns _elems =>
              cases hstore : (LeanFzn.Solution.completedStore m es) n with
              | none =>
                  have hred : (LeanFzn.Solution.completedStore m es n).isSome = true := hall
                  rw [hstore] at hred
                  exact absurd hred (by simp)
              | some v =>
                  have hred : (match LeanFzn.Solution.completedStore m es n with
                      | some (.array vs) =>
                          (decide (vs.length = ty.idx.length) &&
                            vs.all (fun v =>
                              LeanFzn.Solution.varTypeContainsB ty.elem v)) &&
                          LeanFzn.Solution.initializerHoldsB
                            (LeanFzn.Solution.completedStore m es)
                            (VarDeclItem.array ty n _anns _elems)
                      | _ => false) = true := hok
                  rw [hstore] at hred
                  cases v with
                  | bool _ | int _ | setOfInt _ => exact absurd hred (by simp)
                  | array vs =>
                      simp only [Bool.and_eq_true, decide_eq_true_eq,
                        List.all_eq_true] at hred
                      obtain ⟨⟨hlen, helems⟩, _⟩ := hred
                      exact ⟨vs, hstore, hlen, fun v hv =>
                        LeanFzn.Solution.varTypeContainsB_iff.mp (helems v hv)⟩
        · -- initializer conditions from varDeclsOkB
          intro d hd
          have hok := hvars d hd
          have hinit : LeanFzn.Solution.initializerHoldsB
              (LeanFzn.Solution.completedStore m es) d = true := by
            cases d with
            | basic _ty n _anns _opt =>
                cases hstore : (LeanFzn.Solution.completedStore m es) n with
                | none =>
                    have hred : (match LeanFzn.Solution.completedStore m es n with
                        | some v =>
                            LeanFzn.Solution.varTypeContainsB _ty v &&
                              LeanFzn.Solution.initializerHoldsB
                                (LeanFzn.Solution.completedStore m es)
                                (VarDeclItem.basic _ty n _anns _opt)
                        | none => false) = true := hok
                    rw [hstore] at hred
                    exact absurd hred (by simp)
                | some _v =>
                    have hred : (match LeanFzn.Solution.completedStore m es n with
                        | some v =>
                            LeanFzn.Solution.varTypeContainsB _ty v &&
                              LeanFzn.Solution.initializerHoldsB
                                (LeanFzn.Solution.completedStore m es)
                                (VarDeclItem.basic _ty n _anns _opt)
                        | none => false) = true := hok
                    rw [hstore] at hred
                    simp only [Bool.and_eq_true] at hred
                    exact hred.2
            | array _ty n _anns _elems =>
                cases hstore : (LeanFzn.Solution.completedStore m es) n with
                | none =>
                    have hred : (match LeanFzn.Solution.completedStore m es n with
                        | some (.array vs) =>
                            (decide (vs.length = _ty.idx.length) &&
                              vs.all (fun v =>
                                LeanFzn.Solution.varTypeContainsB _ty.elem v)) &&
                            LeanFzn.Solution.initializerHoldsB
                              (LeanFzn.Solution.completedStore m es)
                              (VarDeclItem.array _ty n _anns _elems)
                        | _ => false) = true := hok
                    rw [hstore] at hred
                    exact absurd hred (by simp)
                | some v =>
                    have hred : (match LeanFzn.Solution.completedStore m es n with
                        | some (.array vs) =>
                            (decide (vs.length = _ty.idx.length) &&
                              vs.all (fun v =>
                                LeanFzn.Solution.varTypeContainsB _ty.elem v)) &&
                            LeanFzn.Solution.initializerHoldsB
                              (LeanFzn.Solution.completedStore m es)
                              (VarDeclItem.array _ty n _anns _elems)
                        | _ => false) = true := hok
                    rw [hstore] at hred
                    cases v with
                    | bool _ | int _ | setOfInt _ => exact absurd hred (by simp)
                    | array _vs =>
                        simp only [Bool.and_eq_true] at hred
                        exact hred.2
          exact LeanFzn.Solution.initializerHoldsB_iff.mp hinit
  · rintro ⟨es, hparse, hcons, hvars, hinit⟩
    unfold checkSolutionFull
    rw [hparse]
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩, ?_⟩
    · -- allAssignedB
      intro d hd
      have hdecl := hvars d hd
      cases d with
      | basic _ty n _anns _opt =>
          obtain ⟨v, hstore, _⟩ := hdecl
          have hred : (LeanFzn.Solution.completedStore m es n).isSome = true := by
            rw [hstore]; simp
          show ((LeanFzn.Solution.completedStore m es)
            (VarDeclItem.basic _ty n _anns _opt).name).isSome = true
          exact hred
      | array _ty n _anns _elems =>
          obtain ⟨vs, hstore, _, _⟩ := hdecl
          have hred : (LeanFzn.Solution.completedStore m es n).isSome = true := by
            rw [hstore]; simp
          show ((LeanFzn.Solution.completedStore m es)
            (VarDeclItem.array _ty n _anns _elems).name).isSome = true
          exact hred
    · -- varDeclsOkB
      intro d hd
      have hdecl := hvars d hd
      have hinitd := hinit d hd
      have hinitB : LeanFzn.Solution.initializerHoldsB
          (LeanFzn.Solution.completedStore m es) d = true :=
        LeanFzn.Solution.initializerHoldsB_iff.mpr hinitd
      cases d with
      | basic ty n _anns _opt =>
          cases hstore : (LeanFzn.Solution.completedStore m es) n with
          | none =>
              have hred : ∃ v, LeanFzn.Solution.completedStore m es n = some v ∧
                  ty.contains v := hdecl
              exact absurd hred (by
                intro ⟨v, hn, _⟩
                rw [hstore] at hn
                cases hn)
          | some v =>
              obtain ⟨v', hstore', hcontains⟩ := hdecl
              rw [hstore] at hstore'
              have hvv : v = v' := Option.some.inj hstore'
              show (match LeanFzn.Solution.completedStore m es n with
                | some v => LeanFzn.Solution.varTypeContainsB ty v &&
                    LeanFzn.Solution.initializerHoldsB
                      (LeanFzn.Solution.completedStore m es)
                      (VarDeclItem.basic ty n _anns _opt)
                | none => false) = true
              rw [hstore]
              simp only [Bool.and_eq_true]
              rw [hvv]
              exact ⟨LeanFzn.Solution.varTypeContainsB_iff.mpr hcontains, hinitB⟩
      | array ty n _anns _elems =>
          cases hstore : (LeanFzn.Solution.completedStore m es) n with
          | none =>
              have hred : ∃ vs, LeanFzn.Solution.completedStore m es n =
                  some (Value.array vs) ∧ vs.length = ty.idx.length ∧
                ∀ v ∈ vs, ty.elem.contains v := hdecl
              exact absurd hred (by
                intro ⟨_, hn, _, _⟩
                rw [hstore] at hn
                cases hn)
          | some v =>
              obtain ⟨vs, hstore', hlen, helems⟩ := hdecl
              rw [hstore] at hstore'
              cases v with
              | bool _ | int _ | setOfInt _ =>
                  cases Option.some.inj hstore'
              | array vs' =>
                  have hvs : vs' = vs := by
                    have h1 : Value.array vs' = Value.array vs :=
                      Option.some.inj hstore'
                    exact (Value.array.injEq vs' vs).mp h1
                  have hgoal : (match LeanFzn.Solution.completedStore m es n with
                      | some (.array vs') =>
                          (decide (vs'.length = ty.idx.length) &&
                            vs'.all (fun v =>
                              LeanFzn.Solution.varTypeContainsB ty.elem v)) &&
                          LeanFzn.Solution.initializerHoldsB
                            (LeanFzn.Solution.completedStore m es)
                            (VarDeclItem.array ty n _anns _elems)
                      | _ => false) = true := by
                    rw [hstore]
                    simp only [Bool.and_eq_true, decide_eq_true_eq,
                      List.all_eq_true]
                    have hlen' : vs'.length = ty.idx.length := hvs ▸ hlen
                    have helems' : ∀ v ∈ vs',
                        LeanFzn.Solution.varTypeContainsB ty.elem v = true := by
                      intro v hv
                      exact LeanFzn.Solution.varTypeContainsB_iff.mpr
                        (helems v (hvs ▸ hv))
                    exact ⟨⟨hlen', helems'⟩, hinitB⟩
                  exact hgoal
    · -- constraints
      intro c hc
      exact (constraintHoldsFullB_iff (hnames c hc)).mpr (hcons c hc)

end LeanFzn.Globals
