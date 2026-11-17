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
import LeanFzn.Semantics.Globals

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
