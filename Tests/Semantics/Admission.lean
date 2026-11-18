/-
Purpose: Kernel-evaluated boundary regressions for T2 source admission.
Dependencies: Semantics.Admission and its explicit source/model predicates.
DAG: Source semantics -> admission -> these regression proof leaves.
-/
import LeanFzn.Semantics.Admission

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Admission
namespace Tests.Semantics.Admission

def i (n : Int) : Expr := .basic (.lit (.int n))
def a (ns : List Int) : Expr := .array (ns.map (fun n => .lit (.int n)))
def model (name : String) (args : List Expr) : Model :=
  ⟨[], [], [], [⟨⟨name⟩, args, []⟩], .satisfy []⟩

example : admittedB (model "fzn_bin_packing" [i 1, a [1], a [1]]) = true := by decide
example : admittedB (model "fzn_bin_packing" [i (-1), a [], a []]) = false := by decide
example : admittedB (model "fzn_bin_packing" [i 1, a [1], a [-1]]) = false := by decide
example : admittedB (model "fzn_bin_packing" [i 1, a [1], a []]) = false := by decide
example : admittedB (model "fzn_cumulative" [a [0], a [1], a [0], i 0]) = true := by decide
example : admittedB (model "fzn_cumulative" [a [0], a [-1], a [0], i 0]) = false := by decide
example : admittedB (model "fzn_cumulative" [a [], a [1], a [], i 0]) = false := by decide
example : admittedB (model "fzn_cumulatives_decomp"
    [a [0], a [0], a [1], a [0], a [], .basic (.lit (.bool true))]) = false := by decide
example : admittedB (model "fzn_geost" []) = false := by decide
example : admittedB (model "fzn_geost_bb" []) = false := by decide
example : admittedB (model "fzn_geost_smallest_bb" []) = false := by decide
example : admittedB (model "fzn_cost_mdd" []) = false := by decide
example : admittedB (model "fzn_mdd_nondet" []) = false := by decide
example : admittedB (model "fzn_global_cardinality_low_up_closed"
    [a [], a [1], a [], a [0]]) = false := by decide

end Tests.Semantics.Admission
