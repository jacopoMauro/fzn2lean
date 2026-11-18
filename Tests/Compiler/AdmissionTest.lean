/-
Purpose: Prevent programmatic compiler entries from bypassing T2 admission,
including ground normalization and optimization's satisfaction projection.
Dependencies: Compiler.Objective and Normalize, above Semantics.Admission.
DAG: Source admission -> compiler entries -> these kernel-evaluated tests.
-/
import LeanFzn.Compiler.Objective

open LeanFzn LeanFzn.Compiler
namespace Tests.Compiler.Admission

def blocked (n : String) : Model :=
  ⟨[], [], [.basic (.intRange 0 1) ⟨"objective"⟩ [] none],
    [⟨⟨n⟩, [], []⟩], .satisfy []⟩

def rejected (n : String) : Bool :=
  match compileModelFull (blocked n) with
  | .error _ => true
  | .ok _ => false

def rejectedOpt (n : String) : Bool :=
  match compileModelOpt { blocked n with solve := .minimize [] (.ident ⟨"objective"⟩) } with
  | .error _ => true
  | .ok _ => false

example : rejected "fzn_geost" = true := by decide
example : rejected "fzn_geost_bb" = true := by decide
example : rejected "fzn_geost_smallest_bb" = true := by decide
example : rejected "fzn_cost_mdd" = true := by decide
example : rejected "fzn_mdd_nondet" = true := by decide
example : rejectedOpt "fzn_geost" = true := by decide
example : rejectedOpt "fzn_cost_mdd" = true := by decide

end Tests.Compiler.Admission
