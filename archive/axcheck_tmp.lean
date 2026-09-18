/-
File: axcheck_tmp.lean

Purpose:
  Scratch file to verify that key theorems carry no unexpected axioms.
  Prints axiom lists for propagator-preservation lemmas, agreement
  theorems, and the exhaustive-search completeness spec.

Dependencies:
  LeanFzn.Solver (propEqSlot_preserves, allAssigns_spec, etc.).

Why:
  Development-time sanity check. Not part of any build target.

DAG:
  solver.* -> axcheck_tmp.lean (standalone, no dependents)
-/

open LeanFzn.Solver LeanFzn LeanFzn.Solution
#print axioms propEqSlot_preserves
#print axioms propNeSlot_preserves
#print axioms propLeSlot_preserves
#print axioms propConstEq_preserves
#print axioms DomConstraint.satisfiedB_iff
#print axioms allAssigns_mono
#print axioms allAssigns_spec
#print axioms allAssigns_intro
