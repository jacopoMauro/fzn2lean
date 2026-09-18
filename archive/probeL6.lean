/-
File: probeL6.lean

Purpose:
  Scratch file testing `simp` rules for `Array.getElem!` to inform
  the emit/parse correctness proofs (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution modules).

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn -> probeL6.lean (standalone, no dependents)
-/

import LeanFzn
open LeanFzn LeanFzn.Lexer LeanFzn.Solution
example (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
example (xs : Array Nat) (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h, Option.getD_some]
