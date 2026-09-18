/-
File: probeL.lean

Purpose:
  Scratch file exploring Lean string/char lemma availability for the
  emit/parse round-trip theorem (PLAN.md item 2).

Dependencies:
  LeanFzn (Lexer, Solution modules).

Why:
  Development-time exploration. Not part of any build target.

DAG:
  LeanFzn -> probeL.lean (standalone, no dependents)
-/

import LeanFzn

open LeanFzn LeanFzn.Lexer LeanFzn.Solution

-- What String.getElem lemmas exist?
#check @String.getElem_toList
#check @String.toList_append
#check @String.Internal.toArray
example : String.Internal.toArray "ab" = #[ 'a', 'b' ] := by decide
example (s : String) : (String.Internal.toArray s).size = s.length := by exact?
