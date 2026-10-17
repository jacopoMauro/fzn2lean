/-
File: solver/Direct.lean

Purpose:
  Public umbrella for the checker-independent direct solver scaffold and its
  semantic correctness theorem statements.

Dependencies:
  - solver.Direct.Types/Compile/Search: executable definitions.
  - solver.Direct.Correctness: proof obligations and public theorems.

DAG:
  Direct.Types -> Direct.Compile -> Direct.Search
  Direct.Proofs.* -> Direct.Correctness -> solver.Direct
-/

import solver.Direct.Types
import solver.Direct.Compile
import solver.Direct.Search
import solver.Direct.Correctness
