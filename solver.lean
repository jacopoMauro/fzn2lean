/-
File: solver.lean

Purpose:
  Core root for the direct-solver redevelopment: exports the semantic result
  contract and reusable finite search/domain machinery.

Dependencies:
  solver.Core (shared semantic problem representation), solver.Tree
  (classical tree-search state), solver.LCG (lazy-clause-generation scaffold), solver.Direct
  (checker-independent correctness contract), solver.Search (finite exhaustive
  search), and solver.Domain (domain extraction).

Why:
  The old checker-mediated adapter is intentionally absent from this root.
  Existing optimized components remain available through their own modules
  while they are audited for reuse by the direct solver.

DAG:
  LeanFzn semantics -> solver.Core -> solver.Tree / solver.LCG / solver.Direct
  solver.Search + solver.Domain + solver.Core + solver.Tree + solver.LCG
    + solver.Direct -> solver.lean
-/

import solver.Search
import solver.Domain
import solver.Core
import solver.Tree
import solver.LCG
import solver.Direct
