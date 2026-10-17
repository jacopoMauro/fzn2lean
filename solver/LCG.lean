/-
File: solver/LCG.lean

Purpose:
  Public umbrella for the CP-SAT/lazy-clause-generation solver: the type
  layer, the trail-evaluation and 1-UIP conflict analysis, the L0.1
  encoding semantics, the explanation-carrying propagators, the engine,
  and the proof scaffolds.

DAG:
  Core.Types -> LCG.Types -> LCG.TrailEval -> LCG.Operations
  LCG.Operations -> LCG.Encoding (L0.1 semantic foundation)
  LCG.Operations -> LCG.Propagate -> LCG.Engine
  LCG.Invariants -> LCG.Proofs.Transitions -> LCG.Proofs.Search
  LCG.Engine -> LCG.Search
-/

import solver.LCG.Types
import solver.LCG.TrailEval
import solver.LCG.Operations
import solver.LCG.Encoding
import solver.LCG.Propagate
import solver.LCG.Engine
import solver.LCG.Invariants
import solver.LCG.Search
import solver.LCG.Proofs.Transitions
import solver.LCG.Proofs.Search
import solver.LCG.Proofs.Singleton
import solver.LCG.Proofs.Reachability
import solver.LCG.Proofs.Theory
