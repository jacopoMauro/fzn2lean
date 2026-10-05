/-
File: solver/Direct/Proofs/Compile.lean

Purpose:
  The exact semantic-correspondence theorems for the certified
  FlatZinc fragment compiler (`solver/Direct/Compile.lean`).
  Split (P1c) into elaboration-bounded modules to keep the aggregate
  build inside the container's memory budget; this file is now the
  stable re-export shell that preserves the module's public face for
  its importers (`Direct.Proofs.Exact`, `LCG.Proofs.Fam.AllDiff`,
  and the Direct reference solver).

  - `CompileCore` — lookup lemmas, the compiler inversion, the store
    bridge, constraint exactness, the slot/typing chains, the
    compile-list inversions, the whole-model assembly ingredients,
    and the bool typing chain.
  - `CompileAux1` — the aux-slot expansion's infrastructure: name
    freshness, nameIndex append lemmas, the expansion pre-pass's
    spec/membership inversions, the emitted aux slots' derived
    properties, and the per-piece compile inversions.
  - `CompileAux2a` — the per-shape semantic bridges (SAT and
    coverage), the extended read chains, and the first argument
    inversions.
  - `CompileAux2b` — the remaining argument inversions (two-literal
    times, and/or shapes) and the aux-slot linker's premise chains.
  - `CompileAux2c` — the per-shape name inversions and the per-piece
    successful-compile inversions.

Dependencies:
  - the five split modules above (which in turn depend on
    solver.Direct.Compile and solver.Core).

Why:
  The monolithic module was OOM-killed during elaboration (exit
  137); the split bounds each Lean process's memory. Theorem
  statements are unchanged.

DAG:
  solver.Direct.Compile -> Proofs.CompileCore -> Proofs.CompileAux1
    -> Proofs.CompileAux2a -> Proofs.CompileAux2b -> Proofs.CompileAux2c
    -> Proofs.Compile (this shell)
    -> Proofs.Exact / LCG.Proofs.Fam.AllDiff
-/

import solver.Direct.Proofs.CompileCore
import solver.Direct.Proofs.CompileAux1
import solver.Direct.Proofs.CompileAux2a
import solver.Direct.Proofs.CompileAux2b
import solver.Direct.Proofs.CompileAux2c
