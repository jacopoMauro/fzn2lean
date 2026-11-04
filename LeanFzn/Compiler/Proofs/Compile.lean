/-
File: LeanFzn/Compiler/Proofs/Compile.lean

Purpose:
  The exact semantic-correspondence theorems for the certified
  FlatZinc fragment compiler (`LeanFzn/Compiler/Compile.lean`).
  Split (P1c) into elaboration-bounded modules to keep the aggregate
  build inside the container's memory budget; this file is now the
  stable re-export shell that preserves the module's public face for
  its importers (`LeanFzn.Compiler.Proofs.Exact`, `LeanFzn.Solver.UIP.Proofs.Fam.AllDiff`,
  and the Direct reference LeanFzn.Solver).

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
    LeanFzn.Compiler.Compile and LeanFzn.Solver.Core).

Why:
  The monolithic module was OOM-killed during elaboration (exit
  137); the split bounds each Lean process's memory. Theorem
  statements are unchanged.

DAG:
  LeanFzn.Compiler.Compile -> Proofs.CompileCore -> Proofs.CompileAux1
    -> Proofs.CompileAux2a -> Proofs.CompileAux2b -> Proofs.CompileAux2c
    -> Proofs.CompileAux2d -> Proofs.Compile (this shell)
    -> Proofs.Exact / LeanFzn.Solver.UIP.Proofs.Fam.AllDiff
-/

import LeanFzn.Compiler.Proofs.CompileCore
import LeanFzn.Compiler.Proofs.CompileAux1
import LeanFzn.Compiler.Proofs.CompileAux2a
import LeanFzn.Compiler.Proofs.CompileAux2b
import LeanFzn.Compiler.Proofs.CompileAux2c
import LeanFzn.Compiler.Proofs.CompileAux2d
import LeanFzn.Compiler.Proofs.CompileAux2e
open LeanFzn.Compiler.Domains

