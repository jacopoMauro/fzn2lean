/-
File: Tests/UIP/OracleRunner.lean

Purpose:
  `lean_exe` root for the T1 oracle/fixture suite. The fixtures live in
  `Tests.UIP.OracleFixtures` with the runner namespaced as `T1Oracle.main`, so that
  any other exe root may import the fixtures without a duplicate root `main`.

DAG:
  Tests/OracleFixtures -> Tests.UIP.OracleRunner (lean_exe `tests_oracle`)
-/

import Tests.UIP.OracleFixtures
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-- Runs the T1 independent oracle/fixture checks. -/
def main : IO UInt32 := T1Oracle.main
