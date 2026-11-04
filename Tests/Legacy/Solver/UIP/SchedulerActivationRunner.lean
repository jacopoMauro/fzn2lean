/-
File: Tests/Legacy/Solver/UIP/SchedulerActivationRunner.lean

Purpose: executable wrapper for the T1 activation observations
(`Tests.Legacy.Solver.UIP.SchedulerActivation`). `Tests.Legacy.Solver.UIP.OracleFixtures` declares the global
top-level `main` for the `tests_oracle` target, so the activation suite lives
in its own module with `T3Activation.main`; this wrapper is the registered
`lean_exe` root.

DAG:
  Tests.Legacy.Solver.UIP.SchedulerActivation -> Tests.Legacy.Solver.UIP.SchedulerActivationRunner
  (lean_exe `tests_lcg_scheduler_activation`)
-/

import Tests.Legacy.Solver.UIP.SchedulerActivation
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-- Runs the T1 activation observation suite. -/
def main : IO UInt32 := T3Activation.main
