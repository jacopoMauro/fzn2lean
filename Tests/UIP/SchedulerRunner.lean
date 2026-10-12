/-
File: Tests/UIP/SchedulerRunner.lean

Purpose:
  Executable wrapper for the T2a fixture suite (`Tests/SchedulerFixtures`).

  `Tests/OracleFixtures` already declares the global top-level `main` used by
  the `tests_oracle` target, so the scheduler fixtures live in their own module
  with the runner named `T2Fixtures.main`; this two-line wrapper gives Lake a
  registered `lean_exe` root for them (registration is the integration owner's
  job per PLAN.md's shared-file policy).

DAG:
  Tests/SchedulerFixtures -> Tests/SchedulerRunner (lean_exe `tests_lcg_scheduler_fixtures`)
-/

import Tests.UIP.SchedulerFixtures
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-- Runs the T2a scheduler-fixture checks. -/
def main : IO UInt32 := T2Fixtures.main
