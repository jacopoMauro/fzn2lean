/-
Purpose: executable wrapper for parsed public LCG regressions.
Dependencies/DAG: PublicLcg -> this executable test entry.
-/
import Tests.Integration.PublicLcg
def main : IO UInt32 := PublicLcgFixtures.main
