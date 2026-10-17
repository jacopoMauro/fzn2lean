/-
Purpose: executable wrapper for the activity-ordered LCG route regression.
Dependencies/DAG: HeurLcg -> this executable test entry.
-/
import Tests.Integration.HeurLcg
def main : IO UInt32 := HeurLcgFixtures.main
