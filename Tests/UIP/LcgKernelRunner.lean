/-
Purpose: executable entry for the fuel-free nonunit LCG kernel fixtures.
Dependencies: LcgKernel defines gated inputs and exhaustive comparisons.
DAG: LcgKernel -> this runner (tests_lcg_kernel).
-/
import Tests.UIP.LcgKernel

def main : IO UInt32 := LcgKernelFixtures.main
