/-
File: audits/certified_axioms.lean

Purpose:
  CI axiom-profile audit: the public certified theorems must depend
  only on the three standard Lean axioms.

Usage (from the repo root):
  lake env lean audits/certified_axioms.lean
-/

import solver.Direct.Cli
import solver.LCG.Certified

open LeanFzn LeanFzn.Solver.Direct LeanFzn.Solver.LCG

#print axioms solve_sat_correct
#print axioms solve_unsat_correct
#print axioms solveCertified_sat_correct
#print axioms solveCertified_unsat_correct
#print axioms solve_certified_sat
#print axioms solve_certified_unsat
