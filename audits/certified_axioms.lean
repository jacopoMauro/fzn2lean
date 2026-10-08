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
import solver.LCG.Proofs.Run
import solver.LCG.Proofs.FallbackRaw

open LeanFzn LeanFzn.Solver.Direct LeanFzn.Solver.LCG

#print axioms solve_sat_correct
#print axioms solve_unsat_correct
#print axioms solveCertified_sat_correct
#print axioms solveCertified_unsat_correct
#print axioms solve_certified_sat
#print axioms solve_certified_unsat
#print axioms solve_certified_sat_real
#print axioms solve_certified_unsat_real
#print axioms solve_certified_sat_wide
#print axioms propagatorsOfProved_safeUniv
#print axioms propagatorsOfProved_entitled
#print axioms runPropagators_runInv
#print axioms propagateLoop_runInv
#print axioms repair_runInv
#print axioms analysis_ready_at_conflict
#print axioms level0Solved_solvedBy
#print axioms repair0_decision
#print axioms level0Solved_decision
#print axioms level0Solved_repair
#print axioms asserting_true_at_solutions
#print axioms runPropagators_solvedBy_all
#print axioms propagateLoop_solvedBy_any
#print axioms go_unsat_entry_invariant
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_reasonSafeUniv
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_conflictEntitled
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_just
#print axioms LeanFzn.Solver.LCG.initialStateWithRoots_runInv
#print axioms LeanFzn.Solver.LCG.initialStateWithRoots_level0Solved
#print axioms solve_certified_unsat_wide
#print axioms LeanFzn.Solver.LCG.fallbackNogood_entailed
#print axioms LeanFzn.Solver.LCG.fallbackNogood_entailed_by
#print axioms LeanFzn.Solver.LCG.propagateLoop_conflict_nofit_empty
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_fitexcl_nolinle
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_fallbackng
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_fallbackng_discharged
#print axioms LeanFzn.Solver.LCG.orderUpgrade_weaken
#print axioms LeanFzn.Solver.LCG.propagatorOfProvedB5_run
#print axioms LeanFzn.Solver.LCG.propLinLe2_reason_valid
#print axioms LeanFzn.Solver.LCG.propLinLe2_entitled
#print axioms LeanFzn.Solver.LCG.propLinEq2_reason_valid
#print axioms LeanFzn.Solver.LCG.propLinEq2_entitled
#print axioms LeanFzn.Solver.LCG.propTimes_reason_valid
#print axioms LeanFzn.Solver.LCG.propTimes_entitled
#print axioms LeanFzn.Solver.LCG.propAllDiffLCG_fitexcl
#print axioms LeanFzn.Solver.LCG.propAllDiffLCG_entitled
#print axioms LeanFzn.Solver.LCG.linLe2_obstruction_fixed
#print axioms LeanFzn.Solver.LCG.propagatorOfProvedB6_run
#print axioms LeanFzn.Solver.LCG.lin2_fl_hi_lt
#print axioms LeanFzn.Solver.LCG.lin2_cl_neg_lo_gt
#print axioms LeanFzn.Solver.LCG.propagatorsOfProved_conflictraw

#print axioms LeanFzn.Solver.LCG.frontier_sat_leaf
#print axioms LeanFzn.Solver.LCG.frontier_unsat_excludes
#print axioms LeanFzn.Solver.LCG.frontier_sufficient
#print axioms LeanFzn.Solver.LCG.chronological_sat_correct
#print axioms LeanFzn.Solver.LCG.chronological_unsat_correct
#print axioms LeanFzn.Solver.LCG.chronological_sufficient

-- Fuel-free driver (T0): the executable, its measure lemmas, and its
-- coverage/soundness/completeness/total-verdict theorems.
#print axioms LeanFzn.Solver.LCG.branchCost_pos
#print axioms LeanFzn.Solver.LCG.frontierCost_cons
#print axioms LeanFzn.Solver.LCG.frontierCost_expand
#print axioms LeanFzn.Solver.LCG.frontierSolve
#print axioms LeanFzn.Solver.LCG.frontierSolve_sat_leaf
#print axioms LeanFzn.Solver.LCG.frontierSolve_sat_mem
#print axioms LeanFzn.Solver.LCG.frontierSolve_unsat_excludes
#print axioms LeanFzn.Solver.LCG.frontierSolve_complete
#print axioms LeanFzn.Solver.LCG.chronological_total
#print axioms LeanFzn.Solver.Direct.solveCertified_total
