import LeanFzn.Solver.UIP.Proofs.LcgMixedConflict
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
import LeanFzn.Solver.UIP.Proofs.LcgMixedCompiledKit
import LeanFzn.Solver.UIP.Proofs.LcgMixedCore
import LeanFzn.Solver.UIP.Proofs.LcgMixedDecisions
import LeanFzn.Solver.UIP.Proofs.LcgMixedGood
import LeanFzn.Solver.UIP.Proofs.LcgMixedJump
import LeanFzn.Solver.UIP.Proofs.LcgMixedKitFinal
import LeanFzn.Solver.UIP.Proofs.LcgMixedLiveCoverage
import LeanFzn.Solver.UIP.Proofs.LcgMixedPhaseTerminal
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunDrop
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunStep
/-
File: audits/certified_axioms.lean

Purpose:
  CI axiom-profile audit: the public certified theorems must depend
  only on the three standard Lean axioms.

Usage (from the repo root):
  lake env lean audits/certified_axioms.lean
-/

import LeanFzn.Solver.UIP.Proofs.LcgCanonicalScheduler
import LeanFzn.Solver.UIP.Proofs.LcgCanonicalFamilies
import LeanFzn.Solver.UIP.Proofs.LcgMixedEvents
import LeanFzn.Solver.UIP.Proofs.LcgMixedFrameRun
import LeanFzn.Solver.UIP.Proofs.LcgBooleanPins
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantAbsentShape
import LeanFzn.Solver.Propagation.BoolImplication
import LeanFzn.Solver.UIP.Proofs.LcgPhaseObserved
import LeanFzn.Integration.Lcg
import LeanFzn.Integration.LcgOptimize
import LeanFzn.Integration.LcgSeed
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrameShape
import LeanFzn.Solver.UIP.Proofs.LcgLiveCoverage
import LeanFzn.Solver.UIP.Proofs.LcgPhaseKernel
import LeanFzn.Solver.UIP.Proofs.LcgPhaseTerminal
import LeanFzn.Solver.UIP.Proofs.LcgCompiledKit
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantShape
import LeanFzn.Solver.UIP.Proofs.ConsumeInvariant
import LeanFzn.Solver.UIP.Proofs.SupportedLog
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Integration.Certified
import LeanFzn.Solver.Propagation.Proofs.Run
import LeanFzn.Solver.Propagation.Proofs.FallbackRaw
import LeanFzn.Integration.Proofs.FallbackMulti
import LeanFzn.Solver.Propagation.ExplainedPropagation
import LeanFzn.Solver.Propagation.ConflictResolution
import LeanFzn.Solver.Propagation.AnalysisProgress
import LeanFzn.Solver.Propagation.AnalysisInvariants
import LeanFzn.Solver.Propagation.RestorationCertificate
import LeanFzn.Solver.Propagation.AnalysisCompletion
import LeanFzn.Solver.UIP.Proofs.ConflictResolution
import LeanFzn.Solver.UIP.Proofs.BackjumpFrontier
import LeanFzn.Solver.Chronological.Proofs.AnalysisDriver
import LeanFzn.Solver.UIP.Proofs.CanonicalTrailVocabulary
-- V1 (2026-10-10): new first-UIP chain (R1..P5, W1), X2 driver, D1 entry.
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Solver.UIP.Proofs.SchedulerCoverage
import LeanFzn.Solver.UIP.Proofs.SchedulerFalsified
import LeanFzn.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Solver.UIP.Proofs.SchedulerRank
import LeanFzn.Solver.UIP.Proofs.SchedulerJumpProgress
import LeanFzn.Solver.UIP.Proofs.SchedulerPhaseProgress
import LeanFzn.Solver.UIP.Proofs.SchedulerRun
import LeanFzn.Solver.UIP.Proofs.SchedulerReachClosure
import LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve
import LeanFzn.Solver.UIP.Proofs.DatabaseUnfalsified
import LeanFzn.Solver.UIP.Scheduler
import LeanFzn.Solver.Chronological.Proofs.Search
import LeanFzn.Solver.UIP.Proofs.SchedulerCertifiedRun
-- Session 11: N1/P1/R2a/J1/E1/C1 landings live in the newer proof modules.
import LeanFzn.Solver.UIP.Proofs.SchedulerConflict
import LeanFzn.Solver.UIP.Proofs.ClosureRefutation
import LeanFzn.Solver.UIP.Proofs.PendingRun
import LeanFzn.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Solver.UIP.Proofs.EmissionVocabulary
import LeanFzn.Solver.UIP.Proofs.TrailVocabularyProducers
import LeanFzn.Integration.Proofs.CompiledShape
import LeanFzn.Integration.Proofs.CompiledEntry
import LeanFzn.Integration.Proofs.FallbackPolicy
import LeanFzn.Solver.UIP.Proofs.SupportedProviders
import LeanFzn.Solver.UIP.Proofs.SupportedDead
import LeanFzn.Solver.UIP.Proofs.SupportedArms
-- Session 13: the J1/E1/L1/R2/C1/I1 round modules.
import LeanFzn.Solver.UIP.Proofs.CheckpointPrefix
import LeanFzn.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Solver.UIP.Proofs.SupportedLogSites
import LeanFzn.Solver.UIP.Proofs.ConsumeRun
import LeanFzn.Solver.UIP.Proofs.AnalysisEntail
import LeanFzn.Solver.UIP.Proofs.SiteInhabited
import LeanFzn.Solver.UIP.Proofs.SiteLiveness
import LeanFzn.Solver.UIP.Proofs.FreshCoverless
import LeanFzn.Solver.UIP.Proofs.ExtendedPoolProducers
import LeanFzn.Solver.UIP.Proofs.ClampPool
import LeanFzn.Solver.UIP.Proofs.ClampedRun
import LeanFzn.Solver.UIP.Proofs.ExtendedPoolRank
import LeanFzn.Solver.UIP.Proofs.SupportedInstance
import LeanFzn.Solver.UIP.Proofs.LcgClampTransfer
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantSnap
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrameFalse
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantSync
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrame
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantStep
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantGate
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantReasons
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantTrailStep
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantEvidenceFalse
import LeanFzn.Solver.UIP.Proofs.LcgEvidence
import LeanFzn.Solver.UIP.Proofs.LcgEntailed
import LeanFzn.Solver.UIP.Proofs.LcgAsserting
import LeanFzn.Solver.UIP.Proofs.LcgHbrRefuted
import LeanFzn.Solver.UIP.Proofs.LcgReachable
import LeanFzn.Solver.UIP.Proofs.LcgEvents
import LeanFzn.Solver.UIP.Proofs.LcgRunGood
import LeanFzn.Solver.UIP.Proofs.LcgRunConflict
import LeanFzn.Solver.UIP.Proofs.LcgRunArms
import LeanFzn.Solver.UIP.Proofs.LcgRunJump
import LeanFzn.Solver.UIP.Proofs.LcgRunCert
import LeanFzn.Solver.UIP.Proofs.LcgPropContract
import LeanFzn.Solver.UIP.Proofs.LcgRunPending
import LeanFzn.Solver.UIP.Proofs.LcgRunState
import LeanFzn.Solver.UIP.Proofs.LcgRunStep
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Solver.UIP.Proofs.LcgMixedCompiledKit
import LeanFzn.Solver.UIP.Proofs.LcgKitFinal
import LeanFzn.Solver.UIP.Proofs.LcgEmissionTyped
import LeanFzn.Solver.UIP.Proofs.LcgPropCheck
import LeanFzn.Solver.UIP.Proofs.LcgDecideLive
import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Compiler.Proofs.CompileAux2c
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Compiler.Proofs.Objective
import LeanFzn.Checker.Objective
import LeanFzn.Integration.Optimize
open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn LeanFzn.Compiler LeanFzn.Integration LeanFzn.Solver.Reference LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration

#print axioms solve_sat_correct
#print axioms solve_unsat_correct
#print axioms LeanFzn.Integration.solveCertified_sat_correct
#print axioms LeanFzn.Integration.solveCertified_unsat_correct
#print axioms LeanFzn.Integration.solve_certified_sat
#print axioms LeanFzn.Integration.solve_certified_unsat
#print axioms LeanFzn.Integration.solve_certified_sat_real
#print axioms LeanFzn.Integration.solve_certified_unsat_real
#print axioms LeanFzn.Integration.solve_certified_sat_wide
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_safeUniv
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_entitled
#print axioms LeanFzn.Solver.Propagation.runPropagators_runInv
#print axioms LeanFzn.Solver.Propagation.propagateLoop_runInv
#print axioms LeanFzn.Solver.Propagation.repair_runInv
#print axioms LeanFzn.Solver.Propagation.analysis_ready_at_conflict
#print axioms LeanFzn.Solver.Propagation.level0Solved_solvedBy
#print axioms LeanFzn.Solver.Propagation.repair0_decision
#print axioms LeanFzn.Solver.Propagation.level0Solved_decision
#print axioms LeanFzn.Solver.Propagation.level0Solved_repair
#print axioms LeanFzn.Solver.Propagation.asserting_true_at_solutions
#print axioms LeanFzn.Solver.Propagation.runPropagators_solvedBy_all
#print axioms LeanFzn.Solver.Propagation.propagateLoop_solvedBy_any
#print axioms LeanFzn.Solver.Propagation.go_unsat_entry_invariant
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_reasonSafeUniv
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_conflictEntitled
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_just
#print axioms LeanFzn.Solver.Propagation.initialStateWithRoots_runInv
#print axioms LeanFzn.Solver.Propagation.initialStateWithRoots_level0Solved
#print axioms LeanFzn.Integration.solve_certified_unsat_wide
#print axioms LeanFzn.Solver.Propagation.fallbackNogood_entailed
#print axioms LeanFzn.Solver.Propagation.fallbackNogood_entailed_by
#print axioms LeanFzn.Solver.Propagation.propagateLoop_conflict_nofit_empty
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_fitexcl_nolinle
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_fallbackng
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_fallbackng_discharged
#print axioms LeanFzn.Solver.Propagation.orderUpgrade_weaken
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB5_run
#print axioms LeanFzn.Solver.Propagation.propLinLe2_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinLe2_entitled
#print axioms LeanFzn.Solver.Propagation.propLinEq2_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinEq2_entitled
#print axioms LeanFzn.Solver.Propagation.propTimes_reason_valid
#print axioms LeanFzn.Solver.Propagation.propTimes_entitled
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_fitexcl
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_entitled
#print axioms LeanFzn.Solver.Propagation.linLe2_obstruction_fixed
#print axioms LeanFzn.Solver.Propagation.propagatorOfProvedB6_run
#print axioms LeanFzn.Solver.Propagation.lin2_fl_hi_lt
#print axioms LeanFzn.Solver.Propagation.lin2_cl_neg_lo_gt
#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_conflictraw

#print axioms LeanFzn.Solver.Propagation.frontier_sat_leaf
#print axioms LeanFzn.Solver.Propagation.frontier_unsat_excludes
#print axioms LeanFzn.Solver.Propagation.frontier_sufficient
#print axioms LeanFzn.Solver.Propagation.chronological_sat_correct
#print axioms LeanFzn.Solver.Propagation.chronological_unsat_correct
#print axioms LeanFzn.Solver.Propagation.chronological_sufficient

-- Fuel-free driver (T0): the executable, its measure lemmas, and its
-- coverage/soundness/completeness/total-verdict theorems.
#print axioms LeanFzn.Solver.Propagation.branchCost_pos
#print axioms LeanFzn.Solver.Propagation.frontierCost_cons
#print axioms LeanFzn.Solver.Propagation.frontierCost_expand
#print axioms LeanFzn.Solver.Propagation.frontierSolve
#print axioms LeanFzn.Solver.Propagation.frontierSolve_sat_leaf
#print axioms LeanFzn.Solver.Propagation.frontierSolve_sat_mem
#print axioms LeanFzn.Solver.Propagation.frontierSolve_unsat_excludes
#print axioms LeanFzn.Solver.Propagation.frontierSolve_complete
#print axioms LeanFzn.Solver.Propagation.chronological_total
#print axioms LeanFzn.Integration.solveCertified_total

-- Active finite-domain propagation/learning frontier and source activation.
#print axioms LeanFzn.Solver.Chronological.prunedSolve
#print axioms LeanFzn.Solver.Chronological.prunedSolve_sat_leaf
#print axioms LeanFzn.Solver.Chronological.prunedSolve_unsat_excludes
#print axioms LeanFzn.Solver.Chronological.prunedSolve_complete
#print axioms LeanFzn.Solver.Propagation.filterFrame_preserves
#print axioms LeanFzn.Solver.Propagation.filterFrame_cost_le
#print axioms LeanFzn.Solver.Propagation.clauseRemaining_singleton_implies
#print axioms LeanFzn.Solver.Propagation.boxPropagators_safe
#print axioms LeanFzn.Solver.Propagation.boxPropagators_reasons
#print axioms LeanFzn.Solver.Propagation.boxPropagators_conflicts
#print axioms LeanFzn.Solver.Propagation.propagationClosure_cost_le
#print axioms LeanFzn.Solver.Propagation.propagationClosure_preserves
#print axioms LeanFzn.Solver.Propagation.propagationClosure_learns
#print axioms LeanFzn.Solver.Propagation.domPropagationContract
#print axioms LeanFzn.Integration.compiled_domPruningOk
#print axioms LeanFzn.Solver.Chronological.solve_total

/-! ### P1 branch-state / explanation-trail / analysis / backjump layer -/

#print axioms LeanFzn.Solver.Propagation.BranchState.init_wellFormed
#print axioms LeanFzn.Solver.Propagation.BranchState.decide_wellFormed
#print axioms LeanFzn.Solver.Propagation.BranchState.recordImplied_wellFormed
#print axioms LeanFzn.Solver.Propagation.BranchState.restoreLevel_represents
#print axioms LeanFzn.Solver.Propagation.rootFactsOfDomains_sound
#print axioms LeanFzn.Solver.Propagation.explainedTrail_wellFormed
#print axioms LeanFzn.Solver.Propagation.explainedTrail_len_le
#print axioms LeanFzn.Solver.Propagation.projectedClosure_frame_eq
#print axioms LeanFzn.Solver.Propagation.projectedClosure_learned_eq
#print axioms LeanFzn.Solver.Propagation.explainedStep_of_deduction
#print axioms LeanFzn.Solver.Propagation.explainedDeduction_event
#print axioms LeanFzn.Solver.Propagation.explainedDeduction_learned_entailed
#print axioms LeanFzn.Solver.Propagation.stepChronology_of_domReasonRecorded
#print axioms LeanFzn.Solver.Propagation.explainedClosure_coverage
#print axioms LeanFzn.Solver.Propagation.domExplainedContract
#print axioms LeanFzn.Solver.Propagation.analyzeAtAllowance_fuel_eq
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_mono
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_mono_le
#print axioms LeanFzn.Solver.Propagation.impliesP_sound
#print axioms LeanFzn.Solver.Propagation.pivotCost_filter_lt
#print axioms LeanFzn.Solver.Propagation.litFalseAtRoot_sound
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_inv
#print axioms LeanFzn.Solver.Propagation.levelSorted_append
#print axioms LeanFzn.Solver.Propagation.nextPivot_mark
#print axioms LeanFzn.Solver.Propagation.markLit_invariants
#print axioms LeanFzn.Solver.Propagation.analyzeStep_invariants
#print axioms LeanFzn.Solver.Propagation.analyzeStep_uip_on_trail
#print axioms LeanFzn.Solver.Propagation.analyzeTrail_belowFalsified
#print axioms LeanFzn.Solver.Propagation.analyzeTrail_uip_on_trail
#print axioms LeanFzn.Solver.Propagation.findEntryOf_last_match
#print axioms LeanFzn.Solver.Propagation.falsifier_level_le
#print axioms LeanFzn.Solver.Propagation.below_pair_facts
-- NOTE: `foldl_max_lt` is deliberately not profiled: it is axiom-free
-- ("does not depend on any axioms"), which the audit's profile regex treats as
-- a malformed line. Its use is covered through `analyzeTrail_certificate`.
#print axioms LeanFzn.Solver.Propagation.analyzeTrail_certificate
#print axioms LeanFzn.Solver.Propagation.findEntryOf_not_after_pivot
#print axioms LeanFzn.Solver.Propagation.pivotFrontier_no_advance
#print axioms LeanFzn.Solver.Propagation.earlierThan_irrefl
#print axioms LeanFzn.Solver.Propagation.earlierThan_asymm
#print axioms LeanFzn.Solver.Propagation.reason_not_negate_pivot
#print axioms LeanFzn.Solver.Propagation.reason_falsifier_not_after_pivot
#print axioms LeanFzn.Solver.Propagation.analyzerPotential_lt_of_next
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_snd
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_mono
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_exists_of_potential
#print axioms LeanFzn.Solver.Propagation.analysis_complete
#print axioms LeanFzn.Solver.Propagation.analyzeAtAllowance_stops
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_holds
#print axioms LeanFzn.Solver.Propagation.analyzeAtAllowance_learnedEntailed
#print axioms LeanFzn.Solver.Propagation.analyzeAtAllowance_certificate
#print axioms LeanFzn.Solver.Propagation.removedValue_excluded
#print axioms LeanFzn.Solver.Propagation.derivedLower_correct
#print axioms LeanFzn.Solver.Propagation.valueLiteral_holds_iff
#print axioms LeanFzn.Solver.Propagation.decide_represents_iff
#print axioms LeanFzn.Solver.UIP.trailFalsifies_eval_false
#print axioms LeanFzn.Solver.UIP.conflict_excludes_solution
#print axioms LeanFzn.Solver.UIP.branchNogood_entailed
#print axioms LeanFzn.Solver.UIP.analyzeConflict_contract
#print axioms LeanFzn.Solver.Propagation.BackjumpPlan.execute_wellFormed
#print axioms LeanFzn.Solver.Propagation.BackjumpPlan.execute_represents_forward
#print axioms LeanFzn.Solver.UIP.classification_retains
#print axioms LeanFzn.Solver.Propagation.ClassificationSound.trans

/-! ### Integrated analysed driver (P1.D/E) -/

#print axioms LeanFzn.Solver.Chronological.frontierCost_prune_le
#print axioms LeanFzn.Solver.Chronological.frontierCost_prune_expand
#print axioms LeanFzn.Solver.Chronological.refutedBy_not_leaf
#print axioms LeanFzn.Solver.Chronological.pruneFrames_preserves
#print axioms LeanFzn.Solver.Chronological.analyzedSolve_sat_leaf
#print axioms LeanFzn.Solver.Chronological.analyzedSolve_unsat_excludes

/-! ### A1 full-box projection, frame/trail bridge, reachable invariant -/

#print axioms LeanFzn.Solver.Propagation.fullDomains_prefix
#print axioms LeanFzn.Solver.Propagation.fullDomains_remaining
#print axioms LeanFzn.Solver.Propagation.Frame.domains_subsets
#print axioms LeanFzn.Solver.Propagation.TrailAgreesFrame_filterFrame
#print axioms LeanFzn.Solver.Propagation.eq_append_of_prefix_agrees
#print axioms LeanFzn.Solver.Propagation.mem_allAssigns_of_getElem?
#print axioms LeanFzn.Solver.Propagation.frame_covers_of_trail
#print axioms LeanFzn.Solver.Propagation.fullDomains_decide_subset
#print axioms LeanFzn.Solver.Propagation.allAssigns_cons_of_mem
#print axioms LeanFzn.Solver.Propagation.FrameCovers_decide
#print axioms LeanFzn.Solver.Propagation.reachable_init
#print axioms LeanFzn.Solver.Propagation.reachable_decide

/-! ### A2 resident explained step -/

#print axioms LeanFzn.Solver.Propagation.norm_valueHolds
#print axioms LeanFzn.Solver.Propagation.filterSlots_valueHolds
#print axioms LeanFzn.Solver.Propagation.filterFrame_literal_holds
#print axioms LeanFzn.Solver.Propagation.FrameCovers_of_subsets
#print axioms LeanFzn.Solver.Propagation.filterSlots_removed
#print axioms LeanFzn.Solver.Propagation.filterFrame_removal_witness
#print axioms LeanFzn.Solver.Propagation.explainedStep_narrow_coverage
#print axioms LeanFzn.Solver.Propagation.explainedStep_narrow_reachable
#print axioms LeanFzn.Solver.Propagation.explainedStep_excluded_entailed
#print axioms LeanFzn.Solver.Propagation.explainedStep_stable_shape
#print axioms LeanFzn.Solver.Propagation.explainedStep_excluded_shape
#print axioms LeanFzn.Solver.Propagation.explainedStep_narrow_shape
#print axioms LeanFzn.Solver.Propagation.explainedStep_nonproductive_shape
#print axioms LeanFzn.Solver.Propagation.explainedStep_nofilter_shape

/-! ### V1 (2026-10-10): first-UIP scheduler chain, rank, whole-run, D1 entry -/

-- R1 reachability and F1-shape exclusion
#print axioms LeanFzn.Solver.UIP.evidenceProvenance_of_reachable
#print axioms LeanFzn.Solver.UIP.reachable_analysis_success
#print axioms LeanFzn.Solver.UIP.analysisSuccess_learned_ne_nil
-- P1 vocabulary
#print axioms LeanFzn.Solver.UIP.canonicalClause_mem_clausePool_of_sublist
#print axioms LeanFzn.Solver.UIP.clausePool_lits_mem
-- S1 typed decisions
#print axioms LeanFzn.Solver.UIP.stepDecide_bool_invariant
#print axioms LeanFzn.Solver.UIP.stepDecide_bool_reachableLearnedProvenance
-- S4 coverage, database entailment
#print axioms LeanFzn.Solver.UIP.stepLearnBackjumpAssert_coverage_of_recorded_analysis
#print axioms LeanFzn.Solver.UIP.entailed_db_never_excludes
-- F1-adjacent falsified-shape refutations
#print axioms LeanFzn.Solver.UIP.analyzeAtAllowance_gap_run
#print axioms LeanFzn.Solver.UIP.gap_run_not_falsifiedByTrail
-- P2 novelty classification
#print axioms LeanFzn.Solver.UIP.jumpNovelty_of_unfalsified
#print axioms LeanFzn.Solver.UIP.not_jumpRepeated_of_unfalsified
-- P3 non-jump rank
#print axioms LeanFzn.Solver.UIP.P3.phaseRank_lt_localExclude_then_consume
#print axioms LeanFzn.Solver.UIP.P3.analyzeConflictCounted_not_repeated
-- P4 jump progress
#print axioms LeanFzn.Solver.UIP.P4.phaseLt_stepLearnBackjumpAssert_of_reachable
-- P5 reachable termination
#print axioms LeanFzn.Solver.UIP.P5.runReachable_total
-- W1 whole-run verdicts
#print axioms LeanFzn.Solver.UIP.W1.runPhase_sat_solution
#print axioms LeanFzn.Solver.UIP.W1.runPhase_unsat_excludes
#print axioms LeanFzn.Solver.UIP.W1.runPhase_total
-- hbr assembly (reach-closure / arms-preserve)
#print axioms LeanFzn.Solver.UIP.reachableBranchInvariant_of_preservation
#print axioms LeanFzn.Solver.UIP.hbr_of_preservation
#print axioms LeanFzn.Solver.UIP.stepLearnBackjumpAssert_branch_reachable
#print axioms LeanFzn.Solver.UIP.hbr_of_reachPreserve
-- DatabaseUnfalsified (except variant + witnesses)
#print axioms LeanFzn.Solver.UIP.jumpNovelty_of_except
#print axioms LeanFzn.Solver.UIP.databaseUnfalsified_of_except_not_mem
-- X2 compiled recursion and its agreement theorem
#print axioms LeanFzn.Solver.UIP.X2.runPhase
#print axioms LeanFzn.Solver.UIP.X2.runPhase_eq_runReachable
-- D1 public driver entry (conditional on CompiledPhasePremises)
#print axioms LeanFzn.Solver.UIP.solvePhaseCompiled_eq_runReachable
#print axioms LeanFzn.Solver.UIP.solvePhaseCompiled_sat_solution
#print axioms LeanFzn.Solver.UIP.solvePhaseCompiled_unsat_excludes
#print axioms LeanFzn.Solver.UIP.solvePhaseCompiled_total

-- C1 (2026-10-11): unit-emission vocabulary, payload producers, run-level halignDB
#print axioms LeanFzn.Solver.UIP.unitEmissionVocabulary_runProfile
#print axioms LeanFzn.Solver.UIP.databaseAligned_deduction_learned
#print axioms LeanFzn.Solver.UIP.databaseAligned_conflict_learned
#print axioms LeanFzn.Solver.UIP.databaseAligned_terminalResult_conflict
#print axioms LeanFzn.Solver.Propagation.terminalResult_ne_localExcluded
#print axioms LeanFzn.Solver.UIP.databaseAligned_explainedClosure
#print axioms LeanFzn.Solver.UIP.databaseAligned_perform
#print axioms LeanFzn.Solver.UIP.databaseAlignedStep
#print axioms LeanFzn.Solver.UIP.databaseAlignedAndEvidence_of_supportedRun
#print axioms LeanFzn.Solver.UIP.halignDB_of_supportedRun
#print axioms LeanFzn.Solver.UIP.databaseAlignedAndEvidence_of_reachable
#print axioms LeanFzn.Solver.UIP.halignDB_of_reachable
-- C1 canonical resume trail vocabulary
#print axioms LeanFzn.Solver.UIP.valueLiteral_norm_mem_litPool
#print axioms LeanFzn.Solver.UIP.valueLiteral_negate_norm_mem_litPool
#print axioms LeanFzn.Solver.UIP.canonicalPins_vocabulary
#print axioms LeanFzn.Solver.UIP.canonicalFalsifiers_vocabulary
#print axioms LeanFzn.Solver.UIP.canonicalTrail_vocabulary
#print axioms LeanFzn.Solver.UIP.resumePending_branchTrailVocabulary
#print axioms LeanFzn.Solver.UIP.resumePending_databaseAligned
#print axioms LeanFzn.Solver.UIP.recordedAnalysis_learned_poolAligned_of_resumePending

-- F1 (2026-10-11): compiled-input shape + supported-input assembly (CompiledShape/CompiledEntry)
#print axioms LeanFzn.Integration.shapeTypedDomains_of_compileModel
#print axioms LeanFzn.Integration.shapeTypedDomains_of_compileModel_toLCG
#print axioms LeanFzn.Integration.intViewedDomains_of_shapeTyped
#print axioms LeanFzn.Integration.supportedInput_of_compiled
#print axioms LeanFzn.Integration.supportedInput_of_compiled_toLCG
#print axioms LeanFzn.Integration.boolNot_recorded_fails
-- F1 (2026-10-11): coverage matrix and proved fallback (FallbackMulti)
#print axioms LeanFzn.Integration.unitEvidenceRoute_iff_class
#print axioms LeanFzn.Integration.unitEvidenceRoute_not_general
#print axioms LeanFzn.Integration.unitEvidence_familyRoute_explained
#print axioms LeanFzn.Integration.fallbackRoute_total
#print axioms LeanFzn.Integration.unitFamily_propagatorEvidence
#print axioms LeanFzn.Integration.boolNotRegistered_recorded_fails
#print axioms LeanFzn.Integration.compiled_boolNotFragment_evidence_fails
#print axioms LeanFzn.Integration.fallbackFitexcl_boolNotSlot
#print axioms LeanFzn.Integration.fallbackFitexcl_eqSlot
#print axioms LeanFzn.Integration.fallbackFitexcl_linEq
#print axioms LeanFzn.Integration.fallbackFitexcl_allDiff
#print axioms LeanFzn.Integration.fallbackCoverage_nonempty_of_proved
#print axioms LeanFzn.Integration.fallbackCoverage_empty_of_proved
#print axioms LeanFzn.Integration.fallbackCoverage_of_proved
#print axioms LeanFzn.Integration.compiled_hfallbackng_of_compileModel
#print axioms LeanFzn.Integration.compiled_hconfent_norm_of_compileModel
#print axioms LeanFzn.Integration.compiled_hconfraw_of_compileModel
#print axioms LeanFzn.Integration.fallbackCoverage_of_compiled
-- Session 11 (2026-10-12): N1 acceptance, the P1 closure-contract repair
-- (UnitDB gate + retained refutation), R2a/J1/E1/C1 producer landings.
#print axioms LeanFzn.Solver.UIP.unitRunInvariant_of_reachable
#print axioms LeanFzn.Solver.UIP.unitRunInvariant_step
#print axioms LeanFzn.Solver.UIP.chronology_without_unitGate_false
#print axioms LeanFzn.Solver.UIP.hShape_false_at_refBs
#print axioms LeanFzn.Solver.Propagation.unitPayload_of_unitKit
#print axioms LeanFzn.Solver.Propagation.deduction_reason_unit_lower
#print axioms LeanFzn.Solver.UIP.pendingSideInv_of_premises
#print axioms LeanFzn.Solver.UIP.supportedHdeadCheckpointRegion_of_snapshots
#print axioms LeanFzn.Solver.UIP.supportedHpre_of_snapshots
#print axioms LeanFzn.Solver.UIP.supportedHstable_of_reach
#print axioms LeanFzn.Solver.UIP.supportedHcert_of_premises
#print axioms LeanFzn.Solver.UIP.negStable_posBool_refuted
#print axioms LeanFzn.Solver.UIP.unitEmissionVocabulary_proved_of_thresholds
#print axioms LeanFzn.Solver.UIP.emitted_threshold_not_pooled
#print axioms LeanFzn.Solver.UIP.deduction_literal_pooled
#print axioms LeanFzn.Solver.UIP.branchTrailVocabulary_supportedRun_evidenceSites
#print axioms LeanFzn.Solver.UIP.supportedHclos_of_compiled
#print axioms LeanFzn.Solver.UIP.perform_reachable_of_pre
#print axioms LeanFzn.Solver.UIP.supportedCoreGates_of_producers
#print axioms LeanFzn.Solver.UIP.supportedReachAndEvidence_of_premises
#print axioms LeanFzn.Solver.Propagation.explainedClosure_reachable
#print axioms LeanFzn.Solver.Propagation.explainedClosureResult_spec
#print axioms LeanFzn.Solver.Propagation.explainedDeduction_narrow_reachable
#print axioms LeanFzn.Solver.UIP.hshape_of_unitLearned
#print axioms LeanFzn.Solver.UIP.unitClauseEvidence_of_provenance
-- Session 12 (2026-10-12): R2 consume unification + supported hconsume,
-- J1 avoiding-form restoration + unit-run instantiation, C1 extended pool.
#print axioms LeanFzn.Solver.UIP.stepConsume_reachable_of_inv
#print axioms LeanFzn.Solver.UIP.supportedHconsume_of_premises
#print axioms LeanFzn.Solver.UIP.stepConsume_branch
#print axioms LeanFzn.Solver.UIP.literal_negate_norm_eval_false
#print axioms LeanFzn.Solver.UIP.resumeSibling_shadow_not_represents
#print axioms LeanFzn.Solver.UIP.restorationPreReachable_of_success_avoiding
#print axioms LeanFzn.Solver.UIP.supportedHpre_of_unitRun
#print axioms LeanFzn.Solver.UIP.supportedHneg_of_unitRun
#print axioms LeanFzn.Solver.UIP.supportedLearned_eq_asserting_of_unitRun
#print axioms LeanFzn.Solver.UIP.identifies_survives_strict
#print axioms LeanFzn.Solver.UIP.othersBelow_falsifier_at_target
#print axioms LeanFzn.Solver.UIP.strict_hsurv_insufficient_for_chronology
#print axioms LeanFzn.Solver.UIP.unitEmissionVocabulary_proved_litPoolExt
#print axioms LeanFzn.Solver.UIP.litPoolExt_length_le
#print axioms LeanFzn.Solver.UIP.emissionVocabularyAt_litPoolExt
#print axioms LeanFzn.Solver.UIP.emissionLits_mem_litPoolExt
#print axioms LeanFzn.Solver.Propagation.negStableAvoiding_of_learned_eq_singleton
-- Session 12 addendum: E1 premise-discharge wrapper + F1 routing policy.
#print axioms LeanFzn.Solver.UIP.supportedHdeadCheckpointRegion_of_premises
#print axioms LeanFzn.Integration.firstUIPRoute_supportedInput
#print axioms LeanFzn.Integration.firstUIPRoute_false_witness
#print axioms LeanFzn.Integration.multipleResolution_obligation_retained
-- Session 12 round 3 addendum: the triple joint induction + consume route.
#print axioms LeanFzn.Solver.UIP.pendingSideInv_supportedStep

#print axioms LeanFzn.Solver.UIP.stepConsume_invariant_of_components
#print axioms LeanFzn.Solver.UIP.supportedLogSound_of_newRegions
#print axioms LeanFzn.Solver.UIP.newRegionsSound_of_regions_eq
#print axioms LeanFzn.Solver.UIP.newRegionsSound_of_register
-- Session 13 addendum: J1 hsurv/hfresh/hrange, E1 of_reach, L1 sites,
-- R2 consume run, C1 extended pool/rank, I1 chain + unit-kit instance.
#print axioms LeanFzn.Solver.UIP.checkpointsStrictPrefix_of_reach
#print axioms LeanFzn.Solver.UIP.supportedHsurv_of_reach
#print axioms LeanFzn.Solver.UIP.supportedHdeadCheckpointRegion_of_reach
#print axioms LeanFzn.Solver.UIP.supportedHpre_of_unitRun_reach
#print axioms LeanFzn.Solver.UIP.supportedNewRegionsSound_of_premises
#print axioms LeanFzn.Solver.UIP.supportedLogSound_of_premises
#print axioms LeanFzn.Solver.UIP.supportedHconsumeInv_of_coverage
#print axioms LeanFzn.Solver.UIP.hAnalysisEntail_unitKit
#print axioms LeanFzn.Solver.UIP.cexNotAllSites
#print axioms LeanFzn.Solver.UIP.supportedInhabited_or_coverless
#print axioms LeanFzn.Solver.UIP.recordedInhabited_false
#print axioms LeanFzn.Solver.UIP.supportedHfresh_of_reach_or_coverless
#print axioms LeanFzn.Solver.UIP.unitKit_backjumpLevel_eq_zero
#print axioms LeanFzn.Solver.UIP.supportedReachEvidenceChain_of_premises
#print axioms LeanFzn.Solver.UIP.supportedCoreGates_unitKit
#print axioms LeanFzn.Solver.UIP.halignDB_litPoolExt_of_supportedRun
#print axioms LeanFzn.Solver.UIP.trailInvWith_of_supportedRun
-- Solution checker front door (checker-fixes import, 2026-10-12).
#print axioms LeanFzn.Checker.checkModelSolution_correct
#print axioms LeanFzn.Checker.checkModelSolution_accepted
#print axioms LeanFzn.Checker.checkModelSolutionFast_eq
#print axioms LeanFzn.Checker.Solution.completedStore_entry
#print axioms LeanFzn.Checker.Solution.completedStore_paramHonest
#print axioms LeanFzn.Compiler.compileFull_exact
#print axioms LeanFzn.Compiler.compileFull_covers
#print axioms LeanFzn.Compiler.compileFull_covers_agree
#print axioms LeanFzn.Compiler.compileOpt_exact
#print axioms LeanFzn.Compiler.compileOpt_covers
#print axioms LeanFzn.Compiler.compileOpt_optimal
#print axioms LeanFzn.Checker.checkedObjective_sound
#print axioms LeanFzn.Integration.optLoop_inv
#print axioms LeanFzn.Integration.optLoop_complete
#print axioms LeanFzn.Integration.optimizeCertified_solution_sound
#print axioms LeanFzn.Integration.optimizeCertified_improving
#print axioms LeanFzn.Integration.optimizeCertified_optimal
#print axioms LeanFzn.Integration.optimizeCertified_unsat
#print axioms LeanFzn.Integration.optimizeCertified_total
-- B1: streaming emission of improving solutions.
#print axioms LeanFzn.Integration.optLoopEmit_eq
#print axioms LeanFzn.Integration.optLoopEmit_fst
#print axioms LeanFzn.Integration.optLoopEmit_snd
#print axioms LeanFzn.Integration.optimizeStreamLoop_emit
#print axioms LeanFzn.Integration.optimizeStreamLoop_trace
#print axioms LeanFzn.Integration.optimizeStream_eq
#print axioms LeanFzn.Integration.chronVerdict_sat
#print axioms LeanFzn.Integration.chronVerdict_unsat
#print axioms LeanFzn.Integration.chronSolver

-- R1c (2026-10-13): conflict routing, wipe-out clause, seeded root, unit-kit gate
#print axioms LeanFzn.Solver.Propagation.wipeoutClause_entailed
#print axioms LeanFzn.Solver.Propagation.wipeoutClause_falsified
#print axioms LeanFzn.Solver.Propagation.wipeoutClause_excludes
#print axioms LeanFzn.Solver.Propagation.terminalResult_spec
#print axioms LeanFzn.Solver.Propagation.terminalResult_conflict_cases
#print axioms LeanFzn.Solver.Propagation.reachable_seed
#print axioms LeanFzn.Solver.UIP.schedulerInvariant_init
#print axioms LeanFzn.Solver.UIP.unitRunInvariant_of_supported
#print axioms LeanFzn.Solver.UIP.recordedStep_is_propagatorConflict
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propSem_iff
#print axioms LeanFzn.Solver.UIP.LcgFamilies.narrowHi_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.narrowLo_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLeConstHi_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propConstEq_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propBoolNot_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propBoolAnd_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propBoolOr_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLe_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLt_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propEq_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propPlus_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinLe2_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinEq2_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propNe_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propAllDiffLCG_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propSem_of_family
#print axioms LeanFzn.Solver.UIP.LcgFamilies.runSemContract_of_families
#print axioms LeanFzn.Solver.UIP.LcgFamilies.lcgKit_gate_of_families
#print axioms LeanFzn.Solver.UIP.LcgFamilies.boolNot_sparse_semOK
#print axioms LeanFzn.Solver.UIP.ClampPool.snapLit_eval
#print axioms LeanFzn.Solver.UIP.ClampPool.snapClause_satisfied
#print axioms LeanFzn.Solver.UIP.ClampPool.snapLit_norm
#print axioms LeanFzn.Solver.UIP.ClampPool.snapLit_norm_mem_litPool
#print axioms LeanFzn.Solver.UIP.ClampPool.emissionPoolAt_clampProps
#print axioms LeanFzn.Solver.UIP.ClampedRun.halignDB_of_clampedRun
#print axioms LeanFzn.Solver.UIP.ClampedRun.ClampedPhasePremises.toPremises
#print axioms LeanFzn.Solver.UIP.LcgClamp.litFalseAtRoot_snap
#print axioms LeanFzn.Solver.UIP.LcgClamp.semFalsified_snap
#print axioms LeanFzn.Solver.UIP.LcgClamp.semReasonOK_snap
#print axioms LeanFzn.Solver.UIP.LcgClamp.snap_conflict
#print axioms LeanFzn.Solver.UIP.LcgClamp.propSem_clamp
#print axioms LeanFzn.Solver.UIP.LcgRunInv.snapLit_fixed_of_pool
#print axioms LeanFzn.Solver.UIP.LcgRunInv.trailSnapFixed_of_clampedRun
#print axioms LeanFzn.Solver.UIP.LcgRunInv.boolPin_witness_on_run
#print axioms LeanFzn.Solver.UIP.LcgRunInv.first_step_bool_decision
#print axioms LeanFzn.Solver.UIP.LcgRunInv.syncOne_covers
#print axioms LeanFzn.Solver.UIP.LcgRunInv.syncCands_ok
#print axioms LeanFzn.Solver.UIP.LcgRunInv.explSlot_of_covers
#print axioms LeanFzn.Solver.UIP.LcgRunInv.syncAll_explains
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_narrow_sync
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_split
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_resume
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_closure
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_perform
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameRun_step
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameRun_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameExplainedFull_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgRunInv.runSemContract_intBox
#print axioms LeanFzn.Solver.UIP.LcgRunInv.lcgKit_gate_intBox
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameFalse_sem
#print axioms LeanFzn.Solver.UIP.LcgRunInv.nextPruningEvent_implied_sem
#print axioms LeanFzn.Solver.UIP.LcgRunInv.trailSem_closure
#print axioms LeanFzn.Solver.UIP.LcgRunInv.trailSem_perform
#print axioms LeanFzn.Solver.UIP.LcgRunInv.trailRun_step
#print axioms LeanFzn.Solver.UIP.LcgRunInv.trailRun_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgRunInv.wipeoutOk_of_fits
#print axioms LeanFzn.Solver.UIP.LcgRunInv.lcgRunInv_of_residual
#print axioms LeanFzn.Solver.UIP.LcgRunInv.evidence_refuted
#print axioms LeanFzn.Solver.UIP.LcgRunInv.evidenceRun_refuted
#print axioms LeanFzn.Solver.UIP.LcgRunInv.impliesBase_sound_value
#print axioms LeanFzn.Solver.UIP.LcgRunInv.literalImpossible_of_sem
#print axioms LeanFzn.Solver.UIP.LcgRunInv.dbSemUnfalsified_of_stableScan
#print axioms LeanFzn.Solver.UIP.LcgRunInv.productive_false_of_redundant
#print axioms LeanFzn.Solver.UIP.LcgRunInv.closure_at_decide
#print axioms LeanFzn.Solver.UIP.LcgEvidence.analysis_some_conflict_semFalsified
#print axioms LeanFzn.Solver.UIP.LcgEvidence.evidenceRunCond_holds
#print axioms LeanFzn.Solver.UIP.LcgEvidence.lcgRunInvCond_of_residual
#print axioms LeanFzn.Solver.UIP.LcgEvidence.evidence_witness_analysis_none
#print axioms LeanFzn.Solver.UIP.LcgEntailed.entailedRun_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgEntailed.lcgRunInvCond_of_residual_noEnt
#print axioms LeanFzn.Solver.UIP.LcgAsserting.checkpoint_covers_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgAsserting.semFalsifiedBefore_of_others
#print axioms LeanFzn.Solver.UIP.LcgAsserting.assertingSem_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgAsserting.lcgRunInvCond_of_residual_noAss
#print axioms LeanFzn.Solver.UIP.LcgHbrRefuted.not_wf_of_badChrono
#print axioms LeanFzn.Solver.UIP.LcgHbrRefuted.witness_badChrono
#print axioms LeanFzn.Solver.UIP.LcgHbrRefuted.hbr_refuted
#print axioms LeanFzn.Solver.UIP.LcgReachable.trailSem_of_wf
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgReachable_of_reachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.LcgReachableState.wf_nochron
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgReachable_decide
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgReachable_recordImplied
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgReachable_learnGlobal
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgReachable_restoreLevel
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgExplainedStep_narrow_reachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.syncOne_lcgReachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.syncSlot_lcgReachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.syncAll_lcgReachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.stepNarrowSync_lcgReachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgExplainedDeduction_narrow_reachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgExplainedClosure_reachable
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgPerform_reachable_of_narrowFrame
#print axioms LeanFzn.Solver.UIP.LcgReachable.lcgPerform_reachable_of_pre
#print axioms LeanFzn.Solver.UIP.LcgEvents.slot_lt_of_productive
#print axioms LeanFzn.Solver.UIP.LcgEvents.lcgEventPremise_of_kit
#print axioms LeanFzn.Solver.UIP.LcgEvents.lcgEvent_of_kit_at
#print axioms LeanFzn.Solver.UIP.LcgRunGood.explainedClosure_induction
#print axioms LeanFzn.Solver.UIP.LcgRunGood.LcgGood.stepNarrowSync
#print axioms LeanFzn.Solver.UIP.LcgRunGood.LcgGood.closure
#print axioms LeanFzn.Solver.UIP.LcgRunConflict.implied_reason_entailed
#print axioms LeanFzn.Solver.UIP.LcgRunConflict.conflict_event_entailed
#print axioms LeanFzn.Solver.UIP.LcgRunConflict.terminal_conflict_entailed
#print axioms LeanFzn.Solver.UIP.LcgRunArms.lcgReachable_decideSkip
#print axioms LeanFzn.Solver.UIP.LcgRunArms.lcgPinFits_int
#print axioms LeanFzn.Solver.UIP.LcgRunArms.lcgResume_reachable
#print axioms LeanFzn.Solver.UIP.LcgRunJump.lcgRestorationState_reachable
#print axioms LeanFzn.Solver.UIP.LcgRunCert.lcg_certificate
#print axioms LeanFzn.Solver.UIP.LcgRunCert.lcg_normFalsified
#print axioms LeanFzn.Solver.UIP.LcgRunPending.lcgPendingSideInv_step
#print axioms LeanFzn.Solver.UIP.LcgRunState.lcgRunState_init
#print axioms LeanFzn.Solver.UIP.LcgRunStep.fresh_of_inhab
#print axioms LeanFzn.Solver.UIP.LcgRunStep.core_jump
#print axioms LeanFzn.Solver.UIP.LcgRunStep.lcgRunState_step
#print axioms LeanFzn.Solver.UIP.LcgRunStep.lcgRunState_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.frameRun_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.frameExplainedFull_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.trailSnapFixed_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.trailRun_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.runSemContract_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.lcgKit_gate_of_kit
#print axioms LeanFzn.Solver.UIP.LcgKitFinal.lcgRunInvCond_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunStep.lcgReach_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunStep.consumeRootRun_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunDrop.consume_falsifiers
#print axioms LeanFzn.Solver.UIP.LcgRunStep.jump_frameSnd
#print axioms LeanFzn.Solver.UIP.LcgRunStep.entailedRun_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunStep.hcertEnt_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunStep.cert_of_kit
#print axioms LeanFzn.Solver.UIP.LcgRunStep.assertingSem_of_kit
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.emissionTyped_of_families
#print axioms LeanFzn.Solver.UIP.LcgNoBool.impliedNB_of_families
#print axioms LeanFzn.Solver.UIP.LcgNoBoolTrail.deduction_literal_nb
#print axioms LeanFzn.Solver.UIP.LcgNoBoolTrail.nbTrail_closure
#print axioms LeanFzn.Solver.UIP.LcgNoBoolRun.nb_jump
#print axioms LeanFzn.Solver.UIP.LcgNoBoolRun.nbCfg_step
#print axioms LeanFzn.Solver.UIP.LcgNoBoolRun.nbCfg_of_kit
#print axioms LeanFzn.Solver.UIP.LcgDecideLive.live_of_wipeNone
#print axioms LeanFzn.Solver.UIP.LcgDecideLive.decide_wipe_none
#print axioms LeanFzn.Solver.UIP.LcgDecideLive.decideLive_of_kit
#print axioms LeanFzn.Solver.UIP.LcgDecideLive.lcgRunInvCond_of_kit_live
#print axioms LeanFzn.Solver.UIP.LcgDecideLive.not_decideLive_empty_domain
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_leConstHi
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_leConstLo
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_ltConstHi
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_ltConstLo
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_constEq
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_boolNot
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_boolAnd
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_boolOr
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_ne
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_allDiff
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_le
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_lt
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_eq
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_plus
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linLe
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linEq
#print axioms LeanFzn.Solver.UIP.LcgPropContract.propagationContract_of_families


#print axioms LeanFzn.Solver.UIP.LcgPhaseKernel.supportedPhaseProgressSorted
#print axioms LeanFzn.Solver.UIP.LcgPhaseKernel.reachablePhaseProgressSorted
#print axioms LeanFzn.Solver.UIP.LcgPhaseTerminal.phaseNext_sat_solution_of_kit
#print axioms LeanFzn.Solver.UIP.LcgPhaseTerminal.solve_sat_solution_of_kit
#print axioms LeanFzn.Solver.UIP.LcgCompiledKit.kit_of_compiled
#print axioms LeanFzn.Solver.UIP.LcgCompiledKit.slots_of_gate
#print axioms LeanFzn.Solver.UIP.LcgRunInv.syncOne_covers_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.covers_sem_shape

#print axioms LeanFzn.Solver.UIP.LcgLiveCoverage.of_kit
#print axioms LeanFzn.Solver.UIP.LcgPhaseTerminal.solve_unsat_excludes_of_kit

#print axioms LeanFzn.Integration.solveCompiledLcg_sat
#print axioms LeanFzn.Integration.solveCompiledLcg_unsat
#print axioms LeanFzn.Integration.solveCompiledLcg_total
-- A5: mixed route gate, mixed kit, mixed solve and its public theorems.
#print axioms LeanFzn.Integration.lcgRouteGateMixed
#print axioms LeanFzn.Integration.lcgInputMixed
#print axioms LeanFzn.Integration.lcgKitMixed
#print axioms LeanFzn.Integration.solveCompiledLcgMixed
#print axioms LeanFzn.Integration.solveCompiledLcgMixed_sat
#print axioms LeanFzn.Integration.solveCompiledLcgMixed_unsat
#print axioms LeanFzn.Integration.solveCompiledLcgMixed_total
#print axioms LeanFzn.Integration.lcgVerdict_sat
#print axioms LeanFzn.Integration.lcgVerdict_unsat
-- P3b: the linear-time route gate (fast twin of `mixedKitGateB`, equal by
-- `mixedKitGateFastB_eq`; the route gate `lcgRouteGateMixed` runs on it).
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.viewCode_injective
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.nodup_map_viewCode
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.viewsNodupFastB_iff
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB_eq
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_syncAll_shape

#print axioms LeanFzn.Solver.UIP.LcgPhaseObserved.solve_fst

#print axioms LeanFzn.Solver.Propagation.boolSlotImp_sound
#print axioms LeanFzn.Solver.Propagation.boolSlotImp_of_excludes

#print axioms LeanFzn.Solver.UIP.LcgRunInv.absent_remaining_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameExplainedFull_of_frameJ_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.emptyBool_absence_explained

#print axioms LeanFzn.Solver.UIP.LcgRunInv.canonical_boolPinsOn
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_resume_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_narrow_syncAll_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_closure_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_root_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.boolPinsOn_perform
#print axioms LeanFzn.Solver.UIP.LcgRunInv.boolPinsOn_append_bool

#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_split_bool_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameJ_perform_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.mixedFrameRun_init
#print axioms LeanFzn.Solver.UIP.LcgRunInv.MixedFrameRun.frameExplained

#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameRun_step_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.booleanPinRun_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgRunInv.mixedFrameRun_step

#print axioms LeanFzn.Solver.UIP.LcgRunInv.frameFalse_sem_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.dbUnit_sem_shape
#print axioms LeanFzn.Solver.UIP.LcgRunInv.raw_negative_boolean_unit_not_reason
#print axioms LeanFzn.Solver.UIP.LcgMixedEvents.lcgEvent_of_kit_at_shape

#print axioms LeanFzn.Solver.UIP.LcgCanonicalClauses.clampProps_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalClauses.recordedAnalysis_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.emissionCanonical_of_families
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.linEq_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.allDiff_canonical

#print axioms LeanFzn.Solver.UIP.LcgCanonicalRun.closure_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalRun.terminalResult_payload_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalRun.perform_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalScheduler.canonicalCfg_step
#print axioms LeanFzn.Solver.UIP.LcgCanonicalScheduler.canonicalCfg_of_families

#print axioms LeanFzn.Solver.UIP.LcgMixedDecisions.lcgPinFits_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedDecisions.lcgSkipTyped_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedGood.MixedLcgGood.stepNarrowSync
#print axioms LeanFzn.Solver.UIP.LcgMixedGood.MixedLcgGood.closure

#print axioms LeanFzn.Solver.UIP.LcgMixedConflict.terminal_conflict_entailed
#print axioms LeanFzn.Solver.UIP.LcgMixedCore.core_decide
#print axioms LeanFzn.Solver.UIP.LcgMixedCore.core_skip
#print axioms LeanFzn.Solver.UIP.LcgMixedCore.core_propagate_shape
-- A2c: mixed consume arm.
#print axioms LeanFzn.Solver.UIP.LcgMixedCore.core_consume_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunState.LcgMixedRunState.good
#print axioms LeanFzn.Solver.UIP.LcgMixedRunState.LcgMixedRunState.rootTrue
#print axioms LeanFzn.Solver.UIP.LcgMixedRunState.lcgMixedRunState_init

-- A2d: shape-typed frame-coverage and dead-site helpers.
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.propagate_covers_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.skip_covers_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.closure_frameSnd_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.terminal_conflict_dead_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.stableNone_dead_lcg_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedRunDrop.unsupportedHead_absent_of_lcgReach

-- A2b: shape-typed analyze/jump (perform) arm.
#print axioms LeanFzn.Solver.UIP.LcgMixedJump.cert_of_state_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedJump.jump_good0_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedJump.core_jump_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedJump.jump_frameSnd_shape

-- A3: mixed joint run step and mixed kit projections.
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.lcgMixedRunState_step
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.lcgMixedRunState_of_supportedRun
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.consumeRootRun_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.lcgMixedReach_of_kit
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.entailedRun_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.hcertEnt_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.cert_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedRunStep.assertingSem_of_kit_mixed

-- A4a: mixed compiled-kit producer (executable gate + five gate lemmas + kit).
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateB
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.shape_of_mixedGate
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.nodup_of_mixedGate
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.families_of_mixedGate
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.slots_of_mixedGate
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.kit_of_compiled_mixed

-- A4c: mixed live coverage and phase terminal transfer.
#print axioms LeanFzn.Solver.UIP.LcgMixedLiveCoverage.step_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedLiveCoverage.of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.phaseNext_sat_solution_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.solve_sat_solution_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.dead_exhausted_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.root_conflict_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.phaseNext_unsat_excludes_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedPhaseTerminal.solve_unsat_excludes_of_kit_mixed

-- A4b: mixed kit-level final results (part 1) and the shape closure chain (part 2).
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.frameRun_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.frameExplainedFull_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.trailSnapFixed_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.trailRun_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.runSemContract_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.lcgKit_gate_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.lcgRunInvCond_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.impliesP_slot
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.intForm_valueHolds_bool
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.valueHolds_of_impliesP_bool
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.literalImpossible_of_sem_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.dbSemUnfalsified_of_stableScan_shape
#print axioms LeanFzn.Solver.UIP.LcgMixedKitFinal.closure_at_decide_shape

-- C1 (2026-10-14): the `int_lin_ne` constructor, its extraction
-- inversion + soundness, and the registered identity propagator
-- (stage 1: certified chronological fallback, `lcgFamB .linNe = false`).
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_linNe
#print axioms LeanFzn.Compiler.holds_int_lin_ne
#print axioms LeanFzn.Solver.Propagation.propIdentity_run
#print axioms LeanFzn.Solver.Propagation.propIdentity_implied_elim
#print axioms LeanFzn.Solver.Propagation.propIdentity_conflict_elim

-- C2 (2026-10-14): the `bool_clause` constructor, its extraction
-- inversion + soundness, the seeded original-clause database (C2's
-- `boolClauseSlot` emission) with its canonical/aligned/entailed
-- facts, and the generalized compiled-kit producers plus the public
-- seed facts of `Integration.Lcg`.
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_boolClause
#print axioms LeanFzn.Compiler.holds_bool_clause
#print axioms LeanFzn.Compiler.bang_any_eqB_iff_slotIsBoolB
#print axioms LeanFzn.Compiler.seedClauses_mem_inv
#print axioms LeanFzn.Compiler.boolClauseSeed_entailed
#print axioms LeanFzn.Compiler.seedClauses_entailed
#print axioms LeanFzn.Compiler.seedClauses_satisfiedBy
#print axioms LeanFzn.Compiler.seedClauses_any_satisfiedB
#print axioms LeanFzn.Solver.UIP.LcgSeedClauses.seedClauses_canonical
#print axioms LeanFzn.Solver.UIP.LcgSeedClauses.seedClauses_aligned
#print axioms LeanFzn.Solver.UIP.LcgSeedClauses.seedClauses_aligned_of_slotOK
#print axioms LeanFzn.Solver.UIP.LcgCompiledKit.kit_of_compiled_nil
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.kit_of_compiled_mixed_nil
#print axioms LeanFzn.Integration.lcgSeedCanonical
#print axioms LeanFzn.Integration.lcgSeedAlignedInt
#print axioms LeanFzn.Integration.lcgSeedAlignedMixed
#print axioms LeanFzn.Integration.lcgSeedEntailed
#print axioms LeanFzn.Integration.compiled_clauseDatabase_seed
-- C2 helper lemmas (seed normal form, pin reads, clause bridging).
#print axioms LeanFzn.Compiler.getElem_bang_some
#print axioms LeanFzn.Compiler.mem_boolClauseSeed
#print axioms LeanFzn.Compiler.boolClauseSeed_norm
#print axioms LeanFzn.Compiler.seedClauses_norm
#print axioms LeanFzn.Compiler.slotIsBoolB_some
#print axioms LeanFzn.Compiler.clause_any_iff
#print axioms LeanFzn.Solver.UIP.LcgSeedClauses.mem_dcSlots_boolClauseSlot
#print axioms LeanFzn.Integration.compiled_clauseDatabase_empty

-- C3 (2026-10-14): the `array_bool_and` / `bool2int` / `bool_eq`
-- constructors (Boolean array/int families). Each registers NO
-- propagator (leaf-enforced, `.localFallback` route, no clause seed),
-- so the certification surface is the declarative/executable
-- semantics agreement, the extraction inversion + both soundness
-- directions, and the routing table entries.
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint.satisfiedB_iff
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_boolArr
#print axioms LeanFzn.Compiler.bang_all_eqB_iff_slotIsBoolB
#print axioms LeanFzn.Compiler.mapM_arr_ident
#print axioms LeanFzn.Compiler.holds_array_bool_and
#print axioms LeanFzn.Compiler.holds_bool2int
#print axioms LeanFzn.Compiler.holds_bool_eq
#print axioms LeanFzn.Compiler.extractConstraint_inv
#print axioms LeanFzn.Compiler.extractConstraint_holds
#print axioms LeanFzn.Compiler.eval_arr_ident
#print axioms LeanFzn.Compiler.extractConstraint_holds_converse
#print axioms LeanFzn.Solver.UIP.familyRoute_explained_or_fallback
#print axioms LeanFzn.Integration.compiled_linLe_shape
#print axioms LeanFzn.Integration.compiled_linEq_shape

-- C4 (2026-10-15): the `array_int_element` / `array_var_int_element` /
-- `array_var_bool_element` constructors (the FlatZinc element
-- families, 1-based `valuesGet1` reads). Each registers NO propagator
-- (leaf-enforced, `.localFallback` route, no clause seed), so the
-- certification surface is the extraction inversion + both soundness
-- directions and the arity-specific argument-evaluation bridges.
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_elem
#print axioms LeanFzn.Compiler.intLits_eval
#print axioms LeanFzn.Compiler.mapM_ident_arr_ident
#print axioms LeanFzn.Compiler.holds_array_int_element
#print axioms LeanFzn.Compiler.holds_array_var_int_element
#print axioms LeanFzn.Compiler.holds_array_var_bool_element
#print axioms LeanFzn.Compiler.eval_intLits_arg
#print axioms LeanFzn.Compiler.eval_ident_arr_lits
#print axioms LeanFzn.Compiler.eval_ident_arr_ident

-- B2 (2026-10-15): sound learned-clause reuse across objective bounds.
-- `LcgPhaseRunDb` is the DB-producing twin of the fuel-free supported
-- driver (terminal configuration + verdict agreement), `OptimizeSeed` is
-- the seeded branch-and-bound interface and driver, `LcgSeed` is the LCG
-- instance: leaf monotonicity of `addConstraint`/`improveBound` steps, the
-- seeded compiled problem and its kit, and the per-obligation soundness of
-- the seeded entry.
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_reach_congr
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_sat
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_unsat
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_propagate
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_decide
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_analyzeConflict
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_learnBackjumpAssert
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_localExclude
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_chronologicalFallback
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_fst
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.runSupportedPhaseDb_reach
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.solveDb_fst
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.solveCfg_reach
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.solveDb_spec_mixed
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.solveDb_sat_solution_of_kit_mixed
#print axioms LeanFzn.Solver.UIP.LcgPhaseRunDb.solveDb_unsat_excludes_of_kit_mixed
#print axioms LeanFzn.Integration.learnedEntailed_mono
#print axioms LeanFzn.Integration.SeedDb.nil_entailed
#print axioms LeanFzn.Integration.SeedDb.cast_clauses
#print axioms LeanFzn.Integration.SeedCertSolver.gate_curP
#print axioms LeanFzn.Integration.optLoopSeed_inv
#print axioms LeanFzn.Integration.optLoopSeed_complete
#print axioms LeanFzn.Integration.optimizeSeedCertified_inv
#print axioms LeanFzn.Integration.optimizeSeedCertified_solution_sound
#print axioms LeanFzn.Integration.optimizeSeedCertified_improving
#print axioms LeanFzn.Integration.optimizeSeedCertified_optimal
#print axioms LeanFzn.Integration.optimizeSeedCertified_unsat
#print axioms LeanFzn.Integration.optimizeSeedCertified_total
#print axioms LeanFzn.Integration.optimizeStreamSeedLoop_emit
#print axioms LeanFzn.Integration.verdictOfDriver_sat
#print axioms LeanFzn.Integration.verdictOfDriver_unsat
#print axioms LeanFzn.Integration.lcgLeaf_mono
#print axioms LeanFzn.Integration.lcgLeaf_addConstraint
#print axioms LeanFzn.Integration.learnedEntailed_addConstraint
#print axioms LeanFzn.Integration.improveBound_satisfiedB_mono
#print axioms LeanFzn.Integration.seedClauses_improveBound
#print axioms LeanFzn.Integration.seedClauses_add_improveBound
#print axioms LeanFzn.Integration.lcgLeaf_improveBound
#print axioms LeanFzn.Integration.learnedEntailed_improveBound
#print axioms LeanFzn.Integration.gateOk_lcgProblemSeed
#print axioms LeanFzn.Integration.domPruningOkB_lcgProblemSeed
#print axioms LeanFzn.Integration.mixedKitGateB_lcgProblemSeed
#print axioms LeanFzn.Integration.lcgKitSeed
#print axioms LeanFzn.Integration.lcgLeafSeed_entailed
#print axioms LeanFzn.Integration.lcgLeafSeed_of_lcgLeaf
#print axioms LeanFzn.Integration.lcgLeafSeed_of_accepts
#print axioms LeanFzn.Integration.lcgSeedRun_spec
#print axioms LeanFzn.Integration.lcgSolveDb_sat_sound
#print axioms LeanFzn.Integration.lcgSolveDb_unsat_complete
#print axioms LeanFzn.Integration.lcgSolveDb_db_entailed
#print axioms LeanFzn.Integration.lcgSolveDb_total

-- C5 (2026-10-15): the reified families (`int_eq_reif`,
-- `int_le_reif`, `int_ne_reif`, `int_lin_eq_reif`, `int_lin_le_reif`,
-- `int_lin_ne_reif`). Each registers NO propagator
-- (`propagatorOfProved = none`, leaf-enforced, `.localFallback` route,
-- `lcgFamB = false`), so the certification surface is the reification
-- bridge lemmas, the declarative/executable semantics agreement, the
-- extraction inversion + both soundness directions, and the
-- argument-evaluation bridge for the two-array-plus-int-plus-ident
-- argument shape.
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.reif_disj_iff
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.dotNe_eq
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_reif
#print axioms LeanFzn.Compiler.mapM_lin_reif
#print axioms LeanFzn.Compiler.holds_int_eq_reif
#print axioms LeanFzn.Compiler.holds_int_le_reif
#print axioms LeanFzn.Compiler.holds_int_ne_reif
#print axioms LeanFzn.Compiler.holds_int_lin_eq_reif
#print axioms LeanFzn.Compiler.holds_int_lin_le_reif
#print axioms LeanFzn.Compiler.holds_int_lin_ne_reif
#print axioms LeanFzn.Compiler.eval_lin_reif_args

-- C6 (2026-10-15): the general arithmetic and extreme families
-- (`int_div`/`int_mod` on general basic arguments — the StdLib
-- reading `b ≠ 0 ∧ c = Int.tdiv a b` / `Int.tmod a b`; the general
-- `int_min`/`int_max` with a literal operand; and the
-- `array_int_maximum`/`array_int_minimum` array forms with the
-- `maxValue`/`minValue` reading). Each registers NO propagator
-- (`propagatorOfProved = none`, leaf-enforced, `.localFallback`
-- route, `lcgFamB = false`), so the certification surface is the
-- operand-read bridge (`intArgOf`), the argument-evaluation bridges
-- for the three-basic and ident-array argument shapes, the `Holds`
-- inversion lemmas parameterized by the StdLib reading, the
-- extraction inversion + both soundness directions, and the
-- `DomIntArg` read lemmas.
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.DomIntArg.read_slot
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.DomIntArg.read_lit
#print axioms LeanFzn.Compiler.fullInterp_of_extracted_arith
#print axioms LeanFzn.Compiler.mapM_ident_arr
#print axioms LeanFzn.Compiler.mapM_three_basic
#print axioms LeanFzn.Compiler.intArgOf_read
#print axioms LeanFzn.Compiler.holds_int_arith_gen
#print axioms LeanFzn.Compiler.holds_array_int_extreme
#print axioms LeanFzn.Compiler.eval_basic_arg
#print axioms LeanFzn.Compiler.eval_three_basic
#print axioms LeanFzn.Compiler.eval_ident_slot_array

-- P1 (2026-10-15, resume + round 2): incremental propagator scheduling as an
-- executable refinement. The scheduled scan reuses a memorized result when
-- the watched-slot projection is unchanged; the dispatch equivalence
-- `phaseNextSched_fst_eq` (under `PropSchedulerOK` + the concrete
-- `PropLocal` discharge `clampProps_local`) lets the certified driver run on
-- the scheduled dispatcher (`runSched`) with an identical verdict
-- (`runSched_eq_runSupportedPhase`). ROUND 2 (one scan per step):
-- `schedulerNextSchedActive_fst_eq` is the active arm's equivalence at the
-- SINGLE evaluated event (both the transition and the table are read off one
-- `nextPruningEventSched`), and `lcgRunSched_eq_solve` / `lcgRun_eq_solve`
-- certify the scheduled route — now the PUBLIC route `lcgRun` — against the
-- baseline kernel alone (the `solveCompiledLcg*` statements are unchanged).
-- Measured: 1.32x FASTER than the baseline on the 43-instance battery with
-- 84% of propagator runs eliminated (Tests/E1/SchedCounts).
#print axioms LeanFzn.Solver.Propagation.PropSchedulerOK.init
#print axioms LeanFzn.Solver.Propagation.TableOK.of_props_eq
#print axioms LeanFzn.Solver.Propagation.PropLocal.of_props_eq
#print axioms LeanFzn.Solver.Propagation.scanPropagatorsSched_fst_eq
#print axioms LeanFzn.Solver.Propagation.scanPropagatorsSched_OK
#print axioms LeanFzn.Solver.Propagation.nextPruningEventSched_fst_eq
#print axioms LeanFzn.Solver.Propagation.clampProps_local
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_local
#print axioms LeanFzn.Solver.UIP.explainedDeductionSched_fst_eq
#print axioms LeanFzn.Solver.UIP.terminalResultSched_fst_eq
#print axioms LeanFzn.Solver.UIP.schedulerNextSchedActive_fst_eq
#print axioms LeanFzn.Solver.UIP.schedulerNextSched_fst_eq
#print axioms LeanFzn.Solver.UIP.schedulerNextSched_OK
#print axioms LeanFzn.Solver.UIP.phaseNextSched_fst_eq
#print axioms LeanFzn.Solver.UIP.phaseNextSched_OK
#print axioms LeanFzn.Solver.UIP.runSched_eq_runSupportedPhase
#print axioms LeanFzn.Solver.UIP.solve_sched_eq
#print axioms LeanFzn.Solver.UIP.solve_sched_sat
#print axioms LeanFzn.Solver.UIP.solve_sched_unsat
#print axioms LeanFzn.Integration.lcgRunSched_eq_solve
#print axioms LeanFzn.Integration.lcgRun_eq_solve
#print axioms LeanFzn.Integration.lcgRunSched_eq_lcgRun

-- L0a (2026-10-15): the generic checking propagator `propCheck`
-- (`LeanFzn.Solver.Propagation.Proofs.PropCheck`, `LeanFzn.Solver.UIP.Proofs.LcgPropCheck`).
-- `propCheck dc` watches nothing; once every slot `dc` reads
-- (`dcSlotsFull`, the total extension of `dcSlots` covering `DomIntArg`
-- operands) is pinned to a singleton frame domain, it evaluates
-- `dc.satisfiedB` on the forced assignment and reports a conflict
-- clause over the singleton facts on failure (`posNe`/`posBool`); it
-- never implies. No registration or gate change in this sub-box
-- (`propagatorOfProved`/`lcgFamB` untouched; L0b wires it in).
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.propCheck_implied_elim
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.satisfiedB_dcSlotsFull_congr
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.propCheck_conflict_entailed
#print axioms LeanFzn.Solver.UIP.LcgPropCheck.propCheck_sem
#print axioms LeanFzn.Solver.UIP.LcgPropCheck.propCheck_canonical
#print axioms LeanFzn.Solver.UIP.LcgPropCheck.propCheck_typed
#print axioms LeanFzn.Solver.UIP.LcgPropCheck.propCheck_noBool

-- L0b1 (2026-10-15): the registration of `propCheck` for the seventeen
-- `propCheckFamB` families (`propagatorOfProved` now returns
-- `some (propCheck dc)` for them) and the gate flip `lcgFamB = true`.
-- `propagatorOfProved_check_eq`/`_run_check` invert the new registration
-- arm; `dcSlots_eq_full` identifies the UIP slot list with the propagation
-- layer's `dcSlotsFull`; the repaired family theorems
-- (`propSem_of_family`, `emissionTyped_of_families`,
-- `emissionCanonical_of_families`, `impliedNB_of_families`) now dispatch
-- the seventeen families to the L0a obligations.
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_check_eq
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_run_check
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.dcSlots_eq_full

-- PLAN L1a (pinned `int_lin_le_reif` delegation): the decomposition layer.
-- The propagator is NOT registered yet (the registration + consumer
-- integration is parked as /home/vscode/wt/l1a/l1a_integration_wip.patch);
-- these are the proved ingredients.
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_safe
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_entitled
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinLe2_implied_clause_all
#print axioms LeanFzn.Solver.Propagation.propLinLe2_entitled_dot
#print axioms LeanFzn.Solver.Propagation.linLeReif_true_dot
#print axioms LeanFzn.Solver.Propagation.linLeReif_false_dot
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_implied_order
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinLeReif_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linLeReif
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.linLeReif_canonical

-- PLAN L3 (2026-10-16): `minSlot`/`maxSlot` re-registered to the proved
-- bound propagators `propMin`/`propMax` (previously `propCheck`).  The
-- A3 obligation triples (`propMin_safe`/`propMin_reason_valid`/
-- `propMin_entitled` and the `propMax` twins), the four UIP obligation
-- families (run gate, typed emission, canonicality, no-Bool) and all
-- consumer arms were reproved; `propagatorOfProved_run` gained the two
-- disjuncts `∃ i j k, dc = .minSlot i j k ∧ propMin st i j k = res` /
-- `∃ i j k, dc = .maxSlot i j k ∧ propMax st i j k = res`.
#print axioms LeanFzn.Solver.Propagation.propMin_safe
#print axioms LeanFzn.Solver.Propagation.propMax_safe
#print axioms LeanFzn.Solver.Propagation.propMin_reason_valid
#print axioms LeanFzn.Solver.Propagation.propMax_reason_valid
#print axioms LeanFzn.Solver.Propagation.propMin_entitled
#print axioms LeanFzn.Solver.Propagation.propMax_entitled
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propMin_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propMax_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_min
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_max
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.min_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.max_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_min
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_max

-- PLAN L3 (pair remainder): the all-slot `minPair`/`maxPair` shapes ride
-- `propMin`/`propMax`; `propagatorOfProved_run`'s min/max disjuncts now carry
-- the implication `∀ a, dc.SatisfiedBy a → (minSlot i j k).SatisfiedBy a`
-- instead of `dc = .minSlot i j k`; `propMin/propMax_{reason_valid,entitled}`
-- take `∀ a, ProblemSolution problem SatisfiedBy a → (minSlot ..).SatisfiedBy a`.
#print axioms LeanFzn.Solver.Propagation.slotBang_int
#print axioms LeanFzn.Solver.Propagation.minPair_imp_minSlot
#print axioms LeanFzn.Solver.Propagation.maxPair_imp_maxSlot
#print axioms LeanFzn.Compiler.sat_aux_reifRK
#print axioms LeanFzn.Compiler.sat_aux_reifKR
#print axioms LeanFzn.Compiler.sat_aux_ternRK
#print axioms LeanFzn.Compiler.sat_aux_ternKR
#print axioms LeanFzn.Compiler.fullInterp_int_min_iff
#print axioms LeanFzn.Compiler.fullInterp_int_max_iff
#print axioms LeanFzn.Compiler.compileConstraint_int_min_inv
#print axioms LeanFzn.Compiler.compileConstraint_int_max_inv
#print axioms LeanFzn.Compiler.auxShapeOf_minRK_inv
#print axioms LeanFzn.Compiler.auxShapeOf_minKR_inv
#print axioms LeanFzn.Compiler.auxShapeOf_maxRK_inv
#print axioms LeanFzn.Compiler.auxShapeOf_maxKR_inv
-- PLAN C9 remainder (2026-10-16): the LITERAL-RESULT min/max shapes
-- (`minRRK`/`maxRRK`: `int_min(x, y, k)` / `int_max(x, y, k)`) expanded to
-- `minSlot`/`maxSlot` over a pinned aux slot.
#print axioms LeanFzn.Compiler.sat_aux_ternRRK
#print axioms LeanFzn.Compiler.auxShapeOf_minRRK_inv
#print axioms LeanFzn.Compiler.auxShapeOf_maxRRK_inv
#print axioms LeanFzn.Compiler.mapM_ident_ident_const
#print axioms LeanFzn.Compiler.fullInterp_int_le_reif_iff
#print axioms LeanFzn.Compiler.compileConstraint_int_le_reif_inv

-- PLAN C9 remainder (2026-10-16): the TWO-ELEMENT ARRAY shapes
-- (`array_int_minimum(r, [e₁, e₂])` / `array_int_maximum(r, [e₁, e₂])`)
-- rewritten to `int_min(e₁, e₂, r)` / `int_max(e₁, e₂, r)` over the
-- model's own slots, plus the semantics-audit lemma (`array_int_minimum`
-- reads `minValue`, which IGNORES a non-integer TAIL, so the rewrite is
-- sound only under the WF int-typing guards).
#print axioms LeanFzn.Compiler.auxShapeOf_minGen2_inv
#print axioms LeanFzn.Compiler.auxShapeOf_maxGen2_inv
#print axioms LeanFzn.Compiler.mapM_ident_ident_arr
#print axioms LeanFzn.Compiler.minValue_int_int
#print axioms LeanFzn.Compiler.maxValue_int_int
#print axioms LeanFzn.Compiler.minValue_pair_int_tail
#print axioms LeanFzn.Compiler.maxValue_pair_int_tail
#print axioms LeanFzn.Compiler.array_int_minimum_rewrite_gap
#print axioms LeanFzn.Compiler.sigEnv_array_int_extreme
#print axioms LeanFzn.Compiler.holds_array_int_minimum_of_minSlot
#print axioms LeanFzn.Compiler.holds_array_int_maximum_of_maxSlot
#print axioms LeanFzn.Compiler.store_int_read_of_slot_checkArg
#print axioms LeanFzn.Compiler.checkBase_int_of_array_elem

-- PLAN L2 (2026-10-16): `linNe` registered to the explained single-value
-- removal propagator `propLinNe` (previously `propCheck`).
#print axioms LeanFzn.Solver.Propagation.propLinNe_safe
#print axioms LeanFzn.Solver.Propagation.propLinNe_entitled
#print axioms LeanFzn.Solver.Propagation.propLinNe_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinNe_implied_decided
#print axioms LeanFzn.Solver.Propagation.propLinNe_implied_inv
#print axioms LeanFzn.Solver.Propagation.propLinNe_conflict_inv
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinNe_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linNe
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.linNe_canonical

-- PLAN L4 (2026-10-16): `leReifSlot` registered to the pinned-direction
-- delegation `propLeReifSlot` (previously `propCheck`).
#print axioms LeanFzn.Solver.Propagation.propLeReifSlot_safe
#print axioms LeanFzn.Solver.Propagation.propLeReifSlot_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLeReifSlot_entitled
#print axioms LeanFzn.Solver.Propagation.propLeReifSlot_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLeReifSlot_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_leReifSlot
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.leReifSlot_canonical

-- PLAN L4 (continued, 2026-10-16): `eqReifSlot`/`neReifSlot` registered to
-- the pinned-direction delegations `propEqReifSlot`/`propNeReifSlot`.
-- (`propEqReifSlot_cases`/`propNeReifSlot_cases` are the case splits used by
-- the noBool dispatch inside `LcgNoBoolEmit.impliedNB_of_families`; that
-- module has no per-family noBool theorem to profile.)
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_safe
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_reason_valid
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_entitled
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propEqReifSlot_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_eqReifSlot
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.eqReifSlot_canonical
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_safe
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_reason_valid
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_entitled
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propNeReifSlot_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_neReifSlot
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.neReifSlot_canonical

-- PLAN L1b (stage 1.5): the machinery's auxiliary lemmas
#print axioms LeanFzn.Solver.Propagation.posBool_eval_bool
#print axioms LeanFzn.Solver.Propagation.linLeReifEscB_true_of_bool_read
#print axioms LeanFzn.Solver.UIP.LcgFamilies.linLeReifEscB_sf
#print axioms LeanFzn.Solver.UIP.LcgNoBool.not_intState_of_domBoolOnly

-- PLAN L1b (stage 2, 2026-10-16): the bounds-decide-`b` arm is WIRED
-- (`propLinLeReif_run_b`) with the operand-range/arity gate threaded from
-- `domPruningOkB` (`domPruningOk_lreif`) through `boxPropagators_reasons`
-- and `propagatorsOfProved_reasonSafeUniv`.
#print axioms LeanFzn.Solver.Propagation.domPruningOk_lreif
#print axioms LeanFzn.Solver.Propagation.mul_le_maxContrib_of_cause_false
#print axioms LeanFzn.Solver.Propagation.dotOver_le_sumMax_of_causes_false
#print axioms LeanFzn.Solver.Propagation.propLinLeReifB_implied_true
#print axioms LeanFzn.Solver.Propagation.propLinLeReifB_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_run_b
-- (`propLinLeReif_reason_valid`'s existing L1a profile above now covers the
-- B-arm-widened statement; only its hypotheses changed.)
-- (`propLinLeReif_sem` / `typed_linLeReif` / `linLeReif_canonical` keep
-- their existing L1a profiles above; their statements are unchanged by L1b.)

-- PLAN L5 (2026-10-16): `linEqReif`/`linNeReif` registered to the
-- pinned-direction delegations `propLinEqReif`/`propLinNeReif`
-- (previously `propCheck`).  `propCheckFamB` lost the two `true` arms
-- (now `false` for both families) and `propagatorOfProved_run` gained
-- the two disjuncts `∃ coeffs is b r, dc = .linEqReif coeffs is b r ∧
-- propLinEqReif st coeffs is b r = res` / `... .linNeReif ...`.
-- Pinned-true arms delegate to `propLinEq2`/`propLinNe` under the
-- escape `posBool r false`; pinned-false arms (under `domsIntOnlyB`)
-- delegate to the complemented kernel as CONFLICTS ONLY.
#print axioms LeanFzn.Solver.Propagation.linReifNarrowHi_bounds_of_implied
#print axioms LeanFzn.Solver.Propagation.linReifNarrowLo_bounds_of_implied
#print axioms LeanFzn.Solver.Propagation.linReif_getD_ne_nil_of_domMinI
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_run_true
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_run_false
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_run_stable
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_run_arity
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_run_true
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_run_false
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_run_stable
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_run_arity
#print axioms LeanFzn.Solver.Propagation.linEqReif_satisfied_inv
#print axioms LeanFzn.Solver.Propagation.linNeReif_satisfied_inv
#print axioms LeanFzn.Solver.Propagation.linEqReif_true_dot
#print axioms LeanFzn.Solver.Propagation.linNeReif_true_dot
#print axioms LeanFzn.Solver.Propagation.dotProduct_exists_of_reads
#print axioms LeanFzn.Solver.Propagation.linEqReif_false_dot
#print axioms LeanFzn.Solver.Propagation.linNeReif_false_dot
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_safe
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_safe
#print axioms LeanFzn.Solver.Propagation.propLinEq2_entitled_dot
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_entitled
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_entitled
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_implied_order
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_implied_order
#print axioms LeanFzn.Solver.Propagation.slotInt_exists_of_state_ne_nil
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_implied_decided
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_implied_decided
#print axioms LeanFzn.Solver.Propagation.linEqReif_split_true
#print axioms LeanFzn.Solver.Propagation.linNeReif_split_true

-- PLAN L8 (2026-10-17): the strengthened `all_different` — fixed-slot
-- VALUE ELIMINATIONS (`xᵢ = c ⇒ xⱼ ≠ c`).  `propAllDiffLCG` now emits
-- `.implied (posNe j c)` with the `propNe`-shaped reason
-- `allDiffElimClause i j c`; the new `domPruningOkB` operand-range
-- conjunct (extracted by `domPruningOk_lad`) is threaded through
-- `boxPropagators_reasons` (profile above; statement widened by the new
-- `hlad` hypothesis only), `propagatorsOfProved_reasonSafeUniv` (above),
-- `propagatorsOfProved_just` (above) and the `fallbackCoverage_*`
-- producers; `propAllDiffLCG_sem` (above) gained the frame's
-- `AbsentExpl` premise (conclusion unchanged).
#print axioms LeanFzn.Solver.Propagation.domPruningOk_lad
#print axioms LeanFzn.Solver.Propagation.allDiffElimB_eq
#print axioms LeanFzn.Solver.Propagation.allDiffElimTarget_spec
#print axioms LeanFzn.Solver.Propagation.allDiffElimFirst_spec
#print axioms LeanFzn.Solver.Propagation.allDiffElimClause_slot
#print axioms LeanFzn.Solver.Propagation.allDiffElimClause_norm
#print axioms LeanFzn.Solver.Propagation.allDiff_read_ne
#print axioms LeanFzn.Solver.Propagation.intSingleton_read
#print axioms LeanFzn.Solver.Propagation.allDiff_elim_true_of_fits
#print axioms LeanFzn.Solver.Propagation.allDiff_nogood_true
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_implied_inv
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_reason_valid
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_safe
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_reason_valid
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinEqReif_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLinNeReif_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linEqReif
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_linNeReif
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.linEqReif_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.linNeReif_canonical

-- PLAN L7 (2026-10-16): `absSlot` re-registered to the proved bound
-- propagator `propAbs` (previously `propCheck`).  The A3 obligation
-- triple (`propAbs_safe`/`propAbs_reason_valid`/`propAbs_entitled`, in
-- `Fam/Arith.lean`), the new decidedness helper for the sweep's
-- opposing-pair arm, the four UIP obligation families (run gate, typed
-- emission, canonicality, no-Bool) and all consumer arms were reproved;
-- `propagatorOfProved_run` gained the disjunct
-- `∃ i k, dc = .absSlot i k ∧ propAbs st i k = res` and
-- `propCheckFamB (.absSlot i k)` is now `false`.
#print axioms LeanFzn.Solver.Propagation.propAbs_safe
#print axioms LeanFzn.Solver.Propagation.propAbs_reason_valid
#print axioms LeanFzn.Solver.Propagation.propAbs_entitled
#print axioms LeanFzn.Solver.Propagation.absSlot_views
#print axioms LeanFzn.Solver.Propagation.propAbs_implied_decided_views
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propAbs_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_abs
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.abs_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_abs

-- PLAN L7 (2026-10-17): the general `int_div`/`int_mod` shapes
-- re-registered to the proved bound propagators `propDiv`/`propMod`
-- (previously `propCheck`).  The A3 obligation triples
-- (`propDiv_safe`/`propDiv_reason_valid`/`propDiv_entitled` and the
-- `propMod` mirror, in `Fam/Arith.lean`), the truncation arithmetic
-- (`tdiv_mem_hull`, `tmod_bounds`, `tmod_mem_hull`), the pinned-divisor
-- inversion (`divPin_slot_dom` — the exact integer-singleton domain the
-- zero-divisor conflict consumes through the frame invariant's
-- `FixExpl`), the decidedness helpers for the sweep's opposing-pair
-- arm, the four UIP obligation families (run gate, typed emission,
-- canonicality, no-Bool) and all consumer arms were reproved;
-- `propagatorOfProved_run` gained the disjuncts
-- `∃ o₁ o₂ r, dc = .divGen o₁ o₂ r ∧ propDiv st o₁ o₂ r = res` and the
-- `.modGen` mirror, and `propCheckFamB (.divGen ..)`/`(.modGen ..)` are
-- now `false`.
#print axioms LeanFzn.Solver.Propagation.divPin_slot_dom
#print axioms LeanFzn.Solver.Propagation.divPin_slot
#print axioms LeanFzn.Solver.Propagation.tdiv_mem_hull
#print axioms LeanFzn.Solver.Propagation.tmod_bounds
#print axioms LeanFzn.Solver.Propagation.tmod_mem_hull
#print axioms LeanFzn.Solver.Propagation.propDiv_safe
#print axioms LeanFzn.Solver.Propagation.propMod_safe
#print axioms LeanFzn.Solver.Propagation.propDiv_reason_valid
#print axioms LeanFzn.Solver.Propagation.propMod_reason_valid
#print axioms LeanFzn.Solver.Propagation.propDiv_entitled
#print axioms LeanFzn.Solver.Propagation.propMod_entitled
#print axioms LeanFzn.Solver.Propagation.propDiv_implied_decided
#print axioms LeanFzn.Solver.Propagation.propMod_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propDiv_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propMod_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_div
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_mod
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.div_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.mod_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_div
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_mod

-- PLAN L6: `int_times` (`timesSlot`) re-registers the proved bound
-- propagator `propTimes` (previously `propCheck`).  The A3 obligation
-- triple (`propTimes_safe`/`propTimes_reason_valid`/`propTimes_entitled`;
-- the latter two are listed above), the emission-slot inversion and the
-- four UIP obligation families (sem/typed/canonical/noBool); the new
-- `propagatorOfProved_run` disjunct is
-- `∃ i j k, dc = .timesSlot i j k ∧ propTimes st i j k = res`.
#print axioms LeanFzn.Solver.Propagation.propTimes_safe
#print axioms LeanFzn.Solver.Propagation.propTimes_implied_slot
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propTimes_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_times
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.times_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_times

-- PLAN C9-remainder: the n-ary `array_int_minimum`/`array_int_maximum`
-- (the `minGen`/`maxGen` families, the extractor's leaf shape for
-- n >= 3) re-register the attained-operand result propagators
-- `propMinGen`/`propMaxGen` (previously `propCheck`).  Each propagator
-- emits only the two bounds justified by the `minValue`/`maxValue`
-- attainment (`result >= min of the operands' state lower bounds`,
-- `result <= max of the operands' state upper bounds`); the strong
-- corner arm `result <= min of the state upper bounds` is NOT sound
-- without an int-typing gate on the operand slots (the non-integer
-- tail `minValue` ignores) and is dropped, with the kernel-checked
-- counterexample lemma `minGen_hi_corner_gap` documenting the gap.
-- The new `propagatorOfProved_run` disjuncts are
-- `∃ os r, dc = .maxGen os r ∧ propMaxGen st os r = res` /
-- `∃ os r, dc = .minGen os r ∧ propMinGen st os r = res`; the
-- `propCheckFamB` arms for the two families are removed.
#print axioms LeanFzn.Solver.Propagation.minValue_mem
#print axioms LeanFzn.Solver.Propagation.maxValue_mem
#print axioms LeanFzn.Solver.Propagation.minGen_attained
#print axioms LeanFzn.Solver.Propagation.maxGen_attained
#print axioms LeanFzn.Solver.Propagation.read_slot_int
#print axioms LeanFzn.Solver.Propagation.read_lit_int
#print axioms LeanFzn.Solver.Propagation.minArgLo_spec
#print axioms LeanFzn.Solver.Propagation.maxArgHi_spec
#print axioms LeanFzn.Solver.Propagation.argLoCause_mem
#print axioms LeanFzn.Solver.Propagation.argHiCause_mem
#print axioms LeanFzn.Solver.Propagation.argLoCause_slot_none
#print axioms LeanFzn.Solver.Propagation.argLoCause_slot_some
#print axioms LeanFzn.Solver.Propagation.argHiCause_slot_none
#print axioms LeanFzn.Solver.Propagation.argHiCause_slot_some
#print axioms LeanFzn.Solver.Propagation.argLoCause_canonical
#print axioms LeanFzn.Solver.Propagation.argHiCause_canonical
#print axioms LeanFzn.Solver.Propagation.clauseCanonical_flatMap
#print axioms LeanFzn.Solver.Propagation.genValue_bounds
#print axioms LeanFzn.Solver.Propagation.propGen_lo_nogood_true
#print axioms LeanFzn.Solver.Propagation.propGen_hi_nogood_true
#print axioms LeanFzn.Solver.Propagation.propMinGen_safe
#print axioms LeanFzn.Solver.Propagation.propMaxGen_safe
#print axioms LeanFzn.Solver.Propagation.propMinGen_reason_valid
#print axioms LeanFzn.Solver.Propagation.propMaxGen_reason_valid
#print axioms LeanFzn.Solver.Propagation.propMinGen_entitled
#print axioms LeanFzn.Solver.Propagation.propMaxGen_entitled
#print axioms LeanFzn.Solver.Propagation.minGen_hi_corner_gap
#print axioms LeanFzn.Solver.UIP.LcgFamilies.argLoCause_sf
#print axioms LeanFzn.Solver.UIP.LcgFamilies.argHiCause_sf
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propMinGen_sem
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propMaxGen_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.argLoCause_slotOK
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.argHiCause_slotOK
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.clauseSlotOK_cons
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_minGen
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_maxGen
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.minGen_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.maxGen_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_minGen
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_maxGen

-- PLAN P1b: the optimised learned-database scan (`DbScanIndex.lean`) — the
-- unconditional equality against the certified `scanDatabase` plus its
-- supporting classification lemmas.  The scheduled dispatch consumes
-- `scanDatabaseFast_eq` at `nextPruningEventSched_fst_eq`, so every
-- scheduled-route theorem below inherits these profiles.
#print axioms LeanFzn.Solver.Propagation.literalImpossibleArr_eq
#print axioms LeanFzn.Solver.Propagation.clauseClassify_some
#print axioms LeanFzn.Solver.Propagation.clauseClassify_none
#print axioms LeanFzn.Solver.Propagation.scanDatabaseFastAux_eq
#print axioms LeanFzn.Solver.Propagation.scanDatabaseFast_eq

-- PLAN P2: the activity-ordered decision order (`Integration/LcgHeur.lean`).
-- The presentation works by per-domain value-list permutations, so the
-- transfer of every route predicate is a `List.Perm` argument; the profiles
-- below cover the permutation core, the gate/box transfers and the
-- activity-ordered entry's SAT/UNSAT/totality statements.
#print axioms LeanFzn.Integration.LcgHeur.sortDom_perm
#print axioms LeanFzn.Integration.LcgHeur.reorderAux_getElem?
#print axioms LeanFzn.Integration.LcgHeur.gateOk_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.domPruningOkB_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.mixedKitGateB_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.fitsB_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.Fits_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.SlotOK_reorderAux
#print axioms LeanFzn.Integration.LcgHeur.heurLeaf_eq
#print axioms LeanFzn.Integration.LcgHeur.heurKit
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeur_eq_solve
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeur_sat
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeur_unsat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeur_sat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeur_unsat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeur_verdict
