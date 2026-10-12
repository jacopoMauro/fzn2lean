/-
File: audits/certified_axioms.lean

Purpose:
  CI axiom-profile audit: the public certified theorems must depend
  only on the three standard Lean axioms.

Usage (from the repo root):
  lake env lean audits/certified_axioms.lean
-/

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
import LeanFzn.Solver.UIP.Proofs.ExtendedPoolRank
import LeanFzn.Solver.UIP.Proofs.SupportedInstance
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
#print axioms LeanFzn.Solver.Propagation.analyzeStep_eq_analyzeLoop
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_mono
#print axioms LeanFzn.Solver.Propagation.analyzeLoop_mono_le
#print axioms LeanFzn.Solver.Propagation.analyzeStep_mono_le
#print axioms LeanFzn.Solver.Propagation.pivotCost_filter_lt
#print axioms LeanFzn.Solver.Propagation.historicalAllowance_le_analysisFuel
#print axioms LeanFzn.Solver.Propagation.analyzeAtAllowance_dominates
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
#print axioms LeanFzn.Solver.Propagation.transitionBudget_le_analysisFuel
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_snd
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_mono
#print axioms LeanFzn.Solver.Propagation.analyzeTrace_exists_of_decrease
#print axioms LeanFzn.Solver.Propagation.roundCost_scan
#print axioms LeanFzn.Solver.Propagation.roundCost_pivot
#print axioms LeanFzn.Solver.Propagation.initCost_arith
#print axioms LeanFzn.Solver.Propagation.roundCost_init_add_one_le_analysisFuel
#print axioms LeanFzn.Solver.Propagation.analysis_not_fuel_limited
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
#print axioms LeanFzn.Solver.UIP.databaseAligned_terminalResult_localExcluded
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
