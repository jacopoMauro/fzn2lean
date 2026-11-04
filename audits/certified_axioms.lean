import LeanFzn.Integration.Public
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Legacy.Solver.Propagation.Proofs.Fam.AllDiff
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedConflict
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedCompiledKit
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedCore
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedDecisions
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedGood
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedJump
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedKitFinal
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedLiveCoverage
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedPhaseTerminal
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunDrop
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseSchedDb
/-
File: audits/certified_axioms.lean

Purpose:
  CI axiom-profile audit: the public certified theorems must depend
  only on the three standard Lean axioms.

Usage (from the repo root):
  lake env lean audits/certified_axioms.lean
-/

import LeanFzn.Legacy.Solver.Propagation.ClosureFast
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch
import LeanFzn.Legacy.Solver.Propagation.VersionWatch
import LeanFzn.Legacy.Solver.Propagation.WorkQueue
import LeanFzn.Legacy.Solver.Propagation.EventContract
import LeanFzn.Legacy.Solver.Propagation.ClauseLifecycle
import LeanFzn.Solver.Propagation.CompactDomain
import LeanFzn.Legacy.Solver.Propagation.DecisionProto
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalScheduler
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalFamilies
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedEvents
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedFrameRun
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgBooleanPins
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantAbsentShape
import LeanFzn.Solver.Propagation.BoolImplication
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseObserved
import LeanFzn.Legacy.Integration.Lcg
import LeanFzn.Legacy.Integration.LcgOptimize
import LeanFzn.Legacy.Integration.LcgSeed
import LeanFzn.Legacy.Integration.LcgSeedConfig
import LeanFzn.Legacy.Integration.LcgSeedBudget
import LeanFzn.Legacy.Integration.OptimizeBudget
import LeanFzn.Legacy.Integration.OptimizeBisect
import LeanFzn.Legacy.Solver.UIP.Proofs.BudgetRun
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrameShape
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgLiveCoverage
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseKernel
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseTerminal
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCompiledKit
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantShape
import LeanFzn.Legacy.Solver.UIP.Proofs.ConsumeInvariant
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedLog
import LeanFzn.Legacy.Integration.CertifiedSolve
import LeanFzn.Legacy.Integration.CoreSolve
import LeanFzn.Legacy.Integration.Certified
import LeanFzn.Solver.Propagation.Proofs.Run
import LeanFzn.Solver.Propagation.Proofs.Fam.Element
import LeanFzn.Legacy.Solver.Propagation.Proofs.FallbackRaw
import LeanFzn.Legacy.Integration.Proofs.FallbackMulti
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.Propagation.ConflictResolution
import LeanFzn.Legacy.Solver.Propagation.AnalysisProgress
import LeanFzn.Legacy.Solver.Propagation.AnalysisInvariants
import LeanFzn.Legacy.Solver.Propagation.RestorationCertificate
import LeanFzn.Legacy.Solver.Propagation.AnalysisCompletion
import LeanFzn.Legacy.Solver.Propagation.EventScan
import LeanFzn.Legacy.Solver.UIP.Proofs.ConflictResolution
import LeanFzn.Legacy.Solver.UIP.Proofs.BackjumpFrontier
import LeanFzn.Legacy.Solver.Chronological.Proofs.AnalysisDriver
import LeanFzn.Legacy.Solver.UIP.Proofs.CanonicalTrailVocabulary
-- V1 (2026-10-10): new first-UIP chain (R1..P5, W1), X2 driver, D1 entry.
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerCoverage
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerFalsified
import LeanFzn.Legacy.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRank
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerJumpProgress
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerPhaseProgress
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachClosure
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerArmsPreserve
import LeanFzn.Legacy.Solver.UIP.Proofs.DatabaseUnfalsified
import LeanFzn.Legacy.Solver.UIP.Scheduler
import LeanFzn.Legacy.Solver.Chronological.Proofs.Search
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerCertifiedRun
-- Session 11: N1/P1/R2a/J1/E1/C1 landings live in the newer proof modules.
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.ClosureRefutation
import LeanFzn.Legacy.Solver.UIP.Proofs.PendingRun
import LeanFzn.Legacy.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Legacy.Solver.UIP.Proofs.EmissionVocabulary
import LeanFzn.Legacy.Solver.UIP.Proofs.TrailVocabularyProducers
import LeanFzn.Legacy.Integration.Proofs.CompiledShape
import LeanFzn.Legacy.Integration.Proofs.CompiledEntry
import LeanFzn.Legacy.Integration.Proofs.FallbackPolicy
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedProviders
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedDead
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedArms
-- Session 13: the J1/E1/L1/R2/C1/I1 round modules.
import LeanFzn.Legacy.Solver.UIP.Proofs.CheckpointPrefix
import LeanFzn.Legacy.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedLogSites
import LeanFzn.Legacy.Solver.UIP.Proofs.ConsumeRun
import LeanFzn.Legacy.Solver.UIP.Proofs.AnalysisEntail
import LeanFzn.Legacy.Solver.UIP.Proofs.SiteInhabited
import LeanFzn.Legacy.Solver.UIP.Proofs.SiteLiveness
import LeanFzn.Legacy.Solver.UIP.Proofs.FreshCoverless
import LeanFzn.Legacy.Solver.UIP.Proofs.ExtendedPoolProducers
import LeanFzn.Legacy.Solver.UIP.Proofs.ClampPool
import LeanFzn.Legacy.Solver.UIP.Proofs.ClampedRun
import LeanFzn.Legacy.Solver.UIP.Proofs.ExtendedPoolRank
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedInstance
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgClampTransfer
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantSnap
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrameFalse
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantSync
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrame
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantGate
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantReasons
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantTrailStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFinal
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantEvidenceFalse
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEvidence
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEntailed
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgAsserting
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgHbrRefuted
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgReachable
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEvents
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunGood
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunArms
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunJump
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunCert
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPropContract
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunPending
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunState
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedCompiledKit
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgKitFinal
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEmissionTyped
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPropCheck
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgDecideLive
import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Compiler.Proofs.CompileAux2c
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Compiler.Proofs.Objective
import LeanFzn.Checker.Objective
import LeanFzn.Legacy.Integration.Optimize
import LeanFzn.Legacy.Integration.CoreOptimize
import LeanFzn.Legacy.Integration.CoreSeed
import LeanFzn.Legacy.Integration.Primal
import LeanFzn.Engine.Clauses
import LeanFzn.Engine.Prop
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Ne
import LeanFzn.Engine.Props.Linear
import LeanFzn.Engine.Props.Arith
import LeanFzn.Engine.Queue
import LeanFzn.Engine.Analyze
import LeanFzn.Engine.Reduce
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

#print axioms LeanFzn.Solver.Propagation.Frame.domains_subsets
#print axioms LeanFzn.Solver.Propagation.TrailAgreesFrame_filterFrame
#print axioms LeanFzn.Solver.Core.mem_allAssigns_of_getElem?
#print axioms LeanFzn.Solver.Propagation.frame_covers_of_trail
#print axioms LeanFzn.Solver.Propagation.allAssigns_cons_of_mem
#print axioms LeanFzn.Solver.Propagation.reachable_init
#print axioms LeanFzn.Solver.Propagation.reachable_decide

/-! ### A2 resident explained step -/

#print axioms LeanFzn.Solver.Propagation.norm_valueHolds
#print axioms LeanFzn.Solver.Propagation.filterFrame_literal_holds
#print axioms LeanFzn.Solver.Propagation.FrameCovers_of_subsets
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
-- PLAN §3.0 item 2: the constant-set membership domain restriction.
#print axioms LeanFzn.Compiler.setInAccepts_eq
#print axioms LeanFzn.Compiler.setInShape_inv
#print axioms LeanFzn.Compiler.setInCondOf_some_inv
#print axioms LeanFzn.Compiler.holds_of_cond
#print axioms LeanFzn.Compiler.cond_of_holds
#print axioms LeanFzn.Compiler.restrictVarType_range_int
#print axioms LeanFzn.Compiler.restrictVarType_set_int
#print axioms LeanFzn.Compiler.restrictVarType_contains_imp
#print axioms LeanFzn.Compiler.restrictVarDecl_name
#print axioms LeanFzn.Compiler.restrictVarDecl_type
#print axioms LeanFzn.Compiler.staticEnv_restrict
#print axioms LeanFzn.Compiler.restrictSetIn_covers
#print axioms LeanFzn.Compiler.restrictSetIn_exact
#print axioms LeanFzn.Compiler.wf_restrict
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

-- F4 (2026-10-29): the configured seeded driver `--opt=seeded` with the
-- F2/F3 policy surface. `PresentationPerm` transfers the value presentation
-- (a pointwise domain permutation) to the literal pool, the aligned database
-- and the assignment set; `LcgSeedConfig` adds the priority vector, the
-- activity toggle, the static value presentations and the source-level
-- pure/streaming runners with their claim theorems.
#print axioms LeanFzn.Integration.SeedDb.withPrev_clauses
#print axioms LeanFzn.Integration.DomListPerm.refl
#print axioms LeanFzn.Integration.DomListPerm.trans
#print axioms LeanFzn.Integration.DomListPerm.symm
#print axioms LeanFzn.Integration.vocabDomInts_perm
#print axioms LeanFzn.Integration.threshPool_perm
#print axioms LeanFzn.Integration.slotAtomPool_perm
#print axioms LeanFzn.Integration.atomPoolBase_domListPerm
#print axioms LeanFzn.Integration.atomPool_domListPerm
#print axioms LeanFzn.Integration.litPool_domListPerm
#print axioms LeanFzn.Integration.databaseAligned_domListPerm
#print axioms LeanFzn.Integration.mem_allAssigns_domListPerm
#print axioms LeanFzn.Integration.reorderAuxWith_domListPerm
#print axioms LeanFzn.Integration.reorderAux_domListPerm
#print axioms LeanFzn.Integration.heurDomains_domListPerm
#print axioms LeanFzn.Integration.annotDomains_domListPerm
#print axioms LeanFzn.Integration.lcgConfigProblem_domains
#print axioms LeanFzn.Integration.lcgConfigProblem_constraints
#print axioms LeanFzn.Integration.lcgConfigProblem_toStore
#print axioms LeanFzn.Integration.accepts_lcgConfigProblem
#print axioms LeanFzn.Integration.accepts_curP_lcgConfigProblem
#print axioms LeanFzn.Integration.mem_allAssigns_lcgConfigProblem
#print axioms LeanFzn.Integration.gateOk_lcgConfigProblem
#print axioms LeanFzn.Integration.lcgRouteGateMixed_lcgConfigProblem
#print axioms LeanFzn.Integration.lcgSeedSolverConfig_gate
#print axioms LeanFzn.Integration.optimizeSeedConfig_inv
#print axioms LeanFzn.Integration.optimizeSeedConfig_solution_sound
#print axioms LeanFzn.Integration.optimizeSeedConfig_improving
#print axioms LeanFzn.Integration.optimizeSeedConfig_optimal
#print axioms LeanFzn.Integration.optimizeSeedConfig_unsat
#print axioms LeanFzn.Integration.optimizeSeedConfig_total
#print axioms LeanFzn.Integration.optimizeStreamSeedConfig_eq

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
-- 84% of propagator runs eliminated (retired SchedCounts diagnostic).
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

-- PLAN G1 (2026-10-18): `leReifSlot` re-registered to the strengthened
-- `propLeReifSlotB` (pinned delegations byte-identical, unpinned bounds arm
-- `propLeReifB`; the arm's base package is profiled in the Waves 6-7 block
-- below).  The consumer obligations here are the registered surface.
#print axioms LeanFzn.Solver.Propagation.propLeReifB_emission_inv
#print axioms LeanFzn.Solver.Propagation.propLeReifB_ne_conflict
#print axioms LeanFzn.Solver.Propagation.propLeReifB_causes_false_fits
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_safe
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_entitled
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propLeReifSlotB_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_leReifSlotB
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.leReifSlotB_canonical

-- PLAN G1-B (2026-10-18): `bool2intSlot` registered to the explained
-- channeling propagator `propBool2intSlot` (`Fam/Bool.lean`): pinned
-- opposite-digit removals, raw `[.int 0]`/`[.int 1]` target pins through
-- `implyBool`, the unpinned unit removals and the two bound conflicts.
-- The consumer obligations here are the registered surface.
#print axioms LeanFzn.Solver.Propagation.firstBadView_some
#print axioms LeanFzn.Solver.Propagation.b2iBadRes_cases
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_cases
#print axioms LeanFzn.Solver.Propagation.b2iResPinned_entailed
#print axioms LeanFzn.Solver.Propagation.b2iNoBool_excluded
#print axioms LeanFzn.Solver.Propagation.b2i_neg_excluded
#print axioms LeanFzn.Solver.Propagation.b2i_pos_excluded
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_safe
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_reason_valid
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_entitled
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propBool2intSlot_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_bool2int
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.bool2intSlot_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_bool2int

-- PLAN G1c (2026-10-18): `arrayIntElementSlot` registered to the explained
-- constant-table element propagator `propArrayIntElement` (`Fam/Element.lean`):
-- pinned-index target narrowing and out-of-range conflict, pinned-target
-- unsupported-index removal, the unpinned out-of-range unit removal and the
-- no-support removal on an integer-only target. The consumer obligations
-- here are the registered surface.
#print axioms LeanFzn.Solver.Propagation.aie_firstBadView_eq_some
#print axioms LeanFzn.Solver.Propagation.aie_firstBadView_isSome_some
#print axioms LeanFzn.Solver.Propagation.aieEntryEqB_false
#print axioms LeanFzn.Solver.Propagation.aie_firstBadView_entryEqB_some
#print axioms LeanFzn.Solver.Propagation.aie_firstBadView_supportB_some
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_cases
#print axioms LeanFzn.Solver.Propagation.aieResOut_entailed
#print axioms LeanFzn.Solver.Propagation.aieResPinIdx_entailed
#print axioms LeanFzn.Solver.Propagation.aieResPinVal_entailed
#print axioms LeanFzn.Solver.Propagation.aieResNoSupp_entailed
#print axioms LeanFzn.Solver.Propagation.aie_pinBad_excluded
#print axioms LeanFzn.Solver.Propagation.aie_posNe_k_pinIdx_true
#print axioms LeanFzn.Solver.Propagation.aie_posNe_i_pinVal_true
#print axioms LeanFzn.Solver.Propagation.aie_posNe_i_out_true
#print axioms LeanFzn.Solver.Propagation.aie_posNe_i_noSupp_true
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_safe
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_reason_valid
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_entitled
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.aie_negNe_falsified
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propArrayIntElement_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_arrayIntElement
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.arrayIntElementSlot_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_arrayIntElement

-- PLAN P6c (2026-10-26): the hoisted `array_int_element` scans. `valuesGet1A`
-- is O(1) `Array` table access (`valuesGet1A_toArray`), `aieLookup` selects
-- the hoisted view (`aieLookup_none`/`aieLookup_array`), and
-- `aieSupportCached`/`aieEntrySomeCached` carry the table and compact-target
-- options. The gate lemmas show the index-width-gated runtime scan equals the
-- legacy `aieSupportV`/`valuesGet1` scans for every index, so the runtime
-- rewrite changes no propagator decision. `Dom.memBool_ofList` is the
-- compact-membership bridge used by the target hoist.
#print axioms LeanFzn.Solver.Propagation.Dom.memBool_ofList
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_ofList
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_ofList_fun
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_ofList_map
#print axioms LeanFzn.Solver.Propagation.aieSupportV_map_fun
#print axioms LeanFzn.Solver.Propagation.valuesGet1A_toArray
#print axioms LeanFzn.Solver.Propagation.aieLookup_none
#print axioms LeanFzn.Solver.Propagation.aieLookup_array
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_plain
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_hoisted
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_plain_map
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_hoisted_map
#print axioms LeanFzn.Solver.Propagation.aieEntrySomeCached_plain
#print axioms LeanFzn.Solver.Propagation.aieEntrySomeCached_array
#print axioms LeanFzn.Solver.Propagation.aieEntrySomeCached_plain_map
#print axioms LeanFzn.Solver.Propagation.aieEntrySomeCached_array_map
#print axioms LeanFzn.Solver.Propagation.aieEntrySomeCached_gate
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_gate

-- PLAN section 3.3 item 1 (2026-10-24): `arrayVarIntElementSlot` registered
-- to the explained variable-table element propagator `propArrayVarIntElement`
-- (`Fam/VarElement.lean`): pinned-index target/entry narrowing and the
-- out-of-range conflict, pinned-target unsupported-index removal, and the
-- unpinned out-of-range/singleton/hull-separation and no-support rounds.
#print axioms LeanFzn.Solver.Propagation.avieEntry_mem
#print axioms LeanFzn.Solver.Propagation.avie_valuesGet1_of_entry
#print axioms LeanFzn.Solver.Propagation.avie_entry_of_valuesGet1
#print axioms LeanFzn.Solver.Propagation.arrayVarIntElement_views
#print axioms LeanFzn.Solver.Propagation.avie_entry_reads
#print axioms LeanFzn.Solver.Propagation.avieTableMemB_false
-- S2a: the array-view table scan used by the compiled element twin.
#print axioms LeanFzn.Solver.Propagation.avieTableMemArrB_toArray_eq
#print axioms LeanFzn.Solver.Propagation.avieTableMemArrB_eq
#print axioms LeanFzn.Solver.Propagation.firstBadView_congr
#print axioms LeanFzn.Solver.Propagation.avie_guard_of_res
#print axioms LeanFzn.Solver.Propagation.avieResOut_entailed
#print axioms LeanFzn.Solver.Propagation.avieResK_entailed
#print axioms LeanFzn.Solver.Propagation.avieResJ_entailed
#print axioms LeanFzn.Solver.Propagation.avieResPinVal_entailed
#print axioms LeanFzn.Solver.Propagation.avieResSingle_entailed
#print axioms LeanFzn.Solver.Propagation.avieResBelow_entailed
#print axioms LeanFzn.Solver.Propagation.avieResAbove_entailed
#print axioms LeanFzn.Solver.Propagation.avieResNoSupp_entailed
#print axioms LeanFzn.Solver.Propagation.avieResPinBad_excluded
#print axioms LeanFzn.Solver.Propagation.avie_pinK_head
#print axioms LeanFzn.Solver.Propagation.avie_pinJ_head
#print axioms LeanFzn.Solver.Propagation.avie_out_true
#print axioms LeanFzn.Solver.Propagation.avie_pinVal_head
#print axioms LeanFzn.Solver.Propagation.avie_single_head
#print axioms LeanFzn.Solver.Propagation.avie_below_head
#print axioms LeanFzn.Solver.Propagation.avie_above_head
#print axioms LeanFzn.Solver.Propagation.avie_noSupp_head
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_cases
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_safe
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_reason_valid
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_entitled
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_implied_decided
#print axioms LeanFzn.Solver.Propagation.avie_slotInt_of_state_int
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propArrayVarIntElement_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_arrayVarIntElement
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.arrayVarIntElementSlot_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_arrayVarIntElement

-- PLAN section 3.3 item 2 (2026-10-24): `arrayVarBoolElementSlot` registered
-- to the explained variable-table Boolean element propagator
-- `propArrayVarBoolElement` (`Fam/BoolElement.lean`): pinned-index Boolean
-- target/entry narrowing and the out-of-range conflict, pinned-target
-- unsupported-index removal, the unpinned out-of-range/singleton and
-- no-support rounds, and the empty-support conflicts.
#print axioms LeanFzn.Solver.Propagation.avbeFirstBad_some
#print axioms LeanFzn.Solver.Propagation.avbeFirstBad_none
#print axioms LeanFzn.Solver.Propagation.arrayVarBoolElement_views
#print axioms LeanFzn.Solver.Propagation.avbe_entry_reads
#print axioms LeanFzn.Solver.Propagation.avbePinTargetRes_of_bad
#print axioms LeanFzn.Solver.Propagation.avbeSingleRes_of_bad
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_cases
#print axioms LeanFzn.Solver.Propagation.avbe_guard_of_res
#print axioms LeanFzn.Solver.Propagation.avbeResOut_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResPinVal_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResSingle_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResTarget_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResEntry_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResNoSupp_entailed
#print axioms LeanFzn.Solver.Propagation.avbeResPinBad_excluded
#print axioms LeanFzn.Solver.Propagation.avbe_out_true
#print axioms LeanFzn.Solver.Propagation.avbe_pinVal_head
#print axioms LeanFzn.Solver.Propagation.avbe_single_head
#print axioms LeanFzn.Solver.Propagation.avbeTableMemB_false
#print axioms LeanFzn.Solver.Propagation.avbe_target_head
#print axioms LeanFzn.Solver.Propagation.avbe_entry_head
#print axioms LeanFzn.Solver.Propagation.avbe_noSupp_head
#print axioms LeanFzn.Solver.Propagation.avbeResTarget_safe
#print axioms LeanFzn.Solver.Propagation.avbeResEntry_safe
#print axioms LeanFzn.Solver.Propagation.avbeResNoSupp_safe
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_safe
#print axioms LeanFzn.Solver.Propagation.avbe_slotBool_of_state_bool
#print axioms LeanFzn.Solver.Propagation.avbe_reason_valid_of_clause
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_reason_valid
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_entitled
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_implied_decided
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propArrayVarBoolElement_sem
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_arrayVarBoolElement
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.avbe_map_posBool_canonical
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.arrayVarBoolElementSlot_canonical
#print axioms LeanFzn.Solver.UIP.LcgNoBool.domBoolOnlyB_false_of_intState
#print axioms LeanFzn.Solver.UIP.LcgNoBool.avbeGuardB_false_of_intState
#print axioms LeanFzn.Solver.UIP.LcgNoBool.propArrayVarBoolElement_stable_of_intState
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_arrayVarBoolElement

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

-- PLAN G1d (2026-10-18): the `linLeReif` r = false direction is wired: the
-- dual `sumMin > b ⇒ r = false` pin (`propLinLeReifBDual`, tried by
-- `propLinLeReifB` after the max-arm) and the retained pinned-`false`
-- delegated bound implications (the `conflictsOnly` wrapper removed from
-- `propLinLeReif`). The extended emission split and the new running
-- equations are the registered surface; the family-level
-- safe/entitled/reason_valid/implied_* and UIP consumer profiles above
-- re-verify the widened statements.
#print axioms LeanFzn.Solver.Propagation.propLinLeReifBDual_emission_inv
#print axioms LeanFzn.Solver.Propagation.propLinLeReifB_emission_inv
#print axioms LeanFzn.Solver.Propagation.propLinLeReifB_ne_conflict
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_run_false
#print axioms LeanFzn.Solver.Propagation.propLinLe2_implied_order

-- PLAN G1e (2026-10-18): `arrayBoolAndSlot` registered to the explained
-- array-Boolean conjunction propagator `propArrayBoolAnd` (`Fam/Bool.lean`):
-- the all-inputs-pinned-true target pin, the pinned-false input round, the
-- pinned-true target's input pruning, and the Boolean-only singleton round.
-- The consumer obligations here are the registered surface (including the
-- new `BoolDomsAt` problem gate's `domPruningOk_aba` projection).
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_cases
#print axioms LeanFzn.Solver.Propagation.aba_satisfied
#print axioms LeanFzn.Solver.Propagation.aba_allTrue_pivot
#print axioms LeanFzn.Solver.Propagation.aba_pinFalse_pivot
#print axioms LeanFzn.Solver.Propagation.aba_kTrue_pivot
#print axioms LeanFzn.Solver.Propagation.aba_single_pivot
#print axioms LeanFzn.Solver.Propagation.aba_allTrue_excluded
#print axioms LeanFzn.Solver.Propagation.aba_pinFalse_excluded
#print axioms LeanFzn.Solver.Propagation.aba_kTrue_excluded
#print axioms LeanFzn.Solver.Propagation.aba_single_excluded
#print axioms LeanFzn.Solver.Propagation.aba_allTrue_entailed
#print axioms LeanFzn.Solver.Propagation.aba_pair_entailed
#print axioms LeanFzn.Solver.Propagation.aba_pairTrue_entailed
#print axioms LeanFzn.Solver.Propagation.aba_single_entailed
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_safe
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_reason_valid
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_entitled
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_implied_decided
#print axioms LeanFzn.Solver.Propagation.domPruningOk_aba
#print axioms LeanFzn.Solver.UIP.LcgFamilies.propArrayBoolAnd_sem
#print axioms LeanFzn.Solver.UIP.LcgCanonicalFamilies.arrayBoolAndSlot_canonical
#print axioms LeanFzn.Solver.UIP.LcgEmissionTyped.typed_arrayBoolAnd
#print axioms LeanFzn.Solver.UIP.LcgNoBool.nb_arrayBoolAnd

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

-- PLAN O1: the objective-biased decision order (§6-§9 of
-- `Integration/LcgHeur.lean`).  The bias is a second per-domain value-list
-- permutation (`sortDomBias`), transferred through the presentation-generic
-- `reorderAuxWith` core; the profiles below cover the bias sort, the biased
-- transfers and the biased entry's SAT/UNSAT/totality statements.
#print axioms LeanFzn.Integration.LcgHeur.sortDomBias_perm
#print axioms LeanFzn.Integration.LcgHeur.reorderAuxBias_getElem?
#print axioms LeanFzn.Integration.LcgHeur.reorderAuxWith_getD
#print axioms LeanFzn.Integration.LcgHeur.gateOk_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.domPruningOkB_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.mixedKitGateB_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.fitsB_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.Fits_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.SlotOK_reorderAuxBias
#print axioms LeanFzn.Integration.LcgHeur.heurKitBias
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeurBias_eq_solve
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeurBias_sat
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeurBias_unsat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurBias_sat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurBias_unsat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurBias_verdict

-- PLAN F2: annotation-guided search (`Integration/Annot.lean`).  The
-- `seq_search` priority vector is free (the scheduled route holds for every
-- `prio`); the per-slot `indomain_*` presentation is a domain permutation
-- transferred through the same `reorderAuxWith` core as the activity and
-- bias presentations.  Profiles below cover the extraction-facing sort
-- facts, the transfers, the annotated entry and the configuration dispatch.
#print axioms LeanFzn.Integration.sortDomAnnot_perm
#print axioms LeanFzn.Integration.annotDomains_length
#print axioms LeanFzn.Integration.annotDomains_getElem?
#print axioms LeanFzn.Integration.getD_annotDomains
#print axioms LeanFzn.Integration.fitsB_annot
#print axioms LeanFzn.Integration.Fits_annot
#print axioms LeanFzn.Integration.SlotOK_annot
#print axioms LeanFzn.Integration.gateOk_annot
#print axioms LeanFzn.Integration.domPruningOkB_annot
#print axioms LeanFzn.Integration.mixedKitGateB_annot
#print axioms LeanFzn.Integration.annotLeaf_eq
#print axioms LeanFzn.Integration.annotKit
#print axioms LeanFzn.Integration.annotFrameGate
#print axioms LeanFzn.Integration.lcgRunAnnot_eq_solve
#print axioms LeanFzn.Integration.lcgRunAnnot_sat
#print axioms LeanFzn.Integration.lcgRunAnnot_unsat
#print axioms LeanFzn.Integration.lcgRunAnnot_verdict
#print axioms LeanFzn.Integration.solveCompiledAnnot_sat
#print axioms LeanFzn.Integration.solveCompiledAnnot_unsat
#print axioms LeanFzn.Integration.solveCompiledAnnot_verdict
#print axioms LeanFzn.Integration.solveSearchConfig_default
#print axioms LeanFzn.Integration.solveSearchConfig_sat
#print axioms LeanFzn.Integration.solveSearchConfig_unsat
#print axioms LeanFzn.Integration.solveSearchConfig_verdict

-- PLAN F3: general value orders (`--val=min|max|median`) and solution-guided
-- phase saving (`--val=incumbent`).  The static orders reuse the F2
-- per-slot permutation transfer; the phase rank is taken in the
-- activity-ordered enumeration and rotated by `atRank`.  The B&B recursion
-- threads the previous incumbent without changing the termination measure,
-- and the phase-aware dispatch has the same SAT/UNSAT/totality statements.
#print axioms LeanFzn.Integration.sortDomAnnot_nil
#print axioms LeanFzn.Integration.phaseRank?
#print axioms LeanFzn.Integration.phaseOrders
#print axioms LeanFzn.Integration.configOrders
#print axioms LeanFzn.Integration.solveSearchConfigWith_sat
#print axioms LeanFzn.Integration.solveSearchConfigWith_unsat
#print axioms LeanFzn.Integration.solveSearchConfigWith_verdict
#print axioms LeanFzn.Integration.optLoopWith_inv
#print axioms LeanFzn.Integration.optLoopWith_complete
#print axioms LeanFzn.Integration.optLoopEmitWith_eq
#print axioms LeanFzn.Integration.optimizeStreamLoopWith_emit
#print axioms LeanFzn.Integration.lcgVerdictWith_sat
#print axioms LeanFzn.Integration.lcgVerdictWith_unsat
#print axioms LeanFzn.Integration.lcgVerdictWith_fail_free
#print axioms LeanFzn.Integration.lcgSolver

-- Wave 2 (2026-10-17 evening): per-scan literal summaries, the fast closure
-- and its dispatcher wiring, and the watched-clause index core.  The runtime
-- transitions keep their statements and are transported through these
-- equalities: `scanDatabaseFast_eq` -> `nextPruningEventFast_eq` ->
-- `explainedDeductionFast_eq` -> `explainedClosureFast_eq` ->
-- `BackjumpPlan.performFast_eq` -> `backjumpStepFast_eq`.
#print axioms LeanFzn.Solver.Propagation.literalImpossibleFast_eq
#print axioms LeanFzn.Solver.Propagation.clauseClassifyFast_some
#print axioms LeanFzn.Solver.Propagation.clauseClassifyFast_none
#print axioms LeanFzn.Solver.Propagation.productiveFast_eq
#print axioms LeanFzn.Solver.Propagation.nextPruningEventFast_eq
#print axioms LeanFzn.Solver.Propagation.explainedDeductionFast_eq
#print axioms LeanFzn.Solver.Propagation.explainedClosureFast_eq
#print axioms LeanFzn.Solver.Propagation.BackjumpPlan.performFast_eq
#print axioms LeanFzn.Solver.UIP.backjumpStepFast_eq
-- W0/W1 core: the watched database scan is exactly the certified scan; the
-- index is not wired into the runtime yet.
#print axioms LeanFzn.Solver.Propagation.scanDatabaseWatch_fst_eq
#print axioms LeanFzn.Solver.Propagation.scanDatabaseWatch_fst_eq_fast
#print axioms LeanFzn.Solver.Propagation.establish_WatchOK

-- Waves 3-4 (2026-10-17 late evening): the certified work queue (E1), the
-- clause-lifecycle vocabulary (L0), the E0 event contract and the compact
-- domain stage 1 (D2).  The runtime dispatcher consumes the queued prompt
-- through `nextPruningEventQueuedSched_fst_eq` / `scanQueue_event_eq`.
#print axioms LeanFzn.Solver.Propagation.scanQueue_event_eq
#print axioms LeanFzn.Solver.Propagation.scanQueueAux_spec
#print axioms LeanFzn.Solver.UIP.nextPruningEventQueuedSched_fst_eq
#print axioms LeanFzn.Solver.Propagation.QueueOK_drain
#print axioms LeanFzn.Solver.Propagation.empty_complete
#print axioms LeanFzn.Solver.Propagation.frameEvents_complete
#print axioms LeanFzn.Solver.Propagation.clampProps_skipsStable
#print axioms LeanFzn.Solver.Propagation.skipsComplete_proof
#print axioms LeanFzn.Solver.Propagation.ClauseLifecycle.Lifecycle.wellFormed_active_entailed
#print axioms LeanFzn.Solver.Propagation.ClauseLifecycle.Lifecycle.wellFormed_delete
#print axioms LeanFzn.Solver.Propagation.Dom.enum_ofList
#print axioms LeanFzn.Solver.Propagation.Dom.ofList_enum_eq_of_WF
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filter
#print axioms LeanFzn.Solver.Propagation.Dom.memBool_iff
#print axioms LeanFzn.Solver.Propagation.DecisionProto.selectSlot_min
#print axioms LeanFzn.Solver.Propagation.DecisionProto.covers_pin_or_retire
#print axioms LeanFzn.Solver.Propagation.DecisionProto.frontierWeight_split_lt
#print axioms LeanFzn.Solver.Propagation.scanDatabaseWatch2_fst_eq
-- PLAN §3.4: per-slot version discipline and the version-keyed watched scan
-- (the W1 variant; measured but NOT wired, see the module header).
#print axioms LeanFzn.Solver.Propagation.bumpEvents_size
#print axioms LeanFzn.Solver.Propagation.domain_eq_of_version_eq
#print axioms LeanFzn.Solver.Propagation.VersionWatch.sync_size
#print axioms LeanFzn.Solver.Propagation.VWatchOK.bump
#print axioms LeanFzn.Solver.Propagation.VWatchOK.prepend
#print axioms LeanFzn.Solver.Propagation.two_le_clauseRemaining_of_vEntry
#print axioms LeanFzn.Solver.Propagation.scanWatchVAux_spec
#print axioms LeanFzn.Solver.Propagation.scanDatabaseWatchV_fst_eq
#print axioms LeanFzn.Solver.Propagation.scanDatabaseWatchVPrepend_fst_eq

-- Waves 6-7 (2026-10-18): the strengthened leReifSlot unpinned arm (G1) and
-- the bool_xor compiler coverage (C0).
#print axioms LeanFzn.Solver.Propagation.propLeReifB_implied_true
#print axioms LeanFzn.Solver.Propagation.propLeReifB_reason_valid
#print axioms LeanFzn.Solver.Propagation.propLeReifB_cases
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_eq_of_pinned
#print axioms LeanFzn.Solver.Propagation.propLeReifB_implied_decided
#print axioms LeanFzn.Compiler.sat_aux_xor

-- §3.0.1 (2026-10-22): exact-equivalence jump-cost work. The runtime caches
-- (`poolHash`, `learnedNorm`) are primed by `SchedulerConfig.init`, preserved
-- by every real transition (`SupportedReach.cacheAligned`), and the fast
-- novelty guard / single counted analysis are proved equal to the reference
-- `learnedRepeats` / `recordedAnalysis` / `analyzeEventsExpansions` values.
#print axioms LeanFzn.Solver.UIP.hashSetOfList_mem
#print axioms LeanFzn.Solver.UIP.litPoolHash_contains
#print axioms LeanFzn.Solver.UIP.litMask_eq_of_mem_iff
#print axioms LeanFzn.Solver.UIP.clauseKeyWith_eq_of_mem_iff
#print axioms LeanFzn.Solver.UIP.insertClauseKeys_contains_of_contains
#print axioms LeanFzn.Solver.UIP.insertClauseKeys_contains_clause
#print axioms LeanFzn.Solver.UIP.SchedulerConfig.init_poolHashAligned
#print axioms LeanFzn.Solver.UIP.SchedulerConfig.init_learnedNormAligned
#print axioms LeanFzn.Solver.UIP.SchedulerConfig.init_learnedKeysSound
#print axioms LeanFzn.Solver.UIP.SchedulerConfig.init_cacheAligned
#print axioms LeanFzn.Solver.UIP.learnedRepeatsWith_true_exists
#print axioms LeanFzn.Solver.UIP.learnedRepeatsFast_eq
#print axioms LeanFzn.Solver.UIP.countedAnalysisFast_fst
#print axioms LeanFzn.Solver.UIP.countedAnalysisFast_snd
#print axioms LeanFzn.Solver.UIP.stepAnalyzeConflictOf_eq
#print axioms LeanFzn.Solver.UIP.stepAnalyzeConflictCountedOf_eq
#print axioms LeanFzn.Solver.UIP.conflictStepFast_eq
#print axioms LeanFzn.Solver.UIP.SupportedReach.cacheAligned
-- §3.0 item 5: search-policy input (S2/O1 toggles)
#print axioms LeanFzn.Solver.Propagation.SelectPolicy.selectSlotP_nil
#print axioms LeanFzn.Solver.Propagation.SelectPolicy.selectSlotP_live
#print axioms LeanFzn.Solver.Propagation.SelectPolicy.selectSlotP_complete
#print axioms LeanFzn.Solver.Propagation.SelectPolicy.selectSlotP_none_iff
#print axioms LeanFzn.Solver.Propagation.SelectPolicy.bumpPrio_length
#print axioms LeanFzn.Solver.Propagation.SparseRun.Frame.splitP_nil
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurOpts_default
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurOpts_sat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurOpts_unsat
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurOpts_verdict

-- §3.0 P1 (2026-10-24): declared watch footprints for the two dominant
-- families (`linEq` -> its constraint slots, `arrayIntElementSlot` -> index
-- and target) and the locality proofs that make the scheduled scan's reuse
-- exact (`PropLocalOne`). `propLinEq2_propLocal` was already proved but is
-- now consumed by the wired registration; the element proofs are new
-- (`propArrayIntElement_local` reduces the run to the two watched `getD`
-- reads, including the `domsIntOnlyB` singleton guard). Measurements and the
-- go/no-go record are in PLAN.md §3.0 P1.
#print axioms LeanFzn.Solver.Propagation.propLinEq2_propLocal
#print axioms LeanFzn.Solver.Propagation.lt_length_of_getD_ne_nil
#print axioms LeanFzn.Solver.Propagation.domsIntOnlyB_singleton_congr
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_local
#print axioms LeanFzn.Solver.Propagation.propArrayIntElement_propLocal

-- §3.0 P2 (2026-10-24): VERSION-KEYED scheduled propagation. The scheduler
-- carries per-slot counters (`SchedVersions`) aligned with the frame; a sync
-- bumps exactly the slots whose `Frame.domains` entry changed
-- (`frameChanged_complete`), and `domains_eq_of_version_eq` certifies that an
-- unchanged counter means an unchanged watched domain. Entries are
-- transported across a sync (`EntryOK.sync`, `TableOK.sync`), so the public
-- scan equivalence and the table invariant keep their P1 statements while
-- the hot-path skip test becomes O(1) per watched slot (`stampNatEqB` on
-- `watchVersions`). Measurements and the acceptance record are in PLAN.md
-- §3.0 P2.
#print axioms LeanFzn.Solver.Propagation.sVersionBump_size
#print axioms LeanFzn.Solver.Propagation.sVersionBumpAll_size
#print axioms LeanFzn.Solver.Propagation.sVersionBump_getD_self
#print axioms LeanFzn.Solver.Propagation.sVersionBumpAll_getD_ge
#print axioms LeanFzn.Solver.Propagation.sVersionBumpAll_getD_gt_of_mem
#print axioms LeanFzn.Solver.Propagation.frameChangedAux_complete
#print axioms LeanFzn.Solver.Propagation.frameChanged_complete
#print axioms LeanFzn.Solver.Propagation.domains_eq_of_version_eq
#print axioms LeanFzn.Solver.Propagation.stampNatEqB_sound
#print axioms LeanFzn.Solver.Propagation.stampLe.antisymm
#print axioms LeanFzn.Solver.Propagation.watchVersions_le_of_pointwise
#print axioms LeanFzn.Solver.Propagation.watchVersions_getD_of_eq
#print axioms LeanFzn.Solver.Propagation.EntryOK.of_local_run
#print axioms LeanFzn.Solver.Propagation.EntryOK.sync
#print axioms LeanFzn.Solver.Propagation.TableOK.sync
#print axioms LeanFzn.Solver.Propagation.PropScheduler.sync_versions_size
#print axioms LeanFzn.Solver.Propagation.scanPropagatorsSchedAux_spec

-- §3.0 P2b (2026-10-24): PROPAGATOR DEDUCTIONS ARE NOT GLOBALLY LEARNED.
-- `scanPropagators`/`prefixScanPropagators`/`scanPropagatorsSchedAux` (and the
-- E1 queued scan) emit `.implied ... false false`: the reason clause stays on
-- the trail as the deduction's explanation but does not enter the global
-- learned database. The scan-equality theorems keep their statements, so the
-- scheduled route emits the same non-learning event as the reference scan
-- (`scanPropagatorsSched_fst_eq`, already audited). Measurements and the
-- search-policy record (first nonogram decision shifts 9929 -> 9926) are in
-- PLAN.md §3.0 P2b.
#print axioms LeanFzn.Solver.Propagation.scanPropagators_implied_learn_false
#print axioms LeanFzn.Solver.Propagation.prefixScanPropagators_implied_learn_false
#print axioms LeanFzn.Solver.Propagation.scanPropagators_implied_facts

-- §3.0 P2c (2026-10-25): SLOT-FILTERED EXPLANATION SYNC. `syncClause` no
-- longer scans the whole trail: `trailOnSlot` keeps only the entries of the
-- pushed literal's slot, which suffices because `impliesP_slot_eq` shows that
-- an implying trail entry must live on the target slot. `syncExplain` runs on
-- that filtered trail (`syncExplain_trailOnSlot`), and the guard is unchanged
-- semantically (`trailOnSlot_any_impliesP`). `syncRemover` additionally avoids
-- materialising `trail.reverse.map negate` (`syncRemover_trailOnSlot` records
-- that the slot filter commutes with the remover search). Measurements and the
-- acceptance record are in PLAN.md §3.0 P2c.
#print axioms LeanFzn.Solver.Propagation.impliesLit_slot_eq
#print axioms LeanFzn.Solver.Propagation.impliesBase_slot_eq
#print axioms LeanFzn.Solver.Propagation.impliesP_slot_eq
#print axioms LeanFzn.Solver.Propagation.syncRemover_trailOnSlot
#print axioms LeanFzn.Solver.Propagation.syncExplain_trailOnSlot
#print axioms LeanFzn.Solver.Propagation.trailOnSlot_any_impliesP

-- §3.0 P3 (2026-10-25): DECLARED FOOTPRINTS FOR THE REMAINING LINEAR
-- FAMILIES. `propagatorOfProved` now gives `linLe` and `linNe` the footprint
-- `is.map (fun i => Atom.intLe i 0)` (the slots their runs read), so the
-- declared-watch default consumes `propLinLe2_propLocal`/`propLinNe_propLocal`
-- through `propagatorOfProved_local` and `clampProps_local`. The refined
-- per-footprint instances remain available for a queue that subscribes on the
-- audited footprint. Measurements and the acceptance record are in PLAN.md
-- §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.propLinLe2_propLocal
#print axioms LeanFzn.Solver.Propagation.propLinNe_propLocal
#print axioms LeanFzn.Solver.Propagation.propLinLe2_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propLinNe_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_linLe_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_linNe_clamp_skipSoundOn
-- The runtime `queuePolicy` gained a measured unit-count cutoff (large
-- all-linear FBD instances stay on the stamp path). The switch is a pure
-- performance knob; both branches are the certified event.
#print axioms LeanFzn.Solver.UIP.promptOf_fst_eq
#print axioms LeanFzn.Solver.UIP.promptOf_OK

-- §3.0 P3 batch 2 (2026-10-25): DECLARED FOOTPRINTS FOR THE REIFIED BINARY
-- FAMILIES AND `bool2int`. `propagatorOfProved` now gives `eqReifSlot`,
-- `leReifSlot` and `neReifSlot` the footprint `[i, j, r]` (the reif pin and
-- both operands), `linEqReif` and `linNeReif` the footprint `r :: is` (the
-- reif pin and the constraint slots), and `bool2intSlot` the footprint
-- `[i, k]` (source and target). The new locality proofs reduce each run to
-- those watched `getD` reads, including `leReifSlot`'s unpinned bounds arm
-- (`propLeReifB_local`, via `domsIntOnlyB_local`) and the linear
-- delegations' `domsIntOnlyB` guard; `propagatorOfProved_local` consumes
-- them through `clampProps_local`. `linLeReif` stays footprint-less because
-- its dual arm is not proved. The refined and registered
-- `..._clamp_skipSoundOn` instances expose the audited footprints for the
-- queue. Measurements and the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.list_all_congr_mem
#print axioms LeanFzn.Solver.Propagation.domsIntOnlyB_local
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_local
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_local
#print axioms LeanFzn.Solver.Propagation.propLeReifB_local
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_local
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_local
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_local
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_local
#print axioms LeanFzn.Solver.Propagation.watchStamp_getD_reif
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_propLocal
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_propLocal
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_propLocal
#print axioms LeanFzn.Solver.Propagation.watchStamp_getD_reif_lin
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_propLocal
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_propLocal
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_propLocal
#print axioms LeanFzn.Solver.Propagation.propEqReifSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propLeReifSlotB_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propNeReifSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propLinEqReif_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propLinNeReif_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propBool2intSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_eqReifSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_leReifSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_neReifSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_linEqReif_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_linNeReif_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_bool2intSlot_clamp_skipSoundOn

-- §3.0 P3 batch 3 (2026-10-25): DECLARED FOOTPRINT FOR `linLeReif`.
-- `propagatorOfProved` now gives `linLeReif coeffs is b r` the footprint
-- `r :: is` (the reif pin plus the constraint slots), matching the audited
-- reads of all three arms: pinned `true` delegation, pinned `false`
-- delegation, and the unpinned dual bounds arm. The new locality proof
-- reduces the unpinned arm's sum/cause reads to the constraint slots
-- (`propLinLeReifBDual_local`, `propLinLeReifB_local`, `propLinLeReif_local`)
-- and `propagatorOfProved_local` consumes it through `clampProps_local`.
-- The refined and registered `..._clamp_skipSoundOn` instances expose the
-- audited footprint for the queue. Measurements and the acceptance record
-- are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.propLinLeReifBDual_local
#print axioms LeanFzn.Solver.Propagation.propLinLeReifB_local
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_local
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_propLocal
#print axioms LeanFzn.Solver.Propagation.propLinLeReif_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_linLeReif_clamp_skipSoundOn

-- §3.0 P3 batch 4 (2026-10-25): DECLARED FOOTPRINTS FOR `minSlot`/`maxSlot`.
-- `propagatorOfProved` now gives `minSlot i j k` and `maxSlot i j k` the
-- footprint `[i, j, k]` (all three extrema are read). The locality proofs
-- reduce each run to those watched `getD` reads; `propagatorOfProved_local`
-- consumes them through `clampProps_local`. The refined and registered
-- `..._clamp_skipSoundOn` instances expose the audited footprints for the
-- queue. Measurements and the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.propMin_local
#print axioms LeanFzn.Solver.Propagation.propMax_local
#print axioms LeanFzn.Solver.Propagation.propMin_propLocal
#print axioms LeanFzn.Solver.Propagation.propMax_propLocal
#print axioms LeanFzn.Solver.Propagation.propMin_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propMax_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_minSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_maxSlot_clamp_skipSoundOn

-- §3.0 P3 batch 5 (2026-10-25): DECLARED FOOTPRINT FOR `arrayBoolAndSlot`.
-- `propagatorOfProved` now gives `arrayBoolAndSlot is k` the footprint
-- `k :: is` (the target and input Boolean pins). The locality proof reduces
-- the `all`/`find?` scans to pointwise `domBoolPin` reads over those slots
-- (`list_find?_congr_mem`, `propArrayBoolAnd_local`), and
-- `propagatorOfProved_local` consumes it through `clampProps_local`. The
-- refined and registered `..._clamp_skipSoundOn` instances expose the
-- audited footprint for the queue. Measurements and the acceptance record
-- are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.list_find?_congr_mem
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_local
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_propLocal
#print axioms LeanFzn.Solver.Propagation.propArrayBoolAnd_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_arrayBoolAndSlot_clamp_skipSoundOn

-- §3.0 P3 batch 6 (2026-10-25): DECLARED FOOTPRINT FOR `arrayVarIntElementSlot`.
-- `propagatorOfProved` now gives `arrayVarIntElementSlot is i k` the footprint
-- `i :: k :: is` (the index, the target and every table slot). The locality
-- proof localizes `avieEntry`, the `firstBadView` scans over index/target,
-- the table-membership scan and the `domsIntOnlyB` guard, yielding
-- `propArrayVarIntElement_local` and `propArrayVarIntElement_propLocal`;
-- `propagatorOfProved_local` consumes the latter through `clampProps_local`.
-- The refined and registered `..._clamp_skipSoundOn` instances expose the
-- audited footprint for the queue. Measurements and the acceptance record
-- are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.list_any_congr_mem
#print axioms LeanFzn.Solver.Propagation.firstBadView_local
#print axioms LeanFzn.Solver.Propagation.avieTableMemB_local
#print axioms LeanFzn.Solver.Propagation.aviePinTargetOkB_local
#print axioms LeanFzn.Solver.Propagation.aviePinTargetRes_local
#print axioms LeanFzn.Solver.Propagation.avieBelowBadB_local
#print axioms LeanFzn.Solver.Propagation.avieBelowRes_local
#print axioms LeanFzn.Solver.Propagation.avieAboveBadB_local
#print axioms LeanFzn.Solver.Propagation.avieAboveRes_local
#print axioms LeanFzn.Solver.Propagation.avieSingleBadB_local
#print axioms LeanFzn.Solver.Propagation.avieSingleRes_local
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_local
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_propLocal
#print axioms LeanFzn.Solver.Propagation.propArrayVarIntElement_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_arrayVarIntElementSlot_clamp_skipSoundOn

-- §3.0 P3 batch 7 (2026-10-25): DECLARED FOOTPRINT FOR `arrayVarBoolElementSlot`.
-- `propagatorOfProved` now gives `arrayVarBoolElementSlot is i k` the footprint
-- `i :: k :: is` (the index, the Boolean target and every table slot). The
-- locality proof localizes the entry/table helpers, the `avbeGuardB` guard,
-- the `firstBadView`/`avbeFirstBad` scans and the state-carrying emissions,
-- yielding `propArrayVarBoolElement_local` and
-- `propArrayVarBoolElement_propLocal`; `propagatorOfProved_local` consumes
-- the latter through `clampProps_local`. The refined and registered
-- `..._clamp_skipSoundOn` instances expose the audited footprint for the
-- queue. Measurements and the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.avbeTableMemB_local
#print axioms LeanFzn.Solver.Propagation.avbePinTargetOkB_local
#print axioms LeanFzn.Solver.Propagation.avbePinTargetRes_local
#print axioms LeanFzn.Solver.Propagation.avbeSingleBadB_local
#print axioms LeanFzn.Solver.Propagation.avbeSingleRes_local
#print axioms LeanFzn.Solver.Propagation.avbeGuardB_local
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_local
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_propLocal
#print axioms LeanFzn.Solver.Propagation.propArrayVarBoolElement_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_arrayVarBoolElementSlot_clamp_skipSoundOn

-- §3.0 P3 batch 8 (2026-10-25): DECLARED FOOTPRINT FOR `timesSlot`.
-- `propagatorOfProved` now gives `timesSlot i j k` the footprint `[i, j, k]`.
-- The locality proof shows `propTimes` reads only the extrema of the three
-- slots (`propTimes_local`) together with the target membership of each
-- bound update (`narrowLo_local`/`narrowHi_local`), yielding
-- `propTimes_propLocal`; `propagatorOfProved_local` consumes it through
-- `clampProps_local`. The refined and registered `..._clamp_skipSoundOn`
-- instances expose the audited footprint for the queue. Measurements and
-- the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.propTimes_local
#print axioms LeanFzn.Solver.Propagation.propTimes_propLocal
#print axioms LeanFzn.Solver.Propagation.propTimes_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_timesSlot_clamp_skipSoundOn

-- §3.0 P3 batch 9 (2026-10-25): DECLARED FOOTPRINTS FOR `absSlot` AND
-- `divGen`/`modGen`. `propagatorOfProved` now gives `absSlot i k` the
-- footprint `[i, k]`, and `divGen`/`modGen` every slot named by their three
-- `DomIntArg` operands (`(o₁.slots ++ o₂.slots ++ r.slots).map ...`). The
-- locality proof localizes the divisor pin (`divPin_local`), the dividend
-- extrema and the result-bound updates, yielding
-- `propAbs_local`/`propDiv_local`/`propMod_local` and their `PropLocalOne`
-- instances; `propagatorOfProved_local` consumes them through
-- `clampProps_local`. The refined and registered `..._clamp_skipSoundOn`
-- instances expose the audited footprints for the queue. Measurements and
-- the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.divPin_local
#print axioms LeanFzn.Solver.Propagation.propAbs_local
#print axioms LeanFzn.Solver.Propagation.propDiv_local
#print axioms LeanFzn.Solver.Propagation.propMod_local
#print axioms LeanFzn.Solver.Propagation.propAbs_propLocal
#print axioms LeanFzn.Solver.Propagation.propDiv_propLocal
#print axioms LeanFzn.Solver.Propagation.propMod_propLocal
#print axioms LeanFzn.Solver.Propagation.propAbs_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propDiv_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propMod_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_absSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_divGen_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_modGen_clamp_skipSoundOn

-- §3.0 P3 batch 10 (2026-10-25): DECLARED FOOTPRINTS FOR `maxGen`/`minGen`.
-- `propagatorOfProved` now gives `maxGen os r`/`minGen os r` the footprint
-- `(os.flatMap DomIntArg.slots ++ r.slots).map ...` (every slot named by the
-- operands and the result). The locality proof localizes the operand bound
-- folds (`minArgLo_local`/`maxArgHi_local`), the emitted cause clauses
-- (`argLoCauses_local`/`argHiCauses_local`) and the result-bound updates,
-- yielding `propMaxGen_local`/`propMinGen_local` and their `PropLocalOne`
-- instances; `propagatorOfProved_local` consumes them through
-- `clampProps_local`. The refined and registered `..._clamp_skipSoundOn`
-- instances expose the audited footprints for the queue. Measurements and
-- the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.list_flatMap_congr_mem
#print axioms LeanFzn.Solver.Propagation.argLoB_local
#print axioms LeanFzn.Solver.Propagation.argHiB_local
#print axioms LeanFzn.Solver.Propagation.minArgLo_local
#print axioms LeanFzn.Solver.Propagation.maxArgHi_local
#print axioms LeanFzn.Solver.Propagation.argLoCause_local
#print axioms LeanFzn.Solver.Propagation.argHiCause_local
#print axioms LeanFzn.Solver.Propagation.argLoCauses_local
#print axioms LeanFzn.Solver.Propagation.argHiCauses_local
#print axioms LeanFzn.Solver.Propagation.propMinGen_local
#print axioms LeanFzn.Solver.Propagation.propMaxGen_local
#print axioms LeanFzn.Solver.Propagation.propMinGen_propLocal
#print axioms LeanFzn.Solver.Propagation.propMaxGen_propLocal
#print axioms LeanFzn.Solver.Propagation.propMaxGen_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propMinGen_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_maxGen_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_minGen_clamp_skipSoundOn

-- §3.0 P3 batch 11 (2026-10-25): DECLARED FOOTPRINTS FOR THE ALL-SLOT
-- `minPair`/`maxPair` SHAPES AND THE GENERIC CHECKING PROPAGATOR.
-- `propagatorOfProved` now gives the all-slot pair shapes `[i, j, k]`
-- (they ride `propMin`/`propMax`) and every literal-operand pair shape the
-- footprint `(dcSlotsFull dc).map ...`, running `propCheck` at its readiness
-- gate, forced assignment and conflict clause. `propCheck_local` localizes
-- the gate, the `satisfiedB` check and the conflict clause through
-- `frameSingleton`/`propCheckAssign_getElem?`/`satisfiedB_dcSlotsFull_congr`;
-- the empty-domain/out-of-range ambiguity is absorbed by the gate (both
-- sides unready -> `.stable`). `list_filterMap_congr_mem` supplies the
-- conflict-clause congruence. The refined and registered
-- `..._clamp_skipSoundOn` instances expose the audited footprints for the
-- queue. Measurements and the acceptance record are in PLAN.md §3.0 P3.
#print axioms LeanFzn.Solver.Propagation.list_filterMap_congr_mem
#print axioms LeanFzn.Solver.Propagation.propCheck_local
#print axioms LeanFzn.Solver.Propagation.propCheck_propLocal
#print axioms LeanFzn.Solver.Propagation.propMinPairSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propMaxPairSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propCheck_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_minPairSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_maxPairSlot_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.propagatorOfProved_check_clamp_skipSoundOn
#print axioms LeanFzn.Solver.Propagation.Propagator.run_mk

-- §3.0 P6 (2026-10-25): LINEAR CONTIGUOUS `Dom` CONSTRUCTOR AND THE
-- HOISTED `array_int_element` TABLE VIEW.
-- `rangeInts_cons` splits a materialized interval; `rangeEnd?`/`rangeEndV?`
-- recognize a contiguous ascending run in one allocation-free pass and
-- `ofRange?` emits the `ofIntRange` shape. `enum_ofRange?`/`WF_ofRange?`
-- are the constructor laws the S1 frame migration needs; `ofRange?_spec`
-- and `rangeEnd?_range` expose the endpoint/interval correspondence.
-- `aieEntryEqV_map`/`aieSupportV_map` identify the hoisted table view with
-- the old per-probe definitions, and `aieSupportDomV_ofRange?` is the
-- compact-membership bridge used by the eventual prebuilt `Dom` frame.
#print axioms LeanFzn.Solver.Propagation.rangeInts_cons
#print axioms LeanFzn.Solver.Propagation.rangeEnd?_spec
#print axioms LeanFzn.Solver.Propagation.rangeEnd?_range
#print axioms LeanFzn.Solver.Propagation.Dom.rangeEndV?_decode
#print axioms LeanFzn.Solver.Propagation.Dom.ofRange?_spec
#print axioms LeanFzn.Solver.Propagation.Dom.enum_ofRange?
#print axioms LeanFzn.Solver.Propagation.Dom.WF_ofRange?
#print axioms LeanFzn.Solver.Propagation.aieEntryEqV_map
#print axioms LeanFzn.Solver.Propagation.aieSupportV_map
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_ofRange?

-- §3.0 P6b (2026-10-26): STRUCTURAL `filterLit` / `removeVal` AND THE
-- LINEARIZED `.holes` CONSTRUCTOR.
-- `gaps`/`mkHoles?` build the complement holes in one pass and
-- `gaps_eq_holesInts`/`mkHoles?_spec` fix its enumeration; `sortedIntsB_iff`
-- is the linear replacement for the quadratic `List.Pairwise` decision used
-- by `ofSmallInts?`/`ofHoles?`. `holesInts_ne_hi`/`_ne_lo`/`_le`/`_gt` and
-- the `enum_holes_filter_*` laws are the structural `.holes` filter steps,
-- packaged by `enum_filterHoles?`/`wf_filterHoles?`. The `.small` masks
-- (`clearBitMask`/`lowBitsMask`/`boolMask`) satisfy
-- `clearBitMask_testBit`/`lowBitsMask_testBit`, `smallInts_and` and
-- `smallBools_boolMask_lit`; `smallLe_iff` closes the `intLe` cut and
-- `enum_filterSmall?`/`wf_filterSmall?` are the constructor laws.
-- `filterLit` dispatches to these paths, with `enum_filterLit` unconditional,
-- `wf_filterLit` under `WF d`, and `card_filterLit_le` for mass.
-- `removeVal` dispatches to `filterLit` for the matching bool/int sorts,
-- is the identity on mismatched sorts, and keeps the enumerating fallback on
-- `.general`; `enum_removeVal` is unconditional, `wf_removeVal` preserves
-- `WF`, and `card_removeVal_le` bounds the mass.
#print axioms LeanFzn.Solver.Propagation.Dom.gaps_eq_holesInts
#print axioms LeanFzn.Solver.Propagation.Dom.sortedIntsB_iff
#print axioms LeanFzn.Solver.Propagation.Dom.mkHoles?_spec
#print axioms LeanFzn.Solver.Propagation.Dom.holesInts_ne_hi
#print axioms LeanFzn.Solver.Propagation.Dom.holesInts_ne_lo
#print axioms LeanFzn.Solver.Propagation.Dom.holesInts_le
#print axioms LeanFzn.Solver.Propagation.Dom.holesInts_gt
#print axioms LeanFzn.Solver.Propagation.Dom.enum_holes_filter_boolEq
#print axioms LeanFzn.Solver.Propagation.Dom.enum_holes_filter_ne_hi
#print axioms LeanFzn.Solver.Propagation.Dom.enum_holes_filter_ne_lo
#print axioms LeanFzn.Solver.Propagation.Dom.enum_holes_filter_le
#print axioms LeanFzn.Solver.Propagation.Dom.enum_holes_filter_gt
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterHoles?
#print axioms LeanFzn.Solver.Propagation.Dom.wf_filterHoles?
#print axioms LeanFzn.Solver.Propagation.Dom.clearBitMask_testBit
#print axioms LeanFzn.Solver.Propagation.Dom.lowBitsMask_testBit
#print axioms LeanFzn.Solver.Propagation.Dom.smallInts_and
#print axioms LeanFzn.Solver.Propagation.Dom.smallBools_boolMask_lit
#print axioms LeanFzn.Solver.Propagation.Dom.smallLe_iff
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterSmall?
#print axioms LeanFzn.Solver.Propagation.Dom.wf_filterSmall?
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterLit
#print axioms LeanFzn.Solver.Propagation.Dom.wf_filterLit
#print axioms LeanFzn.Solver.Propagation.Dom.card_filterLit_le
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterLit_eq_filter_of
#print axioms LeanFzn.Solver.Propagation.Dom.enum_removeVal
#print axioms LeanFzn.Solver.Propagation.Dom.wf_removeVal
#print axioms LeanFzn.Solver.Propagation.Dom.card_removeVal_le

-- PLAN §3.0 S1: the `Domain := Dom` library migration. The compact domain
-- carrier now backs the runtime frames; these are the new permutation,
-- extensional-equality, filter and presentation-sort laws that the migrated
-- consumers use. They must stay on the three standard axioms.
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.refl
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.symm
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.trans
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.length_eq
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.mem_iff
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.dom_mem_iff
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.subset
#print axioms LeanFzn.Solver.Propagation.Dom.Perm.map
#print axioms LeanFzn.Solver.Propagation.Dom.eqB_refl
#print axioms LeanFzn.Solver.Propagation.Dom.eqB_sound
#print axioms LeanFzn.Solver.Propagation.Dom.filter_eq_self
#print axioms LeanFzn.Solver.Propagation.Dom.wf_filter
#print axioms LeanFzn.Solver.Propagation.Dom.memBool_filter
#print axioms LeanFzn.Solver.Propagation.Dom.card_filter_le
#print axioms LeanFzn.Solver.Propagation.Dom.length_filter_le
#print axioms LeanFzn.Solver.Propagation.Dom.mem_filter
#print axioms LeanFzn.Integration.LcgHeur.keyBiasAux_map

-- PLAN §3.0 S1: the `@[implemented_by]` fast twins introduced for the
-- `Domain := Dom` runtime. Every twin is tied to its logical body by a
-- kernel-checked equality theorem; these profiles keep that seam visible to
-- the axiom audit. (`productiveFast_eq` and `literalImpossibleFast_eq` are
-- audited in the earlier P2b/P1b blocks.)
#print axioms LeanFzn.Solver.Propagation.Dom.smallIntsFast_eq
#print axioms LeanFzn.Solver.Propagation.Dom.cardFast_eq
#print axioms LeanFzn.Solver.Propagation.Dom.cardFast_eq_card
#print axioms LeanFzn.Solver.Propagation.Dom.minInt?Fast_eq
#print axioms LeanFzn.Solver.Propagation.Dom.maxInt?Fast_eq
#print axioms LeanFzn.Solver.Propagation.Dom.smallInts_min?_eq_head
#print axioms LeanFzn.Solver.Propagation.Dom.smallInts_max?_eq_log2
#print axioms LeanFzn.Solver.Propagation.Dom.smallInts_singleton_log2
#print axioms LeanFzn.Solver.Propagation.Dom.intSingleton?_eq
#print axioms LeanFzn.Solver.Propagation.Dom.allBoolBStruct_eq
#print axioms LeanFzn.Solver.Propagation.Dom.allIntBStruct_eq
#print axioms LeanFzn.Solver.Propagation.Dom.hasBoolBStruct_eq
#print axioms LeanFzn.Solver.Propagation.Dom.allIntBStruct_eq_allIntB
#print axioms LeanFzn.Solver.Propagation.Dom.valueHolds_intNe_neg
#print axioms LeanFzn.Solver.Propagation.frameViewedBFast_eq
#print axioms LeanFzn.Solver.Propagation.booleanSlotBFast_eq
#print axioms LeanFzn.Solver.Propagation.slotHasBoolFast_eq
#print axioms LeanFzn.Solver.Propagation.slotBoolBFast_eq
#print axioms LeanFzn.Solver.Propagation.slotSumOfDomainFast_eq
#print axioms LeanFzn.Solver.Propagation.sumsOfArrayFast_eq
#print axioms LeanFzn.Solver.Propagation.minContribFast_eq
#print axioms LeanFzn.Solver.Propagation.maxContribFast_eq
#print axioms LeanFzn.Solver.Propagation.linCauseMinPairFast_eq
#print axioms LeanFzn.Solver.Propagation.linCauseMaxPairFast_eq
#print axioms LeanFzn.Solver.Propagation.pinIntFast_eq
#print axioms LeanFzn.Solver.Propagation.filterFrameFast_eq

-- PLAN §3.0 S1: the cached-bounds fast twin of the `linEq` sweep. The
-- per-call cache replaces several hundred frame-spine `getD` reads by one
-- read per involved slot; every layer of the transcription
-- (contributions, sums, causes, narrowing, arms, deduction kernel, sweep)
-- carries a kernel-checked equality, and `propLinEq2Fast_eq` ties the whole
-- twin to `propLinEq2`.
#print axioms LeanFzn.Solver.Propagation.linLookupB_aux
#print axioms LeanFzn.Solver.Propagation.linLookupB_eq
#print axioms LeanFzn.Solver.Propagation.minContribB_eq
#print axioms LeanFzn.Solver.Propagation.maxContribB_eq
#print axioms LeanFzn.Solver.Propagation.sumMinB_eq
#print axioms LeanFzn.Solver.Propagation.sumMaxB_eq
#print axioms LeanFzn.Solver.Propagation.linCauseMinPairB_eq
#print axioms LeanFzn.Solver.Propagation.linCauseMaxPairB_eq
#print axioms LeanFzn.Solver.Propagation.linCausesMinB_eq
#print axioms LeanFzn.Solver.Propagation.linCausesMaxB_eq
#print axioms LeanFzn.Solver.Propagation.narrowHiB_eq
#print axioms LeanFzn.Solver.Propagation.narrowLoB_eq
#print axioms LeanFzn.Solver.Propagation.linEqArmHiMinB_eq
#print axioms LeanFzn.Solver.Propagation.linEqArmLoMaxB_eq
#print axioms LeanFzn.Solver.Propagation.linEqArmLoMinB_eq
#print axioms LeanFzn.Solver.Propagation.linEqArmHiMaxB_eq
#print axioms LeanFzn.Solver.Propagation.linGenArmHiMinB_eq
#print axioms LeanFzn.Solver.Propagation.linGenArmLoMinB_eq
#print axioms LeanFzn.Solver.Propagation.linGenArmLoMaxB_eq
#print axioms LeanFzn.Solver.Propagation.linGenArmHiMaxB_eq
#print axioms LeanFzn.Solver.Propagation.linDeduceEqB_eq
#print axioms LeanFzn.Solver.Propagation.linSweep_congr
#print axioms LeanFzn.Solver.Propagation.propLinEq2Fast_eq

-- Wave 2: the `syncCands`/`syncClause` `implemented_by` twins. The final hole
-- branch of `syncCands` recognises a fully materialised interval in one linear
-- pass instead of the quadratic `List.contains` sweep, and tests residual
-- membership structurally (`memIntViewB`); `syncClause` defers building the
-- rejected-value list `W` until its cheap guards pass. Both twins carry a
-- kernel-checked extensionality theorem, so the logical definitions and all
-- existing statements are unchanged.
#print axioms LeanFzn.Solver.Propagation.syncCandsFast_eq
#print axioms LeanFzn.Solver.Propagation.syncClauseFast_eq
#print axioms LeanFzn.Solver.Propagation.memIntViewB_iff
#print axioms LeanFzn.Solver.Propagation.syncCands_filter_memIntViewB
#print axioms LeanFzn.Solver.Propagation.syncCands_hole_branch_eq
#print axioms LeanFzn.Solver.Propagation.syncCands_hole_filter_eq_nil
#print axioms LeanFzn.Solver.Propagation.rangeInts_contains_of_lt_of_lt
#print axioms LeanFzn.Solver.Propagation.filterMap_intView_map_int

-- PLAN F0a (2026-10-28): stack-safe wide-domain enumeration and explanation
-- twins. `Dom.enum` of a wide `.holes` interval used to recurse once per
-- value (`i :: holesIntsGo ...`), aborting the native binary at ~62M values.
-- `holesIntsGoTR` accumulates in reverse and is a plain tail call; the
-- `implemented_by` seam keeps `holesInts`/`Dom.enum` as the specification.
-- The remaining twins replace `List.all`/`List.any`-style scans and the
-- rejected-value list construction by loop-compiled folds over the same
-- lists. Every runtime substitution carries a kernel-checked extensionality
-- theorem.
#print axioms LeanFzn.Solver.Propagation.Dom.holesIntsGoTR_eq
#print axioms LeanFzn.Solver.Propagation.Dom.holesIntsGoTR_nil_acc
#print axioms LeanFzn.Solver.Propagation.Dom.holesInts_nil_eq_rangeInts
#print axioms LeanFzn.Solver.Propagation.Dom.holesWFBool_iff
#print axioms LeanFzn.Solver.Propagation.Dom.boolSingleton?_eq
#print axioms LeanFzn.Solver.Propagation.valueAllFast_eq
#print axioms LeanFzn.Solver.Propagation.syncExplain_eq_syncExplainList
#print axioms LeanFzn.Solver.Propagation.syncExplainFold_eq
#print axioms LeanFzn.Solver.Propagation.syncExplainDom_eq
#print axioms LeanFzn.Solver.Propagation.snapLitFast_eq

-- S3a: allDiff watch locality. `inRangeSlots` now keeps exactly the
-- nonempty in-`is` slots, `propAllDiffLCG_domains_local` is the
-- State-level locality theorem, and the registration declares `is` as the
-- footprint (wired in `ScheduledFamilies.propagatorOfProved_local`).
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.mem_inRangeSlots_left
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.getSlot_ne_nil_lt_length
#print axioms LeanFzn.Solver.Propagation.DomainFiltering.lt_length_of_mem_inRangeSlots
#print axioms LeanFzn.Solver.Propagation.inRangeSlots_congr
#print axioms LeanFzn.Solver.Propagation.distinctUnionVals_congr
#print axioms LeanFzn.Solver.Propagation.propAllDiff_test_congr
#print axioms LeanFzn.Solver.Propagation.hallClause_congr
#print axioms LeanFzn.Solver.Propagation.allDiffElimB_congr
#print axioms LeanFzn.Solver.Propagation.allDiffElimTarget_congr
#print axioms LeanFzn.Solver.Propagation.allDiffElimFirst_congr
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCG_domains_local

-- PLAN P6d (2026-10-27): COMPACT STRUCTURAL `PoolCache`.
-- `SchedulerConfig.init` no longer builds the 13M-entry `Std.HashSet` of
-- `litPool orig`; `PoolCache.contains` answers the only used operation
-- structurally over `orig`. `memIntViewB` moved to `Operations` so the
-- formula is available below `ExplainedPropagation`; its exactness theorem
-- is stated there (`memIntViewB_iff_intView`) and the historical
-- `memIntViewB_iff` remains as the same statement. `atomShape` is the
-- per-slot value test (`intLe u` iff `u` or `u+1` is in the integer view),
-- `slotAtomPool_mem_iff` relates it to the pool enumeration, and
-- `atomPoolContainsAux_eq`/`atomPool_mem_iff`/`litPool_mem_iff`/`poolContains_eq`
-- chain it to exact `litPool` membership. `litPoolHash_contains` is the
-- scheduler-facing equality consumed by `PoolHashAligned`.
#print axioms LeanFzn.Solver.Propagation.memIntViewB_iff_intView
#print axioms LeanFzn.Solver.UIP.threshPool_mem_iff
#print axioms LeanFzn.Solver.UIP.slotAtomPool_mem_iff
#print axioms LeanFzn.Solver.UIP.slotAtomPool_boolFlip_mem
#print axioms LeanFzn.Solver.UIP.atomPoolBase_boolFlip_mem
#print axioms LeanFzn.Solver.UIP.atomPoolContainsAux_eq
#print axioms LeanFzn.Solver.UIP.exists_mem_boolFlip_eq
#print axioms LeanFzn.Solver.UIP.atomPool_mem_iff
#print axioms LeanFzn.Solver.UIP.mem_litPool_blocks
#print axioms LeanFzn.Solver.UIP.litPool_mem_iff
#print axioms LeanFzn.Solver.UIP.poolContains_eq
#print axioms LeanFzn.Solver.UIP.atomSlot_boolFlip
#print axioms LeanFzn.Solver.UIP.atomShape_boolFlip
#print axioms LeanFzn.Solver.Propagation.Atom.boolFlip_boolFlip

-- S2a (2026-10-27): structural literal filtering on the compact domain.
-- `Dom.filterLitKeep` returns the original domain when the literal drops no
-- value (so equality-sensitive UIP proofs keep their definitional fixed
-- point) and the structural `Dom.filterLit` otherwise; its enumeration is
-- exactly `Dom.filter l.valueHolds`.  `FrameFilter`/`SparseFrame` call it,
-- and the positional `filterSlotsD`/`filterFrameD`/`massD` bridges moved to
-- `CompactDomainBridges.lean` above `FrameFilter`, breaking the old
-- `CompactDomain` -> `FrameFilter` cycle.  Every statement below is exact.
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterLitKeep
#print axioms LeanFzn.Solver.Propagation.Dom.length_filterLitKeep_eq
#print axioms LeanFzn.Solver.Propagation.Dom.mem_filterLitKeep_iff
#print axioms LeanFzn.Solver.Propagation.Dom.card_filterLitKeep_le
#print axioms LeanFzn.Solver.Propagation.Dom.filterLitKeep_eq_self_of_forall
#print axioms LeanFzn.Solver.Propagation.Dom.enum_filterSlotsD
#print axioms LeanFzn.Solver.Propagation.Dom.filterSlotsD_length
#print axioms LeanFzn.Solver.Propagation.Dom.filterSlotsD_mass_le
#print axioms LeanFzn.Solver.Propagation.Dom.filterFrameD_enum
#print axioms LeanFzn.Solver.Propagation.Dom.massD_eq_frameMass
#print axioms LeanFzn.Solver.Propagation.Frame.covers_filterFrame_iff
#print axioms LeanFzn.Solver.Propagation.Frame.filterFrame_eq_none_iff
#print axioms LeanFzn.Solver.Propagation.SparseFrame.Frame.covers_filterFrame_iff
#print axioms LeanFzn.Solver.Propagation.SparseFrame.Frame.filterFrame_eq_none_iff
#print axioms LeanFzn.Solver.Propagation.SparseFrame.filterSlots_covers_iff_filterFrame
#print axioms LeanFzn.Solver.Propagation.SparseRun.Frame.deduce_narrowed_mass_le

-- S2b (2026-10-27): the D0 frame denotation bridge and the structural
-- bound twins.  `Frame.denote` is the slot-wise `Dom.enum` box and
-- `PrefixFrame.denote` the prefix-singletons-plus-remaining form; the
-- `denote_eq` theorems are the D0 names, and `allAssigns_dom_eq_enum`
-- identifies the compact `allAssigns` with its enumeration.  The
-- structural `narrowLoFast`/`narrowHiFast` are installed with
-- `implemented_by` behind the kernel-checked `_eq` theorems.
#print axioms LeanFzn.Solver.Propagation.Frame.denote_eq
#print axioms LeanFzn.Solver.Propagation.PrefixFrame.denote_eq
#print axioms LeanFzn.Solver.Propagation.Frame.denote_length
#print axioms LeanFzn.Solver.Propagation.Frame.denote_getD
#print axioms LeanFzn.Solver.Propagation.Frame.denote_mass
#print axioms LeanFzn.Solver.Propagation.allAssigns_dom_eq_enum
#print axioms LeanFzn.Solver.Propagation.FrameCovers.denote_iff
#print axioms LeanFzn.Solver.Propagation.Frame.denote_pin
#print axioms LeanFzn.Solver.Propagation.Frame.denote_retire
#print axioms LeanFzn.Solver.Propagation.minInt?_eq_domMinI_enum
#print axioms LeanFzn.Solver.Propagation.maxInt?_eq_domMaxI_enum
#print axioms LeanFzn.Solver.Propagation.narrowLoFast_eq
#print axioms LeanFzn.Solver.Propagation.narrowHiFast_eq

-- S3a (2026-10-27): the structural all-different pigeonhole twin.
-- `propAllDiffD` tests nonemptiness with the cardinality predicate
-- `Dom.isEmpty` and reads only the family's slots, instead of mapping the
-- whole frame through `Dom.enum`; `hallClauseD` builds the Hall clause
-- from the same structural reads.  The reference `propAllDiffLCG` is
-- unchanged and carries the kernel-checked `propAllDiffLCGFast_eq`.
#print axioms LeanFzn.Solver.Propagation.inRangeSlotsD_eq
#print axioms LeanFzn.Solver.Propagation.distinctUnionValsD_eq
#print axioms LeanFzn.Solver.Propagation.propAllDiffD_eq
#print axioms LeanFzn.Solver.Propagation.hallClauseD_eq
#print axioms LeanFzn.Solver.Propagation.propAllDiffLCGFast_eq

-- S3b (2026-10-27): structural element-family target support.
-- `Dom.memBool_enum` relates compact membership to the legacy list
-- membership; the support scan reads the target `Dom` structurally and only
-- enumerates a one-element singleton (`domSingleInt?`).  The reference
-- `propArrayIntElementV` is unchanged and carries the kernel-checked
-- `propArrayIntElementVFast_eq`.
#print axioms LeanFzn.Solver.Propagation.Dom.memBool_enum
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_enum
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_enum_fun
#print axioms LeanFzn.Solver.Propagation.aieSupportDomV_enum_map
#print axioms LeanFzn.Solver.Propagation.aieSupportDomVArr_none
#print axioms LeanFzn.Solver.Propagation.aieSupportDomVArr_array
#print axioms LeanFzn.Solver.Propagation.aieSupportCached_gate_general
#print axioms LeanFzn.Solver.Propagation.domSingleInt?_eq_some_iff
#print axioms LeanFzn.Solver.Propagation.enum_match_domSingleInt?
#print axioms LeanFzn.Solver.Propagation.propArrayIntElementVFast_eq

-- S4b (2026-10-27): structural domain inclusion for the watch certificate.
-- `Dom.subsetB` answers the frozen enumeration inclusion from the compact
-- representation, with one-sided fast tests plus the enum fallback; the exact
-- characterization `subsetB_eq_valuesSubsetB` needs no canonicality premise.
-- `valueDomainSubsetB` uses `Dom.eqB`/`Dom.subsetB` and is pointwise equal to
-- the old enum test.
#print axioms LeanFzn.Solver.Propagation.Dom.bitsSubsetGo_spec
#print axioms LeanFzn.Solver.Propagation.Dom.bitsSubsetB_spec
#print axioms LeanFzn.Solver.Propagation.Dom.mem_smallBools_of_bitsSubsetB
#print axioms LeanFzn.Solver.Propagation.Dom.mem_smallInts_of_bitsSubsetB
#print axioms LeanFzn.Solver.Propagation.Dom.holesSubsetB_sound
#print axioms LeanFzn.Solver.Propagation.Dom.subsetBFast_sound
#print axioms LeanFzn.Solver.Propagation.Dom.subsetB_eq_enum_all
#print axioms LeanFzn.Solver.Propagation.Dom.all_memBool_eq_valuesSubsetB
#print axioms LeanFzn.Solver.Propagation.Dom.subsetB_eq_valuesSubsetB
#print axioms LeanFzn.Solver.Propagation.Dom.subsetB_sound
#print axioms LeanFzn.Solver.Propagation.valuesEqB_self
#print axioms LeanFzn.Solver.Propagation.valueDomainSubsetB_eq

-- S6 (2026-10-27): direct-`Dom` compiler path with a single expansion pass.
-- The compact slot builders enumerate like the legacy list builders and are
-- canonical, `expandDomOf` shares one `expandPlan`, and `compileModelFast`
-- is the logical `compileModel` at every model (including rejections).
#print axioms LeanFzn.Solver.Propagation.Dom.ofIntRange_eq
#print axioms LeanFzn.Compiler.Domains.varDomainDom_eq
#print axioms LeanFzn.Compiler.Domains.varDomainDom_canonical
#print axioms LeanFzn.Compiler.Domains.enumSlot_ofListSlot
#print axioms LeanFzn.Compiler.Domains.canonSlot_ofListSlot
#print axioms LeanFzn.Compiler.Domains.declSlotDom_eq
#print axioms LeanFzn.Compiler.Domains.declSlotDom_canonical
#print axioms LeanFzn.Compiler.Domains.declSlotsDom_eq
#print axioms LeanFzn.Compiler.Domains.declSlotsDom_canonical
#print axioms LeanFzn.Compiler.Domains.slotsCheckedDom_eq
#print axioms LeanFzn.Compiler.Domains.slotsCheckedDom_canonical
#print axioms LeanFzn.Compiler.modelSlotsDom_eq
#print axioms LeanFzn.Compiler.modelSlotsDom_names
#print axioms LeanFzn.Compiler.expandPlanDom_eq
#print axioms LeanFzn.Compiler.modelAuxSlotsDom_eq
#print axioms LeanFzn.Compiler.modelAuxSlotsDom_canonical
#print axioms LeanFzn.Compiler.modelExpandDom_eq
#print axioms LeanFzn.Compiler.assembleDom_eq
#print axioms LeanFzn.Compiler.compileModelFast_eq

-- S7b (2026-10-27): enum-free gate fast paths.
-- `gateOk` and `domPruningOkB` keep their kernel bodies; the structural twins
-- read `Dom.intViewableB`, `Dom.allIntBStruct` and `Dom.allBoolBStruct`
-- instead of scanning every `Dom.enum`.  The four equalities are the seam.
#print axioms LeanFzn.Solver.Propagation.Dom.enum_all_intView_eq
#print axioms LeanFzn.Solver.Propagation.Dom.enum_all_intViewBeq_eq
#print axioms LeanFzn.Solver.Propagation.gateOkFast_eq
#print axioms LeanFzn.Solver.Propagation.domPruningOkFastB_eq

-- S6b (2026-10-27): preserve declared finite types with no constant-set
-- restrictions.  `restrictVarType` leaves `.intRange`/`.intSet` intact when
-- `setInConds` is empty, so the S6 compiler keeps the compact interval; the
-- range/set membership and exactness/covers lemmas are reproved for both
-- branches.  `restrictVarType_range_int`, `restrictVarType_set_int` and
-- `restrictVarType_contains_imp` keep their original statements and are
-- already certified above (lines 534-536); no duplicate profiles here.
#print axioms LeanFzn.Compiler.exists_setInConds_cons
#print axioms LeanFzn.Compiler.restrictVarType_range_nil
#print axioms LeanFzn.Compiler.restrictVarType_range_cons
#print axioms LeanFzn.Compiler.restrictVarType_set_nil
#print axioms LeanFzn.Compiler.restrictVarType_set_cons
#print axioms LeanFzn.Compiler.exists_int_of_restrictVarType_contains

-- S7c (2026-10-27): structural mixed-route gate.  `mixedKitGateFastB` keeps
-- its statement and replaces the four `Dom.enum` scans with
-- `allIntOrBoolStruct`, `Dom.allIntBStruct`, `Dom.allBoolBStruct` and
-- `viewsNodupStruct`; only `.general` still reads its stored list.
-- `mixedKitGateFastB_eq` keeps its original statement and is already
-- certified above (line 767); no duplicate profile here.
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.isIntOrBoolV_int
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.isIntOrBoolV_bool
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.all_isIntOrBoolV_map_int
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.all_isIntOrBoolV_smallBools
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.allIntBStruct_eq_enum
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.allBoolBStruct_eq_enum
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.allIntOrBoolStruct_eq
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.map_valueIntView_eq
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.enum_small_true
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.enum_small_false
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.enum_holes
#print axioms LeanFzn.Solver.UIP.LcgMixedCompiledKit.viewsNodupStruct_eq

-- S7a (2026-10-27): structural inactivity fast path for the activity
-- presentation.  `sortDom`/`reorderAux` keep their kernel bodies and gain
-- `implemented_by` twins that skip the domain enumeration when no
-- constant-bound constraint and no clause literal names the slot.  The
-- equality theorems are the seam; the fallback is the old body.
#print axioms LeanFzn.Integration.LcgHeur.constHits_eq_zero_of_not_mem
#print axioms LeanFzn.Integration.LcgHeur.pinHits_eq_zero_of_slot_not_mem
#print axioms LeanFzn.Integration.LcgHeur.valAct_eq_zero_of_inactiveSlotB
#print axioms LeanFzn.Integration.LcgHeur.keyAux_fst_eq_zero
#print axioms LeanFzn.Integration.LcgHeur.keyAux_uniform_of_valAct_zero
#print axioms LeanFzn.Integration.LcgHeur.sortDomFast_eq
#print axioms LeanFzn.Integration.LcgHeur.sortDomFastOf_eq
#print axioms LeanFzn.Integration.LcgHeur.reorderAuxFastOf_eq
#print axioms LeanFzn.Integration.LcgHeur.reorderAuxFast_eq

-- PLAN F1 (2026-10-28): the frozen search-configuration surface. The default
-- record maps to the unchanged `HeurOpts`, so the optioned certified entries
-- keep exactly the pre-F1 default route; the parser and preset table are data
-- definitions and add no axioms.
#print axioms LeanFzn.Integration.SearchConfig.toHeurOpts_default

-- PLAN K0 (2026-10-29): return-beside engine counters.  The stats twins run
-- the identical certified search and return the terminal `SearchStats`; the
-- `_fst` theorems are the seam proving that the verdict component is the
-- certified entry's.  `SearchStats.steps` is a non-semantic observation.
#print axioms LeanFzn.Solver.UIP.solve_schedStats_fst
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeurStats_fst
#print axioms LeanFzn.Integration.LcgHeur.lcgRunHeurBiasStats_fst
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurStats_fst
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurBiasStats_fst
#print axioms LeanFzn.Integration.LcgHeur.solveCompiledLcgHeurOptsStats_fst
#print axioms LeanFzn.Integration.lcgRunAnnotStats_fst
#print axioms LeanFzn.Integration.solveCompiledAnnotStats_fst
#print axioms LeanFzn.Integration.solveSearchConfigWithStats_fst
#print axioms LeanFzn.Integration.solveSearchConfigStats_fst
#print axioms LeanFzn.Integration.solveCertifiedStats_fst

-- Wave 2 K1 (2026-10-29): incremental `syncSlot` explanation. The new
-- `syncClauseWithTrail`/`syncOneWithTrail`/`syncSlotFast` twins take the
-- slot-filtered trail and the slot's original Boolean-ness as arguments
-- (computed once per slot), use the structural `valueAllDom` guard and the
-- `impliesFast` implication test on non-Boolean slots, and thread each pushed
-- entry back into the trail. `syncSlotFast_eq` is the `implemented_by` seam to
-- the unchanged `syncSlot`; the auxiliary equalities are the kernel-checked
-- steps of that proof.
#print axioms LeanFzn.Solver.Propagation.trailOnSlot_mem_slot
#print axioms LeanFzn.Solver.Propagation.trailOnSlot_append
#print axioms LeanFzn.Solver.Propagation.valueAllDom_eq
#print axioms LeanFzn.Solver.Propagation.impliesP_eq_impliesFast
#print axioms LeanFzn.Solver.Propagation.any_impliesP_eq_any_impliesFast
#print axioms LeanFzn.Solver.Propagation.syncClauseWithTrail_eq_syncClauseFast
#print axioms LeanFzn.Solver.Propagation.syncOneWithTrail_fst_eq
#print axioms LeanFzn.Solver.Propagation.syncOneWithTrail_snd_eq
#print axioms LeanFzn.Solver.Propagation.syncCands_cases_k1
#print axioms LeanFzn.Solver.Propagation.syncCands_slot_k1
#print axioms LeanFzn.Solver.Propagation.syncSlotFastAux_eq
#print axioms LeanFzn.Solver.Propagation.syncSlotFast_eq
-- PLAN F5 (2026-10-29): the fuel-budgeted prefix of the certified phase
-- driver.  `runPhaseBudget` observes the SAME kernel step; the two soundness
-- theorems transfer every terminal budget result to the complete certified
-- driver at the same configuration, and `runPhaseBudget_mono` is the
-- restart/portfolio stability fact (a finished result survives more fuel).
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_zero
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_succ
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_sat
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_unsat
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_succ_terminal
#print axioms LeanFzn.Solver.UIP.runPhaseBudget_mono

-- PLAN F5 (2026-10-29): the budgeted seeded run and the restart/portfolio
-- driver.  `lcgSeedRunBudget` is `runPhaseBudget` at the same kernel and
-- initializer as `lcgSeedRun`; the `_sat`/`_unsat` theorems are the
-- problem-level claims, and `_sat_run`/`_unsat_run` identify a terminal
-- budget result with the complete seeded run's verdict.  `lcgSeedSolverBudget`
-- puts the ordered independent probes in front of the complete `lcgSolveDb`
-- route; every `SeedCertSolver` field is proved from these facts.
#print axioms LeanFzn.Integration.lcgSeedFrameGate
#print axioms LeanFzn.Integration.lcgSeedKernel_step
#print axioms LeanFzn.Integration.lcgSeedInit_reach
#print axioms LeanFzn.Integration.lcgSeedRunBudget_unfold
#print axioms LeanFzn.Integration.lcgSeedRunBudget_sat_run
#print axioms LeanFzn.Integration.lcgSeedRunBudget_unsat_run
#print axioms LeanFzn.Integration.lcgSeedRunBudget_sat
#print axioms LeanFzn.Integration.lcgSeedRunBudget_unsat
#print axioms LeanFzn.Integration.lcgSeedRunBudget_mono

-- PLAN F5 (2026-10-29): schedules and the budgeted solver instance.  The Luby
-- list is the true block-recurrence prefix (kernel-reducible concrete
-- checks), the geometric list is the doubling schedule, and the probe
-- transfer theorems state that any terminal probe is a terminal result of
-- the complete seeded run.  The two budgeted-solver projections are
-- definitional; the `SeedCertSolver` field proofs consume the transfer
-- theorems above.
#print axioms LeanFzn.Integration.lubyBlocks_length
#print axioms LeanFzn.Integration.lubyDepthAux_bound
#print axioms LeanFzn.Integration.lubyDepth_bound
#print axioms LeanFzn.Integration.lubyList_length
#print axioms LeanFzn.Integration.geomList_length
#print axioms LeanFzn.Integration.probeBudgets_none
#print axioms LeanFzn.Integration.probeBudgets_luby
#print axioms LeanFzn.Integration.probeBudgets_geom
#print axioms LeanFzn.Integration.probeBudgets_length
#print axioms LeanFzn.Integration.budgetProbe_nil
#print axioms LeanFzn.Integration.budgetProbe_cons
#print axioms LeanFzn.Integration.budgetProbe_sat
#print axioms LeanFzn.Integration.budgetProbe_unsat
#print axioms LeanFzn.Integration.lcgSeedSolverBudget_gate
#print axioms LeanFzn.Integration.lcgSeedSolverBudget_leaf
#print axioms LeanFzn.Integration.restartSegments_none
#print axioms LeanFzn.Integration.restartSegments_length

-- PLAN F5 (2026-10-29): the restart/portfolio driver.  `probeLoop_inv` is the
-- per-probe soundness/improvement/bound/seed invariant, including the
-- cross-segment transfer `accepts_curP_mono` and the pairwise-last lemma; the
-- source-level `optimizePortfolioConfig_*` corollaries are the only claims a
-- CLI may print.  The final complete segment is the sole source of the
-- `complete` flag.
#print axioms LeanFzn.Integration.accepts_curP_mono
#print axioms LeanFzn.Integration.betterB_of_pairwise_last
#print axioms LeanFzn.Integration.probeLoop_inv
#print axioms LeanFzn.Integration.portfolioRun_inv
#print axioms LeanFzn.Integration.optimizePortfolioConfig_inv
#print axioms LeanFzn.Integration.optimizePortfolioConfig_solution_sound
#print axioms LeanFzn.Integration.optimizePortfolioConfig_improving
#print axioms LeanFzn.Integration.optimizePortfolioConfig_optimal
#print axioms LeanFzn.Integration.optimizePortfolioConfig_unsat
#print axioms LeanFzn.Integration.optimizePortfolioConfig_total
#print axioms LeanFzn.Integration.optimizeRestartConfig_eq
#print axioms LeanFzn.Integration.optimizeRestartConfigOf_eq

-- K0b (2026-10-29): scheduled DB/stats twin and one-prompt step.  `runSched`
-- now binds the scheduled prompt pair once per recursive step; the new
-- `runSchedDb` runs the same scheduled recursion and returns the terminal
-- `SchedulerConfig`; `solve_schedDb`/`solve_schedDbStats` are its initialized
-- and instrumented entries.  `runSchedDb_fst` is the unconditional verdict
-- seam to `runSched`; `solve_schedDbStats_fst` is the seam to `solve_sched`;
-- `solve_schedDbStats_snd`/`solve_schedStats_snd` locate the counters in the
-- terminal record of the scheduled run.  No certified semantic statement
-- changes; the counters remain observations.
#print axioms LeanFzn.Solver.UIP.runSched_congr
#print axioms LeanFzn.Solver.UIP.runSched_sat
#print axioms LeanFzn.Solver.UIP.runSched_unsat
#print axioms LeanFzn.Solver.UIP.runSched_propagate
#print axioms LeanFzn.Solver.UIP.runSched_decide
#print axioms LeanFzn.Solver.UIP.runSched_analyzeConflict
#print axioms LeanFzn.Solver.UIP.runSched_learnBackjumpAssert
#print axioms LeanFzn.Solver.UIP.runSched_localExclude
#print axioms LeanFzn.Solver.UIP.runSched_chronologicalFallback
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.phaseNextSched_decrease
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_congr
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_sat
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_unsat
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_propagate
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_decide
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_analyzeConflict
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_learnBackjumpAssert
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_localExclude
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_chronologicalFallback
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_fst
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.runSchedDb_reach
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.solve_schedDb_fst
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.solve_schedDbStats_fst
#print axioms LeanFzn.Solver.UIP.LcgPhaseSchedDb.solve_schedDbStats_snd
#print axioms LeanFzn.Solver.UIP.solve_schedStats_snd

-- PLAN F4-bisect (2026-10-29): the certified objective-bisection driver.
-- `optKey`/`optVal` normalize both directions to a smaller-is-better integer
-- key; `rootBounds?_sound` bounds every readable objective key by the root
-- domain extremes; `certProbeFn_sat`/`_unsat` are the complete probe's
-- membership/completeness claims; `bisectAccInv_sat`/`_unsat` and
-- `bisectTerminal_inv` are the interval/accumulator invariants;
-- `bisectFallback_inv` is the R1 exhausted-probe fallback; the
-- `optimizeBisect_*` corollaries are the only claims a CLI may print.  The
-- phase-2a streaming wrapper (`optimizeBisectStream_eq`) emits exactly the
-- trace proved sound by `bisectLoopEmitSpec_sound`, and
-- `bisectLoopEmitSpec_solution_sound` is its source-level transfer.  The
-- module remains unbuilt in this worktree; the audit lines are the frozen
-- public surface to check after the phase-2b build.
#print axioms LeanFzn.Integration.optKey_optVal
#print axioms LeanFzn.Integration.optVal_optKey
#print axioms LeanFzn.Integration.betterB_iff_optKey_lt
#print axioms LeanFzn.Integration.betterB_optVal_succ
#print axioms LeanFzn.Integration.accepts_improve_of_betterB
#print axioms LeanFzn.Integration.read_of_accepts_curP_some
#print axioms LeanFzn.Integration.rootBounds?_sound
#print axioms LeanFzn.Integration.midKey_ge
#print axioms LeanFzn.Integration.midKey_lt
#print axioms LeanFzn.Integration.midKey_succ_le
#print axioms LeanFzn.Integration.certProbeFn_sat
#print axioms LeanFzn.Integration.certProbeFn_unsat
#print axioms LeanFzn.Integration.bisectAccInv_sat
#print axioms LeanFzn.Integration.bisectAccInv_unsat
#print axioms LeanFzn.Integration.bisectTerminal_inv
#print axioms LeanFzn.Integration.loopInv_to_bisectRunInv
#print axioms LeanFzn.Integration.loopInvWith_prefix_to_bisectRunInv
#print axioms LeanFzn.Integration.bisectFallback_inv
#print axioms LeanFzn.Integration.bisectFallback_complete
#print axioms LeanFzn.Integration.bisectLoop_inv
#print axioms LeanFzn.Integration.bisectLoop_complete
#print axioms LeanFzn.Integration.bisectRunFor_inv
#print axioms LeanFzn.Integration.bisectRunFor_complete
#print axioms LeanFzn.Integration.bisectLoopEmitSpec_run
#print axioms LeanFzn.Integration.bisectLoopEmitSpec_sound
#print axioms LeanFzn.Integration.bisectLoopEmit_eq
#print axioms LeanFzn.Integration.optimizeBisect_inv
#print axioms LeanFzn.Integration.optimizeBisectStream_eq
#print axioms LeanFzn.Integration.bisectLoopEmitSpec_solution_sound
#print axioms LeanFzn.Integration.optimizeBisect_solution_sound
#print axioms LeanFzn.Integration.optimizeBisect_improving
#print axioms LeanFzn.Integration.optimizeBisect_optimal
#print axioms LeanFzn.Integration.optimizeBisect_unsat
#print axioms LeanFzn.Integration.optimizeBisect_total

-- PLAN K2 (merged 2026-10-30): the fused stamp-scan experiment is test-only,
-- not wired into the default prompt.  The `_eq` theorems are the exactness
-- surface; `nextPruningEventFastSched_fst_eq`/`_OK` transfer the certified
-- prompt event and scheduler invariant to the fused twin.  No production
-- theorem statement changes; the measured `pscanNs` win was below the K2
-- acceptance target, so the default scan stays `scanPropagatorsSched`.
#print axioms LeanFzn.Solver.Propagation.stampMatchAt_eq
#print axioms LeanFzn.Solver.Propagation.stampTest_eq
#print axioms LeanFzn.Solver.Propagation.scanPropagatorsSchedAuxFast_eq
#print axioms LeanFzn.Solver.Propagation.scanPropagatorsSchedFast_eq
#print axioms LeanFzn.Solver.Propagation.nextPruningEventFastSched_eq
#print axioms LeanFzn.Solver.Propagation.nextPruningEventFastSched_fst_eq
#print axioms LeanFzn.Solver.Propagation.nextPruningEventFastSched_OK

-- PLAN F6.1 (2026-10-30): the witness-checked dive primal route.
-- `objSlot?_sound` is the integer slot read; `diveSlice_sound` (T9) is the
-- class-W candidate claim; `compileOpt_optimal_of_bound` (T1) and
-- `optLoopWith_optimal` (T2) transfer the bounded B&B's terminal claim, and
-- `primalBound_optimal` (T4) is the completed-empty-B&B case.  The primal
-- route never prints `==========` itself: the certified B&B on the strictly
-- bounded problem remains the only optimality source.
#print axioms LeanFzn.Integration.objSlot?_sound
#print axioms LeanFzn.Integration.diveSlice_sound
#print axioms LeanFzn.Compiler.compileOpt_optimal_of_bound
#print axioms LeanFzn.Integration.optLoopWith_optimal
#print axioms LeanFzn.Integration.primalBound_optimal

-- Wave 3 (2026-10-31): accepted Core-engine modules.  N5 Clauses, N6
-- generic checker/Bool/Ne, N6b Linear, N7 Queue and N8 Analyze; every
-- exported theorem/lemma is audited under the same allowlist.
#print axioms LeanFzn.Engine.ClauseDB.ensureWatch_size_ge
#print axioms LeanFzn.Engine.ClauseDB.ensureWatch_watchList
#print axioms LeanFzn.Engine.ClauseDB.ensureWatch_mem
#print axioms LeanFzn.Engine.canonLit_lit
#print axioms LeanFzn.Engine.canonLit_fst
#print axioms LeanFzn.Engine.canonLit_table
#print axioms LeanFzn.Engine.canonLit_table_append_only
#print axioms LeanFzn.Engine.canonLit_tableWF
#print axioms LeanFzn.Engine.canonLit_wf
#print axioms LeanFzn.Engine.canonClauseAux_lits
#print axioms LeanFzn.Engine.canonPointwise
#print axioms LeanFzn.Engine.canonClause_fst_lits
#print axioms LeanFzn.Engine.canonClause_table
#print axioms LeanFzn.Engine.canonClause_lits_decode
#print axioms LeanFzn.Engine.canonClause_lits_size
#print axioms LeanFzn.Engine.canonClause_lits
#print axioms LeanFzn.Engine.canonClause_table_append_only
#print axioms LeanFzn.Engine.canonClause_tableWF
#print axioms LeanFzn.Engine.canonClause_wf
#print axioms LeanFzn.Engine.canonClause_entailed
-- S9 (2026-11-02): ownership-preserving canonicalisation twins.
#print axioms LeanFzn.Engine.LitTable.internListFast_eq
#print axioms LeanFzn.Engine.LitTable.internArrayFast_eq
#print axioms LeanFzn.Engine.LitTable.internOneFast_eq
#print axioms LeanFzn.Engine.LitTable.internArray_eq_fast
#print axioms LeanFzn.Engine.canonLitFast_eq
#print axioms LeanFzn.Engine.canonLit_eq_fast
#print axioms LeanFzn.Engine.canonClauseTab_lits
#print axioms LeanFzn.Engine.canonClauseFast_eq
#print axioms LeanFzn.Engine.canonClause_eq_fast
-- S10 (2026-11-02): compact leaf-fit membership twin.
#print axioms LeanFzn.Solver.Propagation.fitsBFast_eq
#print axioms LeanFzn.Solver.Propagation.fitsB_eq_fast
#print axioms LeanFzn.Engine.reasonClause?_none_decision
#print axioms LeanFzn.Engine.reasonClause?_learned
#print axioms LeanFzn.Engine.reasonClause?_reason
#print axioms LeanFzn.Engine.reasonClause?_learned_some
#print axioms LeanFzn.Engine.reasonClause?_entailed
#print axioms LeanFzn.Engine.ClauseDB.Inv.toInvExcept
#print axioms LeanFzn.Engine.ClauseDB.InvExcept.toInv
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_ensureWatch
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_push
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_set_push_self
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watchesAt
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watchesAt_left
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watchesAt_right
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watchedBy
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_clauses
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_live
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_free
#print axioms LeanFzn.Engine.ClauseDB.deletedCount_set_same
#print axioms LeanFzn.Engine.ClauseDB.deletedCount_set_to_live
#print axioms LeanFzn.Engine.ClauseDB.deletedCount_set_to_deleted
#print axioms LeanFzn.Engine.ClauseDB.deletedCount_push_live
#print axioms LeanFzn.Engine.ClauseDB.liveCount_push_live
#print axioms LeanFzn.Engine.ClauseDB.liveCount_set_live
#print axioms LeanFzn.Engine.ClauseDB.liveCount_set_deleted
#print axioms LeanFzn.Engine.ClauseDB.inv_empty
#print axioms LeanFzn.Engine.ClauseDB.invExcept_reuse
#print axioms LeanFzn.Engine.ClauseDB.invExcept_push
#print axioms LeanFzn.Engine.ClauseDB.mem_watchList_iff
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_set_other
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_set_push_old_or_eq
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watchesAt_old_or_eq
#print axioms LeanFzn.Engine.ClauseDB.addWatchPair_watch_lt
#print axioms LeanFzn.Engine.ClauseDB.WatchedBy.mono
#print axioms LeanFzn.Engine.ClauseDB.InvExcept.addWatchPair
#print axioms LeanFzn.Engine.ClauseDB.installWatches_eq_addWatchPair
#print axioms LeanFzn.Engine.ClauseDB.installWatches_eq_self
#print axioms LeanFzn.Engine.ClauseDB.installWatches_inv
#print axioms LeanFzn.Engine.ClauseDB.add_inv
#print axioms LeanFzn.Engine.ClauseDB.Inv.live_pos_of_live
#print axioms LeanFzn.Engine.ClauseDB.delete_live_inv
#print axioms LeanFzn.Engine.ClauseDB.delete_inv
#print axioms LeanFzn.Engine.WPropOut.ofPrunes_prune
#print axioms LeanFzn.Engine.ClauseDB.propagateUnits_fst
#print axioms LeanFzn.Engine.ClauseDB.propagateUnits_inv
#print axioms LeanFzn.Engine.ClauseDB.propagateUnits_conflict
#print axioms LeanFzn.Engine.ClauseDB.propagateUnits_prunes
#print axioms LeanFzn.Engine.ClauseDB.emptyConflict?_spec
#print axioms LeanFzn.Engine.ClauseDB.emptyConflict?_empty
#print axioms LeanFzn.Engine.ClauseDB.ensureWatch_inv
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_inv
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_conflict
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_prunes
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_clauses_e
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_clauses_deleted
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_clauses_size
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_live
#print axioms LeanFzn.Engine.ClauseDB.propagateLiteral_free
#print axioms LeanFzn.Engine.LitTable.decodeClause_map_pLit
#print axioms LeanFzn.Engine.DomC.mem_int_kind
#print axioms LeanFzn.Engine.DomC.mem_bool_kind
#print axioms LeanFzn.Engine.DomC.memIntView_eq_mem_int
#print axioms LeanFzn.Engine.DomC.fixedValue_empty
#print axioms LeanFzn.Engine.DomC.ofDom?_empty
#print axioms LeanFzn.Engine.assignmentOfDoms_getElem?
#print axioms LeanFzn.Engine.posNe_mem_singletonNegLits
#print axioms LeanFzn.Engine.posBool_mem_singletonNegLits
#print axioms LeanFzn.Engine.mem_singletonNegLits_cases
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_of_fixed
#print axioms LeanFzn.Engine.DomC.evalLit_posBool_of_fixed
#print axioms LeanFzn.Engine.propCheckV2With_conflict_entailed
#print axioms LeanFzn.Engine.propCheckV2With_conflict_lits_false
#print axioms LeanFzn.Engine.propCheckV2With_never_prunes
#print axioms LeanFzn.Engine.propCheckV2_noop
#print axioms LeanFzn.Engine.boolClauseLits_entailed
#print axioms LeanFzn.Engine.boolClauseScan_hit_false
#print axioms LeanFzn.Engine.mem_unassigned_iff
#print axioms LeanFzn.Engine.boolClauseScan_count_zero
#print axioms LeanFzn.Engine.boolClauseScan_count_one
#print axioms LeanFzn.Engine.boolClausePropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolClausePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolClausePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolClausePropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolClauseProp_conflict_entailed
#print axioms LeanFzn.Engine.boolClauseProp_prune_reason_entailed
#print axioms LeanFzn.Engine.boolClauseProp_conflict_lits_false
#print axioms LeanFzn.Engine.boolClauseProp_prune_lit_none
#print axioms LeanFzn.Engine.neLit_eval_true_iff_of_mem
#print axioms LeanFzn.Engine.nePropWith_conflict_entailed
#print axioms LeanFzn.Engine.nePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.nePropWith_prune_reason_entailed_symm
#print axioms LeanFzn.Engine.DomC.evalLit_neLit_fixed_false
#print axioms LeanFzn.Engine.DomC.evalLit_neLit_none_of_not_fixed
#print axioms LeanFzn.Engine.DomC.mem_applyLit_neLit
#print axioms LeanFzn.Engine.nePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.nePropWith_prune_lit_none
#print axioms LeanFzn.Engine.nePropWith_prune_lit_none_symm
#print axioms LeanFzn.Engine.nePropWith_mem_prune
#print axioms LeanFzn.Engine.linBoundAt_spec
#print axioms LeanFzn.Engine.linExtractBoundsAux_spec
#print axioms LeanFzn.Engine.linExtractBounds_spec
#print axioms LeanFzn.Engine.linTermsAux_getElem?_some
#print axioms LeanFzn.Engine.linTermsAux_length
#print axioms LeanFzn.Engine.linTerms_length
#print axioms LeanFzn.Engine.linTerms_getElem?_some
#print axioms LeanFzn.Engine.linTotalMin_eq_eraseIdx_add
#print axioms LeanFzn.Engine.linDotSum_eq_eraseIdx_add
#print axioms LeanFzn.Engine.linMinNegLit_false_bound
#print axioms LeanFzn.Engine.linTotalMin_le_linDotSum
#print axioms LeanFzn.Engine.goHoleHi_some_spec3
#print axioms LeanFzn.Engine.DomC.lo?_le_hi?
#print axioms LeanFzn.Engine.slotInt_eq_some_of_getElem!_int
#print axioms LeanFzn.Engine.dotProduct_reads_int_local
#print axioms LeanFzn.Engine.dotProduct_linTermsAux
#print axioms LeanFzn.Engine.dotProduct_eq_linDotSum
#print axioms LeanFzn.Engine.linTerms_slot_mem
#print axioms LeanFzn.Engine.linTermMin_le_value
#print axioms LeanFzn.Engine.linPrunePos_lo_le
#print axioms LeanFzn.Engine.negMulNegSubOne
#print axioms LeanFzn.Engine.linPruneNeg_newLo_le_hi
#print axioms LeanFzn.Engine.linPrunePos_newHi_lt_mul
#print axioms LeanFzn.Engine.linPruneNeg_mul_lt
#print axioms LeanFzn.Engine.linPrunes_mem
#print axioms LeanFzn.Engine.linPrunes_eq_fast
#print axioms LeanFzn.Engine.accepts_satisfiedB
#print axioms LeanFzn.Engine.eval_posLe_some
#print axioms LeanFzn.Engine.eval_negLe_some
#print axioms LeanFzn.Engine.posLe_eval_false_of_not_true
#print axioms LeanFzn.Engine.negLe_eval_false_of_not_true
#print axioms LeanFzn.Engine.linMinNegLit_eval_false_of_not_true
#print axioms LeanFzn.Engine.linMinNegLit_evalLit_false
#print axioms LeanFzn.Engine.evalLit_posLe_none
#print axioms LeanFzn.Engine.evalLit_negLe_none
#print axioms LeanFzn.Engine.ViewWF.dom_wf
#print axioms LeanFzn.Engine.linTerms_mem_bounds
#print axioms LeanFzn.Engine.dot_ge_totalMin
#print axioms LeanFzn.Engine.linConflict_entailed
#print axioms LeanFzn.Engine.linPrunes_sound
#print axioms LeanFzn.Engine.linConflict_lits_evalLit_false
#print axioms LeanFzn.Engine.linPrune_lit_evalLit_none
#print axioms LeanFzn.Engine.atomSlot_linMinNegLit
#print axioms LeanFzn.Engine.linPrune_other_lits_evalLit_false
#print axioms LeanFzn.Engine.linPrunesWith_mem
#print axioms LeanFzn.Engine.linLeMatches_spec
#print axioms LeanFzn.Engine.linLeHmemOfFind
#print axioms LeanFzn.Engine.linLeProp_run_conflict
#print axioms LeanFzn.Engine.linLeProp_run_prune
#print axioms LeanFzn.Engine.linLeProp_conflict_entailed
#print axioms LeanFzn.Engine.linLeProp_conflict_lits_false
#print axioms LeanFzn.Engine.linLeProp_prune_reason_entailed
#print axioms LeanFzn.Engine.linLeProp_prune_lit_none
#print axioms LeanFzn.Engine.linLeProp_run_fix_of_size_ne
#print axioms LeanFzn.Engine.linLePropWith_run_conflict
#print axioms LeanFzn.Engine.linLePropWith_run_prune
#print axioms LeanFzn.Engine.linLePropWith_conflict_entailed
#print axioms LeanFzn.Engine.linLePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linLePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linLePropWith_prune_lit_none
#print axioms LeanFzn.Engine.linLePropWith_run_fix_of_size_ne
#print axioms LeanFzn.Engine.domAfter_zero
#print axioms LeanFzn.Engine.domAfter_succ
#print axioms LeanFzn.Engine.domStep_congr
#print axioms LeanFzn.Engine.domAfter_congr
#print axioms LeanFzn.Engine.list_foldl_congr
#print axioms LeanFzn.Engine.mem_extract_zero_getD
#print axioms LeanFzn.Engine.domAfter_congr_extract
#print axioms LeanFzn.Engine.domAfter_congr_state
#print axioms LeanFzn.Engine.TrailInv.getD_changeList_lt
#print axioms LeanFzn.Engine.domAfter_trailPush_self_lt
#print axioms LeanFzn.Engine.domAfter_trailPush_ne
#print axioms LeanFzn.Engine.getD_congr_getElem?
#print axioms LeanFzn.Engine.SlotHistory.congr
#print axioms LeanFzn.Engine.canonLit_doms
#print axioms LeanFzn.Engine.canonLit_trail
#print axioms LeanFzn.Engine.canonLit_changeList
#print axioms LeanFzn.Engine.canonClause_doms
#print axioms LeanFzn.Engine.canonClause_trail
#print axioms LeanFzn.Engine.canonClause_changeList
#print axioms LeanFzn.Engine.ensureInQueue_doms
#print axioms LeanFzn.Engine.ensureInQueue_trail
#print axioms LeanFzn.Engine.ensureInQueue_changeIndex
#print axioms LeanFzn.Engine.setInQueue_doms
#print axioms LeanFzn.Engine.setInQueue_trail
#print axioms LeanFzn.Engine.setInQueue_changeIndex
#print axioms LeanFzn.Engine.enqueueProp_doms
#print axioms LeanFzn.Engine.enqueueProp_trail
#print axioms LeanFzn.Engine.enqueueProp_changeIndex
#print axioms LeanFzn.Engine.list_foldl_doms
#print axioms LeanFzn.Engine.list_foldl_trail
#print axioms LeanFzn.Engine.list_foldl_changeIndex
#print axioms LeanFzn.Engine.enqueueSubs_doms
#print axioms LeanFzn.Engine.enqueueSubs_trail
#print axioms LeanFzn.Engine.enqueueSubs_changeIndex
#print axioms LeanFzn.Engine.emitSlot_doms
#print axioms LeanFzn.Engine.emitSlot_trail
#print axioms LeanFzn.Engine.emitSlot_changeIndex
#print axioms LeanFzn.Engine.emitSlot_changeList
#print axioms LeanFzn.Engine.slotHistory_init
#print axioms LeanFzn.Engine.slotHistory_trailPush
#print axioms LeanFzn.Engine.test_set!
#print axioms LeanFzn.Engine.Array.set!_eq_setGrow_of_lt
#print axioms LeanFzn.Engine.DomC.empty_applyLit_isEmpty
#print axioms LeanFzn.Engine.TrailInv.congr
#print axioms LeanFzn.Engine.insertPending_slotHistory
#print axioms LeanFzn.Engine.Array.size_filter_le
#print axioms LeanFzn.Engine.List.filter_lt_spec
#print axioms LeanFzn.Engine.SortedList.filter_eq_extract
#print axioms LeanFzn.Engine.SortedList.filter_getD_lt
#print axioms LeanFzn.Engine.SortedList.filter_getD_ge
#print axioms LeanFzn.Engine.undoFuel_doms_empty_of_none
#print axioms LeanFzn.Engine.backjump_doms_of_none_empty
#print axioms LeanFzn.Engine.backjump_changeList_eq_extract
#print axioms LeanFzn.Engine.domAfter_backjump_eq_of_lt
#print axioms LeanFzn.Engine.backjump_slotHistory
#print axioms LeanFzn.Engine.DomC.empty_WF
#print axioms LeanFzn.Engine.Array.set!_eq_self_of_ge
#print axioms LeanFzn.Engine.DomsWF.congr
#print axioms LeanFzn.Engine.DomsWF.setGrow
#print axioms LeanFzn.Engine.DomsWF.set!_of_lt
#print axioms LeanFzn.Engine.DomsWF.set!
#print axioms LeanFzn.Engine.insertPending_domsWF
#print axioms LeanFzn.Engine.ensureInQueue_levelStart
#print axioms LeanFzn.Engine.ensureInQueue_level
#print axioms LeanFzn.Engine.setInQueue_levelStart
#print axioms LeanFzn.Engine.setInQueue_level
#print axioms LeanFzn.Engine.enqueueProp_levelStart
#print axioms LeanFzn.Engine.enqueueProp_level
#print axioms LeanFzn.Engine.list_foldl_levelStart
#print axioms LeanFzn.Engine.list_foldl_level
#print axioms LeanFzn.Engine.enqueueSubs_levelStart
#print axioms LeanFzn.Engine.enqueueSubs_level
#print axioms LeanFzn.Engine.emitSlot_levelStart
#print axioms LeanFzn.Engine.emitSlot_level
#print axioms LeanFzn.Engine.insertPending_trailInv
#print axioms LeanFzn.Engine.List.foldl_domStep_WF
#print axioms LeanFzn.Engine.domAfter_WF
#print axioms LeanFzn.Engine.initWF_of_InitInv
#print axioms LeanFzn.Engine.slotHistory_domsWF
#print axioms LeanFzn.Engine.HistInv.congr
#print axioms LeanFzn.Engine.insertPending_histInv
#print axioms LeanFzn.Engine.canonLit_histInv
#print axioms LeanFzn.Engine.canonClause_histInv
#print axioms LeanFzn.Engine.setInQueue_histInv
#print axioms LeanFzn.Engine.pushPropPrunes_histInv
#print axioms LeanFzn.Engine.drain_histInv
#print axioms LeanFzn.Engine.drain_slotHistory
#print axioms LeanFzn.Engine.drain_trailInv
#print axioms LeanFzn.Engine.propagate_slotHistory
#print axioms LeanFzn.Engine.propagate_trailInv
#print axioms LeanFzn.Engine.trail_entry_prev_WF
#print axioms LeanFzn.Engine.undoFuel_domsWF_aux
#print axioms LeanFzn.Engine.undoFuel_domsWF
#print axioms LeanFzn.Engine.backjump_domsWF
#print axioms LeanFzn.Engine.Good.congr
#print axioms LeanFzn.Engine.insertPending_good
#print axioms LeanFzn.Engine.pushPropPrunes_good
#print axioms LeanFzn.Engine.pushClausePrunes_good
#print axioms LeanFzn.Engine.canonLit_good
#print axioms LeanFzn.Engine.canonClause_good
#print axioms LeanFzn.Engine.setInQueue_good
#print axioms LeanFzn.Engine.drain_good
#print axioms LeanFzn.Engine.drain_slotHistory_good
#print axioms LeanFzn.Engine.drain_trailInv_good
#print axioms LeanFzn.Engine.drain_domsWF
#print axioms LeanFzn.Engine.propagate_slotHistory_good
#print axioms LeanFzn.Engine.propagate_trailInv_good
#print axioms LeanFzn.Engine.propagate_domsWF
#print axioms LeanFzn.Engine.list_foldl_props
#print axioms LeanFzn.Engine.list_foldl_subs
#print axioms LeanFzn.Engine.list_foldl_reasons
#print axioms LeanFzn.Engine.list_foldl_db
#print axioms LeanFzn.Engine.list_foldl_table
#print axioms LeanFzn.Engine.list_foldl_queueHigh
#print axioms LeanFzn.Engine.list_foldl_queueLow
#print axioms LeanFzn.Engine.list_foldl_inQueue
#print axioms LeanFzn.Engine.list_foldl_activity
#print axioms LeanFzn.Engine.list_foldl_activityHeap
#print axioms LeanFzn.Engine.list_foldl_phases
#print axioms LeanFzn.Engine.list_foldl_restarts
#print axioms LeanFzn.Engine.list_foldl_stats
#print axioms LeanFzn.Engine.canonLit_props
#print axioms LeanFzn.Engine.canonLit_subs
#print axioms LeanFzn.Engine.canonLit_reasons
#print axioms LeanFzn.Engine.canonLit_db
#print axioms LeanFzn.Engine.canonLit_level
#print axioms LeanFzn.Engine.canonLit_levelStart
#print axioms LeanFzn.Engine.canonLit_queueHigh
#print axioms LeanFzn.Engine.canonLit_queueLow
#print axioms LeanFzn.Engine.canonLit_inQueue
#print axioms LeanFzn.Engine.canonLit_activity
#print axioms LeanFzn.Engine.canonLit_activityHeap
#print axioms LeanFzn.Engine.canonLit_phases
#print axioms LeanFzn.Engine.canonLit_restarts
#print axioms LeanFzn.Engine.canonLit_stats
#print axioms LeanFzn.Engine.canonLit_changeIndex
#print axioms LeanFzn.Engine.canonClause_props
#print axioms LeanFzn.Engine.canonClause_subs
#print axioms LeanFzn.Engine.canonClause_reasons
#print axioms LeanFzn.Engine.canonClause_db
#print axioms LeanFzn.Engine.canonClause_level
#print axioms LeanFzn.Engine.canonClause_levelStart
#print axioms LeanFzn.Engine.canonClause_queueHigh
#print axioms LeanFzn.Engine.canonClause_queueLow
#print axioms LeanFzn.Engine.canonClause_inQueue
#print axioms LeanFzn.Engine.canonClause_activity
#print axioms LeanFzn.Engine.canonClause_activityHeap
#print axioms LeanFzn.Engine.canonClause_phases
#print axioms LeanFzn.Engine.canonClause_restarts
#print axioms LeanFzn.Engine.canonClause_stats
#print axioms LeanFzn.Engine.canonClause_changeIndex
#print axioms LeanFzn.Engine.ensureSubs_props
#print axioms LeanFzn.Engine.ensureSubs_reasons
#print axioms LeanFzn.Engine.ensureSubs_db
#print axioms LeanFzn.Engine.ensureSubs_table
#print axioms LeanFzn.Engine.ensureSubs_level
#print axioms LeanFzn.Engine.ensureSubs_levelStart
#print axioms LeanFzn.Engine.ensureSubs_queueHigh
#print axioms LeanFzn.Engine.ensureSubs_queueLow
#print axioms LeanFzn.Engine.ensureSubs_inQueue
#print axioms LeanFzn.Engine.ensureSubs_activity
#print axioms LeanFzn.Engine.ensureSubs_activityHeap
#print axioms LeanFzn.Engine.ensureSubs_phases
#print axioms LeanFzn.Engine.ensureSubs_restarts
#print axioms LeanFzn.Engine.ensureSubs_stats
#print axioms LeanFzn.Engine.ensureSubs_doms
#print axioms LeanFzn.Engine.ensureSubs_trail
#print axioms LeanFzn.Engine.ensureSubs_changeIndex
#print axioms LeanFzn.Engine.ensureInQueue_props
#print axioms LeanFzn.Engine.ensureInQueue_subs
#print axioms LeanFzn.Engine.ensureInQueue_reasons
#print axioms LeanFzn.Engine.ensureInQueue_db
#print axioms LeanFzn.Engine.ensureInQueue_table
#print axioms LeanFzn.Engine.ensureInQueue_queueHigh
#print axioms LeanFzn.Engine.ensureInQueue_queueLow
#print axioms LeanFzn.Engine.ensureInQueue_activity
#print axioms LeanFzn.Engine.ensureInQueue_activityHeap
#print axioms LeanFzn.Engine.ensureInQueue_phases
#print axioms LeanFzn.Engine.ensureInQueue_restarts
#print axioms LeanFzn.Engine.ensureInQueue_stats
#print axioms LeanFzn.Engine.setInQueue_props
#print axioms LeanFzn.Engine.setInQueue_subs
#print axioms LeanFzn.Engine.setInQueue_reasons
#print axioms LeanFzn.Engine.setInQueue_db
#print axioms LeanFzn.Engine.setInQueue_table
#print axioms LeanFzn.Engine.setInQueue_queueHigh
#print axioms LeanFzn.Engine.setInQueue_queueLow
#print axioms LeanFzn.Engine.setInQueue_activity
#print axioms LeanFzn.Engine.setInQueue_activityHeap
#print axioms LeanFzn.Engine.setInQueue_phases
#print axioms LeanFzn.Engine.setInQueue_restarts
#print axioms LeanFzn.Engine.setInQueue_stats
#print axioms LeanFzn.Engine.enqueueProp_props
#print axioms LeanFzn.Engine.enqueueProp_subs
#print axioms LeanFzn.Engine.enqueueProp_reasons
#print axioms LeanFzn.Engine.enqueueProp_db
#print axioms LeanFzn.Engine.enqueueProp_table
#print axioms LeanFzn.Engine.enqueueProp_activity
#print axioms LeanFzn.Engine.enqueueProp_activityHeap
#print axioms LeanFzn.Engine.enqueueProp_phases
#print axioms LeanFzn.Engine.enqueueProp_restarts
#print axioms LeanFzn.Engine.enqueueProp_stats
#print axioms LeanFzn.Engine.enqueueSubs_props
#print axioms LeanFzn.Engine.enqueueSubs_subs
#print axioms LeanFzn.Engine.enqueueSubs_reasons
#print axioms LeanFzn.Engine.enqueueSubs_db
#print axioms LeanFzn.Engine.enqueueSubs_table
#print axioms LeanFzn.Engine.enqueueSubs_activity
#print axioms LeanFzn.Engine.enqueueSubs_activityHeap
#print axioms LeanFzn.Engine.enqueueSubs_phases
#print axioms LeanFzn.Engine.enqueueSubs_restarts
#print axioms LeanFzn.Engine.enqueueSubs_stats
#print axioms LeanFzn.Engine.emitSlot_props
#print axioms LeanFzn.Engine.emitSlot_subs
#print axioms LeanFzn.Engine.emitSlot_reasons
#print axioms LeanFzn.Engine.emitSlot_db
#print axioms LeanFzn.Engine.emitSlot_table
#print axioms LeanFzn.Engine.emitSlot_activity
#print axioms LeanFzn.Engine.emitSlot_activityHeap
#print axioms LeanFzn.Engine.emitSlot_phases
#print axioms LeanFzn.Engine.emitSlot_restarts
#print axioms LeanFzn.Engine.emitSlot_stats
#print axioms LeanFzn.Engine.trailPush_props
#print axioms LeanFzn.Engine.setGrow_push_eq
#print axioms LeanFzn.Engine.trailPush_eq_fast
#print axioms LeanFzn.Engine.backjump_eq_fast
#print axioms LeanFzn.Engine.trailPush_subs
#print axioms LeanFzn.Engine.trailPush_db
#print axioms LeanFzn.Engine.trailPush_table
#print axioms LeanFzn.Engine.trailPush_queueHigh
#print axioms LeanFzn.Engine.trailPush_queueLow
#print axioms LeanFzn.Engine.trailPush_inQueue
#print axioms LeanFzn.Engine.trailPush_activity
#print axioms LeanFzn.Engine.trailPush_activityHeap
#print axioms LeanFzn.Engine.trailPush_phases
#print axioms LeanFzn.Engine.trailPush_restarts
#print axioms LeanFzn.Engine.trailPush_stats
#print axioms LeanFzn.Engine.insertPending_reasons
#print axioms LeanFzn.Engine.insertPending_props
#print axioms LeanFzn.Engine.insertPending_subs
#print axioms LeanFzn.Engine.insertPending_level
#print axioms LeanFzn.Engine.insertPending_levelStart
#print axioms LeanFzn.Engine.insertPending_db
#print axioms LeanFzn.Engine.insertPending_table_append_only
#print axioms LeanFzn.Engine.insertPending_tableWF
#print axioms LeanFzn.Engine.insertPending_trail_push
#print axioms LeanFzn.Engine.insertPending_trail_doms
#print axioms LeanFzn.Engine.insertPending_failed
#print axioms LeanFzn.Engine.insertPending_conflict
#print axioms LeanFzn.Engine.insertPending_true_state
#print axioms LeanFzn.Engine.insertPending_conflict_state
#print axioms LeanFzn.Engine.insertPending_failed_state
#print axioms LeanFzn.Engine.pushPropPrunes_eq
#print axioms LeanFzn.Engine.PropStepOK.trans
#print axioms LeanFzn.Engine.list_foldl_propOK
#print axioms LeanFzn.Engine.Array.getElem?_push_of_getElem?
#print axioms LeanFzn.Engine.pushPropStep_ok
#print axioms LeanFzn.Engine.pushPropPrunesOK
#print axioms LeanFzn.Engine.pushPropPrunes_reasons_prefix
#print axioms LeanFzn.Engine.pushPropPrunes_pending_prefix
#print axioms LeanFzn.Engine.pushPropPrunes_pending_spec
#print axioms LeanFzn.Engine.pushPropPrunes_pending_reason_resolves
#print axioms LeanFzn.Engine.pushClausePrunes_eq
#print axioms LeanFzn.Engine.list_foldl_push_prefix
#print axioms LeanFzn.Engine.pushClausePrunes_prefix
#print axioms LeanFzn.Engine.pushClausePrunes_mem
#print axioms LeanFzn.Engine.drain_fuel_zero
#print axioms LeanFzn.Engine.propagate_fuel_zero
#print axioms LeanFzn.Engine.drain_fixpoint
#print axioms LeanFzn.Engine.propagate_fixpoint
#print axioms LeanFzn.Engine.Frame.refl
#print axioms LeanFzn.Engine.Frame.trans
#print axioms LeanFzn.Engine.Frame.congr
#print axioms LeanFzn.Engine.frame_canonLit
#print axioms LeanFzn.Engine.frame_canonClause
#print axioms LeanFzn.Engine.frame_trailPush
#print axioms LeanFzn.Engine.frame_emitSlot
#print axioms LeanFzn.Engine.frame_setInQueue
#print axioms LeanFzn.Engine.frame_domsStats
#print axioms LeanFzn.Engine.frame_reasonsPush
#print axioms LeanFzn.Engine.frame_queueHighPop
#print axioms LeanFzn.Engine.frame_queueLowPop
#print axioms LeanFzn.Engine.frame_propagateLiteral
#print axioms LeanFzn.Engine.frame_insertPending
#print axioms LeanFzn.Engine.pushPropStep_frame
#print axioms LeanFzn.Engine.pushPropStep_failed
#print axioms LeanFzn.Engine.list_foldl_frame
#print axioms LeanFzn.Engine.frame_pushPropPrunes
#print axioms LeanFzn.Engine.drain_frame
#print axioms LeanFzn.Engine.drain_props
#print axioms LeanFzn.Engine.drain_subs
#print axioms LeanFzn.Engine.drain_level
#print axioms LeanFzn.Engine.drain_levelStart
#print axioms LeanFzn.Engine.drain_table_prefix
#print axioms LeanFzn.Engine.drain_tableWF
#print axioms LeanFzn.Engine.drain_reasons_prefix
#print axioms LeanFzn.Engine.drain_trail_prefix
#print axioms LeanFzn.Engine.drain_db_e
#print axioms LeanFzn.Engine.drain_db_size
#print axioms LeanFzn.Engine.drain_db_inv
#print axioms LeanFzn.Engine.propagate_props_subs
#print axioms LeanFzn.Engine.propagate_table
#print axioms LeanFzn.Engine.propagate_tableWF
#print axioms LeanFzn.Engine.propagate_reasons
#print axioms LeanFzn.Engine.pushPropPrunes_reasons_entailed
#print axioms LeanFzn.Engine.insertPending_reasons_entailed
#print axioms LeanFzn.Engine.drain_reasons_entailed
#print axioms LeanFzn.Engine.propagate_reasons_entailed
#print axioms LeanFzn.Engine.propagate_trail
#print axioms LeanFzn.Engine.propagate_db
#print axioms LeanFzn.Engine.drain_failed
#print axioms LeanFzn.Engine.propagate_failed
#print axioms LeanFzn.Engine.drain_conflict_entailed
#print axioms LeanFzn.Engine.propagate_conflict
#print axioms LeanFzn.Engine.pushClausePrunes_reason_resolves
#print axioms LeanFzn.Engine.findExplainList_spec
#print axioms LeanFzn.Engine.explainLit_lit
#print axioms LeanFzn.Engine.findExplainList_some_of_mem_false
#print axioms LeanFzn.Engine.findExplainList_none_iff
#print axioms LeanFzn.Engine.explainLit_spec
#print axioms LeanFzn.Engine.explainLit_none_iff
#print axioms LeanFzn.Engine.DomC.fixedValue_bool_eq_none_of_ne_bool
#print axioms LeanFzn.Engine.DomC.evalLit_boolEq_eq_none_of_nonbool
#print axioms LeanFzn.Engine.Atom.evalAtValue_ne_none_of_mem_evalLit_false
#print axioms LeanFzn.Engine.Literal.valueHolds_negate_of_ne_none
#print axioms LeanFzn.Engine.Literal.valueHolds_negate_eq_true_iff
#print axioms LeanFzn.Engine.addCItem_mem_lit_iff
#print axioms LeanFzn.Engine.addCItem_mem_lit
#print axioms LeanFzn.Engine.addCItem_mem
#print axioms LeanFzn.Engine.addCItem_explained
#print axioms LeanFzn.Engine.addCItem_false
#print axioms LeanFzn.Engine.initSlotOKB_spec
#print axioms LeanFzn.Engine.domFalseB_spec
#print axioms LeanFzn.Engine.itemCheckB_spec
#print axioms LeanFzn.Engine.atomKindOKB_spec
#print axioms LeanFzn.Engine.slotKindOKB_spec
#print axioms LeanFzn.Engine.slotObsB_spec
#print axioms LeanFzn.Engine.sortedB_spec
#print axioms LeanFzn.Engine.subsumeItems_subset
#print axioms LeanFzn.Engine.subsumeStep_entailed
#print axioms LeanFzn.Engine.subsumeItems_entailed
#print axioms LeanFzn.Engine.mem_chainReasonLits
#print axioms LeanFzn.Engine.atomSlot_eq_slot
#print axioms LeanFzn.Engine.mem_allAssigns_getElem_mem
#print axioms LeanFzn.Engine.chainReasonLits_entailed_of_cert
#print axioms LeanFzn.Engine.chainReasonLits_entailed
#print axioms LeanFzn.Engine.Entailed_of_mem_subset
#print axioms LeanFzn.Engine.Entailed_of_perm
#print axioms LeanFzn.Engine.removeLitItems_mem
#print axioms LeanFzn.Engine.removeLitItems_lits
#print axioms LeanFzn.Engine.itemOKB_spec
#print axioms LeanFzn.Engine.initialItems_lit_mem
#print axioms LeanFzn.Engine.initialItems_explained
#print axioms LeanFzn.Engine.initialItems_false
#print axioms LeanFzn.Engine.initialItems_entailed
#print axioms LeanFzn.Engine.initialItems_inv
#print axioms LeanFzn.Engine.litSlotOKB_spec
#print axioms LeanFzn.Engine.chainCertCheckB_spec
#print axioms LeanFzn.Engine.mem_of_any_litEqB
#print axioms LeanFzn.Engine.addReasonLits_lits_eq
#print axioms LeanFzn.Engine.eClause_entailed_lits
#print axioms LeanFzn.Engine.addReasonLits_explained
#print axioms LeanFzn.Engine.addReasonLits_false
#print axioms LeanFzn.Engine.removeLitItems_explained
#print axioms LeanFzn.Engine.removeLitItems_false
#print axioms LeanFzn.Engine.resolveWith_lits_eq
#print axioms LeanFzn.Engine.exactReason_some_any
#print axioms LeanFzn.Engine.chainCert_of_resolveWith_ok_none
#print axioms LeanFzn.Engine.resolveWith_entailed
#print axioms LeanFzn.Engine.resolveWith_explained
#print axioms LeanFzn.Engine.resolveWith_false
#print axioms LeanFzn.Engine.resolveWith_inv
#print axioms LeanFzn.Engine.entailed_of_entailed_cons_initial
#print axioms LeanFzn.Engine.initialDomain_neg_entailed
#print axioms LeanFzn.Engine.eraseCItemAt_toList
#print axioms LeanFzn.Engine.perm_getElem_cons_eraseIdx
#print axioms LeanFzn.Engine.perm_getElem?_cons_eraseIdx
#print axioms LeanFzn.Engine.finishOrder_perm
#print axioms LeanFzn.Engine.maxStep_spec
#print axioms LeanFzn.Engine.maxCurrentIdx_spec
#print axioms LeanFzn.Engine.AnalysisSpec.sound_ok
#print axioms LeanFzn.Engine.failAnalysis_spec
#print axioms LeanFzn.Engine.toList_eq_cons_tail_of_getElem?_zero
#print axioms LeanFzn.Engine.eraseCItemAt_zero_toList
#print axioms LeanFzn.Engine.mem_of_getElem?_zero
#print axioms LeanFzn.Engine.eraseCItemAt_zero_inv
#print axioms LeanFzn.Engine.sentinel_unit
#print axioms LeanFzn.Engine.chain_entailed_of_item
#print axioms LeanFzn.Engine.mem_ofLiterals_lits_iff
#print axioms LeanFzn.Engine.mem_finishOrder_of_getElem?
#print axioms LeanFzn.Engine.finishAnalysis_spec
#print axioms LeanFzn.Engine.finishAnalysis_backjump_lt
#print axioms LeanFzn.Engine.analyze_of_initialItems_none
#print axioms LeanFzn.Engine.analyze_of_initialItems_some
#print axioms LeanFzn.Engine.analyze_sound
#print axioms LeanFzn.Engine.analyze_learned_none_of_not_ok
#print axioms LeanFzn.Engine.analyze_no_claim_on_failure
#print axioms LeanFzn.Engine.analyze_ok_learned
#print axioms LeanFzn.Engine.analyze_empty_unsat
#print axioms LeanFzn.Engine.analyze_asserting_mem
#print axioms LeanFzn.Engine.analyze_learned_lits_false

-- N9: the certified Core search loop (`Engine/Search.lean`), its public
-- seam (`Integration/CoreSolve.lean`), and the source route
-- (`Integration/CertifiedSolve.lean`).  Every result must depend only on
-- the three standard axioms.
#print axioms LeanFzn.Engine.convertDomainsAux_spec
#print axioms LeanFzn.Engine.convertDomains_spec
#print axioms LeanFzn.Engine.slotReadyB_spec
#print axioms LeanFzn.Engine.initReady_spec
#print axioms LeanFzn.Engine.initInv_of_convertDomains
#print axioms LeanFzn.Engine.seedEntailed
#print axioms LeanFzn.Engine.search_sat
#print axioms LeanFzn.Engine.search_unsat
#print axioms LeanFzn.Engine.emptyConflict_entailed
#print axioms LeanFzn.Engine.addSeedClauses_empty_entailed
#print axioms LeanFzn.Engine.coreSolveFull_fst
#print axioms LeanFzn.Engine.seedPhases_none
#print axioms LeanFzn.Engine.seedPhases_some
#print axioms LeanFzn.Engine.coreSolveFullWith_sat
#print axioms LeanFzn.Engine.coreSolveFullWith_unsat
#print axioms LeanFzn.Engine.coreSolveFull_sat
#print axioms LeanFzn.Engine.coreSolveFull_unsat
#print axioms LeanFzn.Engine.coreSolve_sat
#print axioms LeanFzn.Engine.coreSolve_unsat
#print axioms LeanFzn.Engine.coreSolveWith_sat
#print axioms LeanFzn.Engine.coreSolveWith_unsat
#print axioms LeanFzn.Integration.solveSearchConfigCore_sat
#print axioms LeanFzn.Integration.solveSearchConfigCore_unsat
#print axioms LeanFzn.Integration.solveSearchConfigCore_total
#print axioms LeanFzn.Integration.solveSearchConfigCoreFull_fst
#print axioms LeanFzn.Integration.solveCertifiedCoreStats_fst
#print axioms LeanFzn.Integration.solveCertifiedCore_sat_correct
#print axioms LeanFzn.Integration.solveCertifiedCore_unsat_correct

-- N10c: dedicated arithmetic propagators (`Engine/Props/Arith.lean`).
#print axioms LeanFzn.Engine.loLit_eval_false
#print axioms LeanFzn.Engine.hiLit_eval_false
#print axioms LeanFzn.Engine.le_of_loLit_not_true
#print axioms LeanFzn.Engine.le_of_hiLit_not_true
#print axioms LeanFzn.Engine.argBounds?_lit
#print axioms LeanFzn.Engine.argBounds?_slot
#print axioms LeanFzn.Engine.mkGArg?_bounds
#print axioms LeanFzn.Engine.mkGArg?_curSpec
#print axioms LeanFzn.Engine.mkGArg?_arg
#print axioms LeanFzn.Engine.mkGBox?_bounds
#print axioms LeanFzn.Engine.mkGBox?_curSpec
#print axioms LeanFzn.Engine.mkGBox?_arg0
#print axioms LeanFzn.Engine.mkGBox?_arg1
#print axioms LeanFzn.Engine.mkGBox?_arg2
#print axioms LeanFzn.Engine.mkGBox?_wf
#print axioms LeanFzn.Engine.GArg.cur_of_lits_not_true
#print axioms LeanFzn.Engine.GArg.lits_eval_false
#print axioms LeanFzn.Engine.GBox.lits_eval_false
#print axioms LeanFzn.Engine.GBox.cur_of_lits_not_true
#print axioms LeanFzn.Engine.GBox.conflict_lits_false
#print axioms LeanFzn.Engine.GBox.emptyNew_spec
#print axioms LeanFzn.Engine.GBox.emptyNew_false
#print axioms LeanFzn.Engine.GBox.out_conflict
#print axioms LeanFzn.Engine.GBox.out_prune
#print axioms LeanFzn.Engine.GBox.conflict_entailed
#print axioms LeanFzn.Engine.GArg.prune_lit_true
#print axioms LeanFzn.Engine.GArg.mem_prunes
#print axioms LeanFzn.Engine.GArg.prune_reason_satisfied
#print axioms LeanFzn.Engine.GBox.prune_reason_entailed
#print axioms LeanFzn.Engine.GBox.prune_lit_none
#print axioms LeanFzn.Engine.GArg.intersect_sub
#print axioms LeanFzn.Engine.GArg.curSpec_intersect
#print axioms LeanFzn.Engine.GArg.boundSpec_intersect
#print axioms LeanFzn.Engine.GArg.wf_intersect
#print axioms LeanFzn.Engine.GStep.apply_curSpec
#print axioms LeanFzn.Engine.GStep.apply_boundSpec
#print axioms LeanFzn.Engine.GStep.apply_wf
#print axioms LeanFzn.Engine.GStep.apply_sub
#print axioms LeanFzn.Engine.mkPruneArray_mem
#print axioms LeanFzn.Engine.GBox.toPropWith_run_conflict
#print axioms LeanFzn.Engine.GBox.toPropWith_run_prune
#print axioms LeanFzn.Engine.rel3PropWith_run_fix_of_none
#print axioms LeanFzn.Engine.rel3PropWith_run_conflict
#print axioms LeanFzn.Engine.rel3PropWith_run_prune
#print axioms LeanFzn.Engine.rel3PropWith_conflict_entailed
#print axioms LeanFzn.Engine.rel3PropWith_conflict_lits_false
#print axioms LeanFzn.Engine.rel3PropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.rel3PropWith_prune_lit_none
#print axioms LeanFzn.Engine.plusStep_spec
#print axioms LeanFzn.Engine.minStep_spec
#print axioms LeanFzn.Engine.maxStep3_spec
#print axioms LeanFzn.Engine.absStep_spec
#print axioms LeanFzn.Engine.read_slot_int_of_getElem?
#print axioms LeanFzn.Engine.plus_bridge
#print axioms LeanFzn.Engine.min_bridge
#print axioms LeanFzn.Engine.max_bridge
#print axioms LeanFzn.Engine.abs_bridge
#print axioms LeanFzn.Engine.minPair_bridge
#print axioms LeanFzn.Engine.maxPair_bridge
#print axioms LeanFzn.Engine.plusPropWith_run_conflict
#print axioms LeanFzn.Engine.plusPropWith_run_prune
#print axioms LeanFzn.Engine.plusPropWith_conflict_entailed
#print axioms LeanFzn.Engine.plusPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.plusPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.plusPropWith_prune_lit_none
#print axioms LeanFzn.Engine.plusPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.minPropWith_run_conflict
#print axioms LeanFzn.Engine.minPropWith_run_prune
#print axioms LeanFzn.Engine.minPropWith_conflict_entailed
#print axioms LeanFzn.Engine.minPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.minPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.minPropWith_prune_lit_none
#print axioms LeanFzn.Engine.minPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.maxPropWith_run_conflict
#print axioms LeanFzn.Engine.maxPropWith_run_prune
#print axioms LeanFzn.Engine.maxPropWith_conflict_entailed
#print axioms LeanFzn.Engine.maxPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.maxPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.maxPropWith_prune_lit_none
#print axioms LeanFzn.Engine.maxPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.absPropWith_run_conflict
#print axioms LeanFzn.Engine.absPropWith_run_prune
#print axioms LeanFzn.Engine.absPropWith_conflict_entailed
#print axioms LeanFzn.Engine.absPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.absPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.absPropWith_prune_lit_none
#print axioms LeanFzn.Engine.absPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.minPairPropWith_run_conflict
#print axioms LeanFzn.Engine.minPairPropWith_run_prune
#print axioms LeanFzn.Engine.minPairPropWith_conflict_entailed
#print axioms LeanFzn.Engine.minPairPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.minPairPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.minPairPropWith_prune_lit_none
#print axioms LeanFzn.Engine.minPairPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.maxPairPropWith_run_conflict
#print axioms LeanFzn.Engine.maxPairPropWith_run_prune
#print axioms LeanFzn.Engine.maxPairPropWith_conflict_entailed
#print axioms LeanFzn.Engine.maxPairPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.maxPairPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.maxPairPropWith_prune_lit_none
#print axioms LeanFzn.Engine.maxPairPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.timesStep_spec
#print axioms LeanFzn.Engine.timesPropWith_run_conflict
#print axioms LeanFzn.Engine.timesPropWith_run_prune
#print axioms LeanFzn.Engine.timesPropWith_conflict_entailed
#print axioms LeanFzn.Engine.timesPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.timesPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.timesPropWith_prune_lit_none
#print axioms LeanFzn.Engine.timesPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.divNorm_spec
#print axioms LeanFzn.Engine.divStep_spec
#print axioms LeanFzn.Engine.modStep_spec
#print axioms LeanFzn.Engine.divPropWith_run_conflict
#print axioms LeanFzn.Engine.divPropWith_run_prune
#print axioms LeanFzn.Engine.divPropWith_conflict_entailed
#print axioms LeanFzn.Engine.divPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.divPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.divPropWith_prune_lit_none
#print axioms LeanFzn.Engine.divPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.modPropWith_run_conflict
#print axioms LeanFzn.Engine.modPropWith_run_prune
#print axioms LeanFzn.Engine.modPropWith_conflict_entailed
#print axioms LeanFzn.Engine.modPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.modPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.modPropWith_prune_lit_none
#print axioms LeanFzn.Engine.modPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.map_read_constList?
#print axioms LeanFzn.Engine.minGen_const_force
#print axioms LeanFzn.Engine.maxGen_const_force
#print axioms LeanFzn.Engine.minGen_empty_unsat
#print axioms LeanFzn.Engine.maxGen_empty_unsat
#print axioms LeanFzn.Engine.eqLitStep_spec
#print axioms LeanFzn.Engine.emptyStep_spec
#print axioms LeanFzn.Engine.forcedValuePropWith_run_conflict
#print axioms LeanFzn.Engine.forcedValuePropWith_run_prune
#print axioms LeanFzn.Engine.forcedValuePropWith_conflict_entailed
#print axioms LeanFzn.Engine.forcedValuePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.forcedValuePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.forcedValuePropWith_prune_lit_none
#print axioms LeanFzn.Engine.forcedValuePropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.emptyGenPropWith_run_conflict
#print axioms LeanFzn.Engine.emptyGenPropWith_run_prune
#print axioms LeanFzn.Engine.emptyGenPropWith_conflict_entailed
#print axioms LeanFzn.Engine.emptyGenPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.emptyGenPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.emptyGenPropWith_prune_lit_none
#print axioms LeanFzn.Engine.emptyGenPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.minGen_slots_mem
#print axioms LeanFzn.Engine.maxGen_slots_mem
#print axioms LeanFzn.Engine.minGenPropWith_nil
#print axioms LeanFzn.Engine.maxGenPropWith_nil
#print axioms LeanFzn.Engine.minGenPropWith_cons_some
#print axioms LeanFzn.Engine.maxGenPropWith_cons_some
#print axioms LeanFzn.Engine.minGenPropWith_cons_none
#print axioms LeanFzn.Engine.maxGenPropWith_cons_none
#print axioms LeanFzn.Engine.minGenPropWith_run_conflict
#print axioms LeanFzn.Engine.minGenPropWith_run_prune
#print axioms LeanFzn.Engine.minGenPropWith_conflict_entailed
#print axioms LeanFzn.Engine.minGenPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.minGenPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.minGenPropWith_prune_lit_none
#print axioms LeanFzn.Engine.minGenPropWith_run_fix_of_no_bounds
#print axioms LeanFzn.Engine.maxGenPropWith_run_conflict
#print axioms LeanFzn.Engine.maxGenPropWith_run_prune
#print axioms LeanFzn.Engine.maxGenPropWith_conflict_entailed
#print axioms LeanFzn.Engine.maxGenPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.maxGenPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.maxGenPropWith_prune_lit_none
#print axioms LeanFzn.Engine.maxGenPropWith_run_fix_of_no_bounds

-- N10b: dedicated order and bool2int propagators (`Engine/Props/Order.lean`).
#print axioms LeanFzn.Engine.domBounds_spec
#print axioms LeanFzn.Engine.evalLit_posLe_false_of_lo_gt
#print axioms LeanFzn.Engine.evalLit_negLe_false_of_hi_le
#print axioms LeanFzn.Engine.evalLit_posLe_true_of_hi_le
#print axioms LeanFzn.Engine.evalLit_negLe_true_of_lo_gt
#print axioms LeanFzn.Engine.DomC.evalLit_negate
#print axioms LeanFzn.Engine.atomSlot_neLit
#print axioms LeanFzn.Engine.atomSlot_eqLit
#print axioms LeanFzn.Engine.neLit_eval_isSome_of_mem
#print axioms LeanFzn.Engine.eqLit_eval_true_iff_of_mem
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_fixed_true
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_none_of_not_fixed
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_false_of_fixed_intView
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_true_of_not_mem
#print axioms LeanFzn.Engine.DomC.evalLit_negNe_false_of_not_mem
#print axioms LeanFzn.Engine.DomC.evalLit_negNe_none_of_mem
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_none_of_mem
#print axioms LeanFzn.Engine.DomC.evalLit_posBool_none_of_not_fixed
#print axioms LeanFzn.Engine.DomC.evalLit_negBool_none_of_not_fixed
#print axioms LeanFzn.Engine.DomC.evalLit_posBool_false_of_fixed_other
#print axioms LeanFzn.Engine.upperBoundPropWith_run_conflict
#print axioms LeanFzn.Engine.upperBoundPropWith_run_prune
#print axioms LeanFzn.Engine.upperBoundPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.lowerBoundPropWith_run_conflict
#print axioms LeanFzn.Engine.lowerBoundPropWith_run_prune
#print axioms LeanFzn.Engine.lowerBoundPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.leConstHi_entailed
#print axioms LeanFzn.Engine.leConstHiPropWith_run_conflict
#print axioms LeanFzn.Engine.leConstHiPropWith_run_prune
#print axioms LeanFzn.Engine.leConstHiPropWith_conflict_entailed
#print axioms LeanFzn.Engine.leConstHiPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.leConstHiPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.leConstHiPropWith_prune_lit_none
#print axioms LeanFzn.Engine.leConstHiPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.leConstLo_entailed
#print axioms LeanFzn.Engine.leConstLoPropWith_run_conflict
#print axioms LeanFzn.Engine.leConstLoPropWith_run_prune
#print axioms LeanFzn.Engine.leConstLoPropWith_conflict_entailed
#print axioms LeanFzn.Engine.leConstLoPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.leConstLoPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.leConstLoPropWith_prune_lit_none
#print axioms LeanFzn.Engine.leConstLoPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.ltConstHi_entailed
#print axioms LeanFzn.Engine.ltConstHiPropWith_run_conflict
#print axioms LeanFzn.Engine.ltConstHiPropWith_run_prune
#print axioms LeanFzn.Engine.ltConstHiPropWith_conflict_entailed
#print axioms LeanFzn.Engine.ltConstHiPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.ltConstHiPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.ltConstHiPropWith_prune_lit_none
#print axioms LeanFzn.Engine.ltConstHiPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.ltConstLo_entailed
#print axioms LeanFzn.Engine.ltConstLoPropWith_run_conflict
#print axioms LeanFzn.Engine.ltConstLoPropWith_run_prune
#print axioms LeanFzn.Engine.ltConstLoPropWith_conflict_entailed
#print axioms LeanFzn.Engine.ltConstLoPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.ltConstLoPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.ltConstLoPropWith_prune_lit_none
#print axioms LeanFzn.Engine.ltConstLoPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.leSlot_sem
#print axioms LeanFzn.Engine.ltSlot_sem
#print axioms LeanFzn.Engine.le_iUpper_reason_entailed
#print axioms LeanFzn.Engine.le_jLower_reason_entailed
#print axioms LeanFzn.Engine.le_conflict_reason_entailed
#print axioms LeanFzn.Engine.lePropWith_run_conflict
#print axioms LeanFzn.Engine.lePropWith_run_prune
#print axioms LeanFzn.Engine.lePropWith_conflict_entailed
#print axioms LeanFzn.Engine.lePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.lePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.lePropWith_prune_lit_none
#print axioms LeanFzn.Engine.lePropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.lePropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.lt_iUpper_reason_entailed
#print axioms LeanFzn.Engine.lt_jLower_reason_entailed
#print axioms LeanFzn.Engine.lt_conflict_reason_entailed
#print axioms LeanFzn.Engine.ltPropWith_run_conflict
#print axioms LeanFzn.Engine.ltPropWith_run_prune
#print axioms LeanFzn.Engine.ltPropWith_conflict_entailed
#print axioms LeanFzn.Engine.ltPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.ltPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.ltPropWith_prune_lit_none
#print axioms LeanFzn.Engine.ltPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.ltPropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.DomC.intView_isSome_of_mem
#print axioms LeanFzn.Engine.eqSlot_accepts_data
#print axioms LeanFzn.Engine.eqSlot_sem
#print axioms LeanFzn.Engine.eq_iUpper_reason_entailed
#print axioms LeanFzn.Engine.eq_jLower_reason_entailed
#print axioms LeanFzn.Engine.eq_iLower_reason_entailed
#print axioms LeanFzn.Engine.eq_jUpper_reason_entailed
#print axioms LeanFzn.Engine.eq_conflict_ji_reason_entailed
#print axioms LeanFzn.Engine.eq_conflict_ij_reason_entailed
#print axioms LeanFzn.Engine.eqConflict_reason_entailed
#print axioms LeanFzn.Engine.eqPropWith_prune_reason_entailed_i
#print axioms LeanFzn.Engine.eqPropWith_prune_reason_entailed_j
#print axioms LeanFzn.Engine.eqPruneFacts_singleton
#print axioms LeanFzn.Engine.eqPropWith_run_conflict
#print axioms LeanFzn.Engine.eqPropWith_run_prune
#print axioms LeanFzn.Engine.eqPropWith_conflict_entailed
#print axioms LeanFzn.Engine.eqPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.eqPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.eqPropWith_prune_lit_none
#print axioms LeanFzn.Engine.eqPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.eqPropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.DomC.memIntView_false_of_fixed_int_other
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_true_of_fixed_int_other
#print axioms LeanFzn.Engine.DomC.evalLit_negNe_false_of_fixed_int_other
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_int_false_of_fixed_int_other
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_int_none_of_memIntView
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_int_false_of_not_mem
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_bool_false_of_fixed_other
#print axioms LeanFzn.Engine.DomC.evalLit_eqLit_bool_none_of_not_fixed
#print axioms LeanFzn.Engine.bool2int_accepts_data
#print axioms LeanFzn.Engine.eval_eqLit_bool_true_iff
#print axioms LeanFzn.Engine.bool2int_i_reason_entailed
#print axioms LeanFzn.Engine.bool2int_k_reason_entailed
#print axioms LeanFzn.Engine.bool2int_k01_reason_entailed
#print axioms LeanFzn.Engine.bool2intPropWith_run_conflict
#print axioms LeanFzn.Engine.bool2intPropWith_run_prune
#print axioms LeanFzn.Engine.bool2intPropWith_conflict_entailed
#print axioms LeanFzn.Engine.bool2intPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.bool2intPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.bool2intPropWith_prune_lit_none
#print axioms LeanFzn.Engine.bool2intPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.bool2intPropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.neLit_bool_eval_true_iff
#print axioms LeanFzn.Engine.neLit_int_eval_true_iff
#print axioms LeanFzn.Engine.eqLit_int_eval_true_iff
#print axioms LeanFzn.Engine.leReif_true_sem
#print axioms LeanFzn.Engine.leReif_false_sem
#print axioms LeanFzn.Engine.eqReif_true_sem
#print axioms LeanFzn.Engine.eqReif_false_sem
#print axioms LeanFzn.Engine.neReif_true_sem
#print axioms LeanFzn.Engine.neReif_false_sem
#print axioms LeanFzn.Engine.leReif_true_conflict_reason_entailed
#print axioms LeanFzn.Engine.leReif_true_iUpper_reason_entailed
#print axioms LeanFzn.Engine.leReif_true_jLower_reason_entailed
#print axioms LeanFzn.Engine.leReif_false_conflict_reason_entailed
#print axioms LeanFzn.Engine.leReif_false_jUpper_reason_entailed
#print axioms LeanFzn.Engine.leReif_false_iLower_reason_entailed
#print axioms LeanFzn.Engine.leReif_rTrue_reason_entailed
#print axioms LeanFzn.Engine.leReif_rFalse_reason_entailed
#print axioms LeanFzn.Engine.leReifPropWith_run_conflict
#print axioms LeanFzn.Engine.leReifPropWith_run_prune
#print axioms LeanFzn.Engine.leReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.leReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.leReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.leReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.leReifPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.leReifPropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.slotInt_eq_some_exists
#print axioms LeanFzn.Engine.neLit_int_eval_false_iff
#print axioms LeanFzn.Engine.eqReif_true_conflict_ij_reason_entailed
#print axioms LeanFzn.Engine.eqReif_true_conflict_ji_reason_entailed
#print axioms LeanFzn.Engine.eqReif_true_iUpper_reason_entailed
#print axioms LeanFzn.Engine.eqReif_true_jLower_reason_entailed
#print axioms LeanFzn.Engine.eqReif_true_iLower_reason_entailed
#print axioms LeanFzn.Engine.eqReif_true_jUpper_reason_entailed
#print axioms LeanFzn.Engine.eqReif_disjoint_ij_reason_entailed
#print axioms LeanFzn.Engine.eqReif_disjoint_ji_reason_entailed
#print axioms LeanFzn.Engine.eqReif_false_conflict_reason_entailed
#print axioms LeanFzn.Engine.eqReif_false_prune_j_reason_entailed
#print axioms LeanFzn.Engine.eqReif_false_prune_i_reason_entailed
#print axioms LeanFzn.Engine.eqReif_decide_true_reason_entailed
#print axioms LeanFzn.Engine.eqReif_decide_false_reason_entailed
#print axioms LeanFzn.Engine.neReif_decide_false_reason_entailed
#print axioms LeanFzn.Engine.neReif_decide_true_reason_entailed
#print axioms LeanFzn.Engine.eqReifPropWith_run_conflict
#print axioms LeanFzn.Engine.eqReifPropWith_run_prune
#print axioms LeanFzn.Engine.eqReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.eqReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.eqReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.eqReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.eqReifPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.eqReifPropWith_run_fix_of_bounds_none_right
#print axioms LeanFzn.Engine.neReifPropWith_run_conflict
#print axioms LeanFzn.Engine.neReifPropWith_run_prune
#print axioms LeanFzn.Engine.neReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.neReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.neReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.neReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.neReifPropWith_run_fix_of_bounds_none
#print axioms LeanFzn.Engine.neReifPropWith_run_fix_of_bounds_none_right

-- N10a: bounded linear eq/ne/reif propagators (`Engine/Props/LinearExt.lean`).
#print axioms LeanFzn.Engine.linTotalMax_eq_eraseIdx_add
#print axioms LeanFzn.Engine.linMaxNegLit_false_bound
#print axioms LeanFzn.Engine.linDotSum_le_linTotalMax
#print axioms LeanFzn.Engine.linMaxNegLit_eval_false_of_not_true
#print axioms LeanFzn.Engine.linMaxNegLit_evalLit_false
#print axioms LeanFzn.Engine.atomSlot_linMaxNegLit
#print axioms LeanFzn.Engine.linPruneGePos_mul_lt
#print axioms LeanFzn.Engine.linPruneGeNeg_mul_lt
#print axioms LeanFzn.Engine.linPruneGePos_newLo_le_hi
#print axioms LeanFzn.Engine.linPruneGeNeg_newHi_ge_lo
#print axioms LeanFzn.Engine.linPrunesGe_mem
#print axioms LeanFzn.Engine.linPrunesGe_eq_fast
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_intKind
#print axioms LeanFzn.Engine.linPrunes_reason_satisfied
#print axioms LeanFzn.Engine.linPrunesGe_reason_satisfied
#print axioms LeanFzn.Engine.linConflict_satisfied
#print axioms LeanFzn.Engine.linMaxConflict_satisfied
#print axioms LeanFzn.Engine.linNonFixedIndices_mem
#print axioms LeanFzn.Engine.linNonFixedIndices_nil_spec
#print axioms LeanFzn.Engine.linNonFixedIndices_singleton_spec
#print axioms LeanFzn.Engine.linNonFixedIndices_singleton_fixed_erase
#print axioms LeanFzn.Engine.linDotSum_eq_linTotalMin_of_fixed
#print axioms LeanFzn.Engine.linNeConflict_satisfied
#print axioms LeanFzn.Engine.linNePrune_satisfied
#print axioms LeanFzn.Engine.domIntB_spec
#print axioms LeanFzn.Engine.slotsIntB_spec
#print axioms LeanFzn.Engine.viewIntKindB_spec
#print axioms LeanFzn.Engine.linTerms_slot_mem_is
#print axioms LeanFzn.Engine.linTerms_hint_of_dotProduct
#print axioms LeanFzn.Engine.dotProduct_eq_linDotSum_of_slotsIntB
#print axioms LeanFzn.Engine.dotProduct_decide_eq_true
#print axioms LeanFzn.Engine.linEq_accepts_facts
#print axioms LeanFzn.Engine.linNe_accepts_facts
#print axioms LeanFzn.Engine.linLeReif_accepts_facts
#print axioms LeanFzn.Engine.linEqReif_accepts_facts
#print axioms LeanFzn.Engine.linNeReif_accepts_facts
#print axioms LeanFzn.Engine.linLeConflict_satisfied
#print axioms LeanFzn.Engine.linMaxConflict_satisfied_of_ge
#print axioms LeanFzn.Engine.linPlanOut_run_conflict
#print axioms LeanFzn.Engine.linPlanOut_run_prune
#print axioms LeanFzn.Engine.linPlanOut_run_fix_of_no_prunes
#print axioms LeanFzn.Engine.linLePlan_conf_entailed
#print axioms LeanFzn.Engine.linLePlan_prunes_entailed
#print axioms LeanFzn.Engine.linGePlan_conf_entailed
#print axioms LeanFzn.Engine.linGePlan_prunes_entailed
#print axioms LeanFzn.Engine.linMaxConflict_lits_evalLit_false
#print axioms LeanFzn.Engine.linPruneGe_lit_evalLit_none
#print axioms LeanFzn.Engine.linPruneGe_other_lits_evalLit_false
#print axioms LeanFzn.Engine.linEqPlan_conflict_cases
#print axioms LeanFzn.Engine.linEqPlan_conflict_none_cases
#print axioms LeanFzn.Engine.linEqPlan_prunes_cases
#print axioms LeanFzn.Engine.linEqPlan_conf_entailed
#print axioms LeanFzn.Engine.linEqPlan_prunes_entailed
#print axioms LeanFzn.Engine.linEqOutWith_run_conflict
#print axioms LeanFzn.Engine.linEqOutWith_run_prune
#print axioms LeanFzn.Engine.linEqPropWith_run_conflict
#print axioms LeanFzn.Engine.linEqPropWith_run_prune
#print axioms LeanFzn.Engine.linEqPropWith_conflict_entailed
#print axioms LeanFzn.Engine.linEqPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linEqPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linEqPropWith_prune_lit_none
#print axioms LeanFzn.Engine.linEqPropWith_run_fix_of_size_ne
#print axioms LeanFzn.Engine.linDotSum_eq_linDotLo_of_posNe_false
#print axioms LeanFzn.Engine.linNeConflict_satisfied_of_dotLo
#print axioms LeanFzn.Engine.linNePruneFor_mem
#print axioms LeanFzn.Engine.linNePlan_conflict_cases
#print axioms LeanFzn.Engine.linNePlan_prunes_cases
#print axioms LeanFzn.Engine.linNePlan_conf_entailed
#print axioms LeanFzn.Engine.linNePlan_prunes_entailed
#print axioms LeanFzn.Engine.linNeOutWith_run_conflict
#print axioms LeanFzn.Engine.linNeOutWith_run_prune
#print axioms LeanFzn.Engine.linNePropWith_run_conflict
#print axioms LeanFzn.Engine.linNePropWith_run_prune
#print axioms LeanFzn.Engine.linNePropWith_conflict_entailed
#print axioms LeanFzn.Engine.linNePropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linNePropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linNePropWith_prune_lit_none
#print axioms LeanFzn.Engine.linNePropWith_run_fix_of_size_ne
#print axioms LeanFzn.Engine.Entailed_append_lit
#print axioms LeanFzn.Engine.linPlanAppendLit_conf_mem
#print axioms LeanFzn.Engine.linPlanAppendLit_prunes_mem
#print axioms LeanFzn.Engine.linPlanAppendLit_conf_entailed
#print axioms LeanFzn.Engine.linPlanAppendLit_prunes_entailed
#print axioms LeanFzn.Engine.linPlanSingle_prunes
#print axioms LeanFzn.Engine.domC_evalLit_posBool_true_iff
#print axioms LeanFzn.Engine.domC_evalLit_posBool_false_iff
#print axioms LeanFzn.Engine.domC_evalLit_posBool_none_iff
#print axioms LeanFzn.Engine.dotProduct_some_of_slotsIntB
#print axioms LeanFzn.Engine.linLeReif_rel_facts
#print axioms LeanFzn.Engine.linEqReif_rel_facts
#print axioms LeanFzn.Engine.linNeReif_rel_facts
#print axioms LeanFzn.Engine.linMaxLits_satisfied_or_all_false
#print axioms LeanFzn.Engine.linConflictLits_satisfied_or_all_false
#print axioms LeanFzn.Engine.linLeReifDecidePlan_prunes_entailed
#print axioms LeanFzn.Engine.linEqReifDecidePlan_prunes_entailed
#print axioms LeanFzn.Engine.linNeReifDecidePlan_prunes_entailed
#print axioms LeanFzn.Engine.linEqReif_fixed_conf_entailed
#print axioms LeanFzn.Engine.linEqReif_fixed_prunes_entailed
#print axioms LeanFzn.Engine.linLeReif_fixed_conf_entailed
#print axioms LeanFzn.Engine.linLeReif_fixed_prunes_entailed
#print axioms LeanFzn.Engine.linNeReif_fixed_conf_entailed
#print axioms LeanFzn.Engine.linNeReif_fixed_prunes_entailed
#print axioms LeanFzn.Engine.linLeReifDecidePlan_conflict_none
#print axioms LeanFzn.Engine.linEqReifDecidePlan_conflict_none
#print axioms LeanFzn.Engine.linNeReifDecidePlan_conflict_none
#print axioms LeanFzn.Engine.domC_evalLit_posBool_compl
#print axioms LeanFzn.Engine.domC_evalLit_posBool_none_of_not
#print axioms LeanFzn.Engine.domC_evalLit_posBool_none_of_none
#print axioms LeanFzn.Engine.linLePlan_conflict_cases
#print axioms LeanFzn.Engine.linLePlan_conflict_none_cases
#print axioms LeanFzn.Engine.linGePlan_conflict_cases
#print axioms LeanFzn.Engine.linGePlan_conflict_none_cases
#print axioms LeanFzn.Engine.linLeReifDecidePlan_prunes_cases
#print axioms LeanFzn.Engine.linEqReifDecidePlan_prunes_cases
#print axioms LeanFzn.Engine.linNeReifDecidePlan_prunes_cases
#print axioms LeanFzn.Engine.linLeReifOutWith_run_conflict
#print axioms LeanFzn.Engine.linPlanAppendLit_conflict_none
#print axioms LeanFzn.Engine.linLeReifOutWith_run_prune
#print axioms LeanFzn.Engine.linEqReifOutWith_run_conflict
#print axioms LeanFzn.Engine.linEqReifOutWith_run_prune
#print axioms LeanFzn.Engine.linNeReifOutWith_run_conflict
#print axioms LeanFzn.Engine.linNeReifOutWith_run_prune
#print axioms LeanFzn.Engine.linEqReifPropWith_run_conflict
#print axioms LeanFzn.Engine.linEqReifPropWith_run_prune
#print axioms LeanFzn.Engine.linEqReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.linEqReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linEqReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linEqReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.linEqReifPropWith_run_fix_of_size_ne
#print axioms LeanFzn.Engine.linLeReifPropWith_run_conflict
#print axioms LeanFzn.Engine.linLeReifPropWith_run_prune
#print axioms LeanFzn.Engine.linLeReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.linLeReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linLeReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linLeReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.linLeReifPropWith_run_fix_of_size_ne
#print axioms LeanFzn.Engine.linNeReifPropWith_run_conflict
#print axioms LeanFzn.Engine.linNeReifPropWith_run_prune
#print axioms LeanFzn.Engine.linNeReifPropWith_conflict_entailed
#print axioms LeanFzn.Engine.linNeReifPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.linNeReifPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.linNeReifPropWith_prune_lit_none
#print axioms LeanFzn.Engine.linNeReifPropWith_run_fix_of_size_ne

-- N10d: dedicated Boolean propagators (`Engine/Props/BoolExt.lean`).
#print axioms LeanFzn.Engine.BArg.BShape.ofDom?_isBool
#print axioms LeanFzn.Engine.BArg.BShape.ofDom?_fixedFalse
#print axioms LeanFzn.Engine.BArg.BShape.ofDom?_fixedTrue
#print axioms LeanFzn.Engine.BArg.BShape.ofDom?_full_none
#print axioms LeanFzn.Engine.BArg.ofDom?_slot
#print axioms LeanFzn.Engine.BArg.ofDom?_cur_cases
#print axioms LeanFzn.Engine.BArg.ofDom?_isBool
#print axioms LeanFzn.Engine.BArg.ofDom?_eq_none_of_not_bool
#print axioms LeanFzn.Engine.BArg.ofDom?_fixed_false
#print axioms LeanFzn.Engine.BArg.ofDom?_fixed_true
#print axioms LeanFzn.Engine.BArg.ofDom?_full_fixed_none
#print axioms LeanFzn.Engine.BArg.ofDom?_evalLit_fixed
#print axioms LeanFzn.Engine.BArg.ofDom?_evalLit_none_full
#print axioms LeanFzn.Engine.BArgs.ofSlots_map_slot
#print axioms LeanFzn.Engine.BArgs.ofSlots_allCur
#print axioms LeanFzn.Engine.BArgs.ofSlots_eq_none_of_mem_mk_none
#print axioms LeanFzn.Engine.BArgs.mem_enum_iff
#print axioms LeanFzn.Engine.BArgs.hasSupport_true
#print axioms LeanFzn.Engine.BArgs.hasAnySupport_false
#print axioms LeanFzn.Engine.BArgs.hasSupport_false
#print axioms LeanFzn.Engine.BArgs.valsOf_length
#print axioms LeanFzn.Engine.BArgs.valsOf_getD
#print axioms LeanFzn.Engine.BArgs.getD_mem
#print axioms LeanFzn.Engine.BArgs.mem_fixedLits
#print axioms LeanFzn.Engine.BArg.eval_posBool_eq_false_of_not_true
#print axioms LeanFzn.Engine.BArgs.fixedLits_false_of_not_true
#print axioms LeanFzn.Engine.BArg.valAt_eq_true_iff
#print axioms LeanFzn.Engine.BArg.valAt_eq_of_some_bool
#print axioms LeanFzn.Engine.BArg.valAt_eq_slotIsBoolB
#print axioms LeanFzn.Engine.BArg.slot_of_mem_fixedLit
#print axioms LeanFzn.Engine.BArg.cur_false_of_fixedLits_false
#print axioms LeanFzn.Engine.BArg.cur_true_of_fixedLits_false
#print axioms LeanFzn.Engine.BArg.valAt_of_fixed_false
#print axioms LeanFzn.Engine.BArg.valAt_of_fixed_true
#print axioms LeanFzn.Engine.BArg.cur_valAt_of_fixedLits_false
#print axioms LeanFzn.Engine.BArgs.curVec_valsOf_of_fixedLits_false
#print axioms LeanFzn.Engine.BArgs.mem_mkPrunes
#print axioms LeanFzn.Engine.BArgs.mkPlan_conflict_entailed
#print axioms LeanFzn.Engine.BArgs.mkPrunes_reason_entailed
#print axioms LeanFzn.Engine.BArgs.mkPlan_prunes_entailed
#print axioms LeanFzn.Engine.BPlan.out_run_conflict
#print axioms LeanFzn.Engine.BPlan.out_run_prune
#print axioms LeanFzn.Engine.BPlan.out_run_fix_of_no_prunes
#print axioms LeanFzn.Engine.BArgs.ofSlots_two
#print axioms LeanFzn.Engine.BArgs.ofSlots_three
#print axioms LeanFzn.Engine.BArgs.ofSlots_array
#print axioms LeanFzn.Engine.BArgs.planOf_some
#print axioms LeanFzn.Engine.BArgs.planOf_prunes_eq
#print axioms LeanFzn.Engine.getD_append_singleton_self
#print axioms LeanFzn.Engine.BArgs.initBoolB_some
#print axioms LeanFzn.Engine.BArgs.exists_bool_of_mem_bool
#print axioms LeanFzn.Engine.BArgs.mem_getD_bool_of_init
#print axioms LeanFzn.Engine.BArgs.boolNotR_spec
#print axioms LeanFzn.Engine.BArgs.boolAndR_spec
#print axioms LeanFzn.Engine.BArgs.boolOrR_spec
#print axioms LeanFzn.Engine.BArgs.boolEqR_spec
#print axioms LeanFzn.Engine.BArgs.arrayBoolAndR_spec
#print axioms LeanFzn.Engine.BArgs.mem_fixedLits_fixedLit
#print axioms LeanFzn.Engine.BArgs.ofSlots_mem_mk
#print axioms LeanFzn.Engine.BArgs.ofSlots_eval_fixed
#print axioms LeanFzn.Engine.BArgs.hasAnySupport_true
#print axioms LeanFzn.Engine.BArgs.curVec_getD
#print axioms LeanFzn.Engine.BArgs.cur_other_of_prune
#print axioms LeanFzn.Engine.BArgs.mkPlan_conflict_eq_fixedLits
#print axioms LeanFzn.Engine.BArgs.mem_mkPrunes_shape
#print axioms LeanFzn.Engine.BArgs.mkPrunes_evalLit_none
#print axioms LeanFzn.Engine.BPlan.out_run_conflict_plan
#print axioms LeanFzn.Engine.BPlan.out_run_prune_plan
#print axioms LeanFzn.Engine.BPlan.out_run_prune_lit_none_plan
#print axioms LeanFzn.Engine.boolSupportPropWith_run_conflict
#print axioms LeanFzn.Engine.boolSupportPropWith_run_prune
#print axioms LeanFzn.Engine.boolSupportPropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolSupportPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolSupportPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolSupportPropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolSupportPropWith_run_fix_of_no_plan
#print axioms LeanFzn.Engine.boolNotPropWith_run_conflict
#print axioms LeanFzn.Engine.boolNotPropWith_run_prune
#print axioms LeanFzn.Engine.boolNotPropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolNotPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolNotPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolNotPropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolNotPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.boolAndPropWith_run_conflict
#print axioms LeanFzn.Engine.boolAndPropWith_run_prune
#print axioms LeanFzn.Engine.boolAndPropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolAndPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolAndPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolAndPropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolAndPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.boolOrPropWith_run_conflict
#print axioms LeanFzn.Engine.boolOrPropWith_run_prune
#print axioms LeanFzn.Engine.boolOrPropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolOrPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolOrPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolOrPropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolOrPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.boolEqPropWith_run_conflict
#print axioms LeanFzn.Engine.boolEqPropWith_run_prune
#print axioms LeanFzn.Engine.boolEqPropWith_conflict_entailed
#print axioms LeanFzn.Engine.boolEqPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.boolEqPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.boolEqPropWith_prune_lit_none
#print axioms LeanFzn.Engine.boolEqPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_run_conflict
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_run_prune
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_conflict_entailed
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_prune_lit_none
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.boolNotPropWith_run_fix_of_slots_none
#print axioms LeanFzn.Engine.boolAndPropWith_run_fix_of_slots_none
#print axioms LeanFzn.Engine.boolOrPropWith_run_fix_of_slots_none
#print axioms LeanFzn.Engine.boolEqPropWith_run_fix_of_slots_none
#print axioms LeanFzn.Engine.arrayBoolAndPropWith_run_fix_of_slots_none

-- N10e: dedicated element propagators (`Engine/Props/Element.lean`).
#print axioms LeanFzn.Engine.mem_intCandidatesAux
#print axioms LeanFzn.Engine.mem_intCandidates
#print axioms LeanFzn.Engine.DomC.evalLit_negNe_false_of_not_memIntView
#print axioms LeanFzn.Engine.DomC.evalLit_posNe_false_of_fixed_int
#print axioms LeanFzn.Engine.mkElemPruneArray_mem
#print axioms LeanFzn.Engine.aie_satisfied_views
#print axioms LeanFzn.Engine.aie_entailed_out
#print axioms LeanFzn.Engine.aie_entailed_noSupp
#print axioms LeanFzn.Engine.aie_entailed_posLe
#print axioms LeanFzn.Engine.aie_entailed_negLe
#print axioms LeanFzn.Engine.aiePrunePairs_entailed
#print axioms LeanFzn.Engine.aiePrunePairs_eval
#print axioms LeanFzn.Engine.aieOut_conflict_cases
#print axioms LeanFzn.Engine.aieOut_prune_cases
#print axioms LeanFzn.Engine.arrayIntElementPropWith_run_conflict
#print axioms LeanFzn.Engine.arrayIntElementPropWith_run_prune
#print axioms LeanFzn.Engine.arrayIntElementPropWith_conflict_entailed
#print axioms LeanFzn.Engine.arrayIntElementPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.arrayIntElementPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.arrayIntElementPropWith_prune_lit_none
#print axioms LeanFzn.Engine.arrayIntElementPropWith_run_fix_of_bounds
#print axioms LeanFzn.Engine.intBounds_some_iff
#print axioms LeanFzn.Engine.avieJPrunes_mem
#print axioms LeanFzn.Engine.avieKPrunes_mem
#print axioms LeanFzn.Engine.safePrunes_mem
#print axioms LeanFzn.Engine.avieFixedPrunes_mem
#print axioms LeanFzn.Engine.avieIndexPrunes_mem
#print axioms LeanFzn.Engine.avieNoSuppPrunes_mem
#print axioms LeanFzn.Engine.avieGeneralPrunes_mem
#print axioms LeanFzn.Engine.avie_entailed_out
#print axioms LeanFzn.Engine.avie_entailed_J
#print axioms LeanFzn.Engine.avie_entailed_K
#print axioms LeanFzn.Engine.avie_entailed_pinVal
#print axioms LeanFzn.Engine.avie_entailed_single
#print axioms LeanFzn.Engine.avie_entailed_below
#print axioms LeanFzn.Engine.avie_entailed_above
#print axioms LeanFzn.Engine.avie_entailed_noSupp
#print axioms LeanFzn.Engine.avieBadIndexPinVal?_entailed
#print axioms LeanFzn.Engine.avieBadIndexPairOf?_entailed
#print axioms LeanFzn.Engine.avieBadIndexPair?_entailed
#print axioms LeanFzn.Engine.aviePrunePairs_entailed
#print axioms LeanFzn.Engine.avieFixedConflict?_cases
#print axioms LeanFzn.Engine.aviePrunePairs_eval
#print axioms LeanFzn.Engine.avieOut_conflict_cases
#print axioms LeanFzn.Engine.avieOut_prune_cases
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_run_conflict
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_conflict_entailed
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_run_prune
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_prune_lit_none
#print axioms LeanFzn.Engine.avieOut_eq_fix_of_index_bounds_none
#print axioms LeanFzn.Engine.avieOut_eq_fix_of_result_bounds_none
#print axioms LeanFzn.Engine.avieOut_eq_fix_of_table_false
#print axioms LeanFzn.Engine.arrayVarIntElementPropWith_run_fix_of_malformed
#print axioms LeanFzn.Engine.avbeFixedPrunes_mem
#print axioms LeanFzn.Engine.avbeBadIndexPair?_mem
#print axioms LeanFzn.Engine.avbeBadIndexPair?_cases
#print axioms LeanFzn.Engine.avbe_entailed_out
#print axioms LeanFzn.Engine.avbe_entailed_pinVal
#print axioms LeanFzn.Engine.avbe_entailed_single
#print axioms LeanFzn.Engine.avbeBadIndexPair?_entailed
#print axioms LeanFzn.Engine.avbePrunePairs_entailed
#print axioms LeanFzn.Engine.avbePrunePairs_eval
#print axioms LeanFzn.Engine.avbeOut_conflict_cases
#print axioms LeanFzn.Engine.avbeOut_prune_cases
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_run_conflict
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_conflict_entailed
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_conflict_lits_false
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_run_prune
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_prune_reason_entailed
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_prune_lit_none
#print axioms LeanFzn.Engine.avbeOut_eq_fix_of_index_bounds_none
#print axioms LeanFzn.Engine.avbeOut_eq_fix_of_result_bounds_none
#print axioms LeanFzn.Engine.avbeOut_eq_fix_of_guard_false
#print axioms LeanFzn.Engine.arrayVarBoolElementPropWith_run_fix_of_malformed

-- N11a: Core as a certified optimizer (`Integration/CoreOptimize.lean`).
#print axioms LeanFzn.Integration.coreVerdict_sat
#print axioms LeanFzn.Integration.coreVerdict_unsat
#print axioms LeanFzn.Integration.coreVerdict_ne_fail
#print axioms LeanFzn.Integration.coreVerdict_eq_sat_iff
#print axioms LeanFzn.Integration.coreVerdict_eq_unsat_iff
#print axioms LeanFzn.Integration.coreVerdictWith_sat
#print axioms LeanFzn.Integration.coreVerdictWith_unsat
#print axioms LeanFzn.Integration.coreVerdictWith_ne_fail
#print axioms LeanFzn.Integration.coreVerdictWith_eq_fallback
#print axioms LeanFzn.Integration.coreVerdictWith_eq_coreVerdict_of_not_gaveUp
#print axioms LeanFzn.Integration.coreVerdictWith_eq_sat_iff
#print axioms LeanFzn.Integration.coreVerdictWith_eq_unsat_iff
#print axioms LeanFzn.Integration.coreVerdictSeeded_sat
#print axioms LeanFzn.Integration.coreVerdictSeeded_unsat
#print axioms LeanFzn.Integration.coreVerdictSeeded_ne_fail
#print axioms LeanFzn.Integration.coreVerdictSeeded_eq_fallback
#print axioms LeanFzn.Integration.coreVerdictSeeded_eq_sat_iff
#print axioms LeanFzn.Integration.coreVerdictSeeded_eq_unsat_iff
#print axioms LeanFzn.Integration.coreSolver_gate
#print axioms LeanFzn.Integration.optimizeCore_solution_sound
#print axioms LeanFzn.Integration.optimizeCore_improving
#print axioms LeanFzn.Integration.optimizeCore_optimal
#print axioms LeanFzn.Integration.optimizeCore_unsat
#print axioms LeanFzn.Integration.optimizeCore_total

-- N11b: incremental Core branch and bound (`Engine/Incremental.lean`,
-- `Integration/CoreSeed.lean`).
#print axioms LeanFzn.Engine.coreSolveSeedTail_sat
#print axioms LeanFzn.Engine.coreSolveSeedTail_unsat
#print axioms LeanFzn.Engine.coreSolveSeed_sat
#print axioms LeanFzn.Engine.coreSolveSeed_unsat
#print axioms LeanFzn.Integration.coreSeedVerdict_sat
#print axioms LeanFzn.Integration.coreSeedVerdict_unsat
#print axioms LeanFzn.Integration.coreSeedVerdict_ne_fail
#print axioms LeanFzn.Integration.coreSeed_improveBound_satisfiedB_mono
#print axioms LeanFzn.Integration.coreSeedBetterBound
#print axioms LeanFzn.Integration.optLoopCoreSeed_inv
#print axioms LeanFzn.Integration.optLoopCoreSeed_complete
#print axioms LeanFzn.Integration.optimizeCoreSeed_inv
#print axioms LeanFzn.Integration.optimizeCoreSeed_solution_sound
#print axioms LeanFzn.Integration.optimizeCoreSeed_improving
#print axioms LeanFzn.Integration.optimizeCoreSeed_optimal
#print axioms LeanFzn.Integration.optimizeCoreSeed_unsat
#print axioms LeanFzn.Integration.optimizeCoreSeed_total
#print axioms LeanFzn.Integration.optimizeStreamCoreSeedLoop_emit
#print axioms LeanFzn.Integration.optimizeStreamCoreSeed_eq

-- N13: certified LBD clause-database reduction (`Engine/Reduce.lean`).
#print axioms LeanFzn.Engine.ClauseDB.setLbd_getElem?
#print axioms LeanFzn.Engine.ClauseDB.setLbd_clauses_size
#print axioms LeanFzn.Engine.ClauseDB.setLbd_inv
#print axioms LeanFzn.Engine.ClauseDB.setLbd_getElem?_self
#print axioms LeanFzn.Engine.ClauseDB.setLbd_live
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_clauses
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_free
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_live
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_liveB
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_watchList
#print axioms LeanFzn.Engine.ClauseDB.watchesAt_compactWatches
#print axioms LeanFzn.Engine.ClauseDB.compactWatches_inv
#print axioms LeanFzn.Engine.retireStep_e_lits
#print axioms LeanFzn.Engine.retireStep_w1
#print axioms LeanFzn.Engine.retireStep_w2
#print axioms LeanFzn.Engine.retireStep_live_eq
#print axioms LeanFzn.Engine.ClauseDB.retireMark_watch
#print axioms LeanFzn.Engine.ClauseDB.retireMark_free
#print axioms LeanFzn.Engine.ClauseDB.retireMark_clauses
#print axioms LeanFzn.Engine.ClauseDB.retireMark_live
#print axioms LeanFzn.Engine.ClauseDB.retireMark_getElem?
#print axioms LeanFzn.Engine.ClauseDB.retireMark_clauses_size
#print axioms LeanFzn.Engine.ClauseDB.retireMark_inv
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_clauses
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_free
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_live
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_clauses_size
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_inv
#print axioms LeanFzn.Engine.ClauseDB.retireWhere_live_le
#print axioms LeanFzn.Engine.ClauseDB.reduce_clauses_size
#print axioms LeanFzn.Engine.ClauseDB.reduce_inv
#print axioms LeanFzn.Engine.ClauseDB.reduce_live_le
#print axioms LeanFzn.Engine.maybeReduce_doms
#print axioms LeanFzn.Engine.maybeReduce_trail
#print axioms LeanFzn.Engine.maybeReduce_level
#print axioms LeanFzn.Engine.maybeReduce_stats
#print axioms LeanFzn.Engine.maybeReduce_table
#print axioms LeanFzn.Engine.maybeReduce_nextReduce
#print axioms LeanFzn.Engine.maybeReduce_db
#print axioms LeanFzn.Engine.maybeReduce_inv

-- Core-only public API: sound completed results and exact streaming traces.
#print axioms LeanFzn.Core.solveCompiled_sat
#print axioms LeanFzn.Core.solveCompiled_unsat
#print axioms LeanFzn.Core.solveModelWithStats_fst
#print axioms LeanFzn.Core.solveModel_sat_correct
#print axioms LeanFzn.Core.solveModel_unsat_correct
#print axioms LeanFzn.Core.coreVerdictWith_sat
#print axioms LeanFzn.Core.coreVerdictWith_unsat
#print axioms LeanFzn.Core.optimizeCore_solution_sound
#print axioms LeanFzn.Core.optimizeCore_improving
#print axioms LeanFzn.Core.optimizeCore_optimal
#print axioms LeanFzn.Core.optimizeCore_unsat
#print axioms LeanFzn.Core.coreSeedVerdict_sat
#print axioms LeanFzn.Core.coreSeedVerdict_unsat
#print axioms LeanFzn.Core.optLoopCoreSeed_inv
#print axioms LeanFzn.Core.optimizeCoreSeed_solution_sound
#print axioms LeanFzn.Core.optimizeCoreSeed_improving
#print axioms LeanFzn.Core.optimizeCoreSeed_optimal
#print axioms LeanFzn.Core.optimizeCoreSeed_unsat
#print axioms LeanFzn.Core.optimizeStreamCoreSeedLoop_emit
#print axioms LeanFzn.Core.optimizeStreamCoreSeed_eq
#print axioms LeanFzn.Core.coreSeed_improveBound_satisfiedB_mono
#print axioms LeanFzn.Core.coreSeedBetterBound
#print axioms LeanFzn.Core.optimizeCoreSeed_inv
