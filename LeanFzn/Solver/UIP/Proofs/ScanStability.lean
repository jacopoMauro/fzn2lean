/-
File: LeanFzn/Solver/UIP/Proofs/ScanStability.lean

Purpose: the C1 `hdb` producer chain. The former premise
`∀ cfg, SchedulerReachable cfg → DatabaseUnfalsified cfg.branch` overclaimed
at arbitrary reachable configurations (it also demanded unfalsifiedness at
non-evidence states); PLAN C1 restates `hdb` at the ACTUAL analysis site:

  §1 `ScanStableRecorded` — the site predicate: whenever a configuration
     carries recorded evidence, its database scan is stable.
  §2 `schedulerNext_successor_conflict_terminal` — the recording-successor
     classification WITH the predecessor's terminal event: a successor
     carrying evidence is exactly the `.analyzeConflict` successor of a
     conflictStep arm whose `terminalResult` was a nonempty conflict.
  §3 `scanDatabase_stable_of_recordedStep` / `scanStableRecorded_of_reachable`
     — ONE dispatched step (then the whole run by structural induction)
     establishes the site predicate, via
     `nextPruningEvent_eq_of_terminalResult_conflict` +
     `scanDatabase_stable_of_nextPruningEvent_conflict_cons`.
  §4 `databaseUnfalsified_of_reachable_recorded` /
     `supportedDatabaseUnfalsified_of_recorded` — the concrete site-form
     `hdb` producers (branch reachability + frame inhabitedness inputs).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.ScanStability` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedDatabaseFacts
import LeanFzn.Solver.UIP.Proofs.DatabaseUnfalsified
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Solver.UIP.Proofs.Scheduler
import LeanFzn.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The site predicate -/

/-- C1's analysis-site database fact: every configuration carrying
recorded conflict evidence has a STABLE database scan. This is the
honest restatement of `hdb` (no claim at non-evidence states). -/
def ScanStableRecorded {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop :=
  ∀ ev : ConflictEvidence, cfg.conflict = some ev →
    scanDatabase cfg.original cfg.branch.frame cfg.branch.learned = .stable

/-! ## §2 The recording-successor classification with the terminal event -/

/-- A successor configuration carrying recorded evidence is EXACTLY the
`.analyzeConflict` successor of a `conflictStep` arm whose predecessor's
`terminalResult` was a nonempty conflict. This refines
`schedulerNext_successor_conflict_classification` with the predecessor's
terminal event (the fact the scan-stability transport consumes). -/
theorem schedulerNext_successor_conflict_terminal {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {t : SchedulerTransition leaf}
    {ev' : ConflictEvidence}
    (hnext : schedulerNext cfg = t) (hsucc : t.successor = some cfg')
    (hev' : cfg'.conflict = some ev') :
    ∃ (bs : BranchState leaf) (c : Clause) (rest learned : List Clause),
      terminalResult cfg.original cfg.props cfg.branch
          = .conflict bs (c :: rest) learned ∧
        cfg' = stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.branch.trail cfg.branch.level c) := by
  cases hcc : cfg.conflict with
  | some ev =>
      have ht : backjumpStep cfg ev = t := by
        simp only [schedulerNext, hcc] at hnext
        exact hnext
      rw [← ht] at hsucc
      rw [backjumpStep_successor_conflict_none hsucc] at hev'
      cases hev'
  | none =>
      cases hst : cfg.status with
      | dead =>
          have ht : consumeStep cfg = t := by
            simp only [schedulerNext, hcc, hst] at hnext
            exact hnext
          rw [← ht] at hsucc
          rw [consumeStep_successor_conflict hsucc] at hev'
          cases hev'
      | active =>
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              have ht : SchedulerTransition.propagate (stepPropagate cfg d) = t := by
                simp only [schedulerNext, hcc, hst, hd] at hnext
                exact hnext
              rw [← ht] at hsucc
              rw [successor_propagate] at hsucc
              cases hsucc
              rw [stepPropagate_conflict, hcc] at hev'
              cases hev'
          | none =>
              cases htt : terminalResult cfg.original cfg.props cfg.branch with
              | stable st =>
                  have ht : stableStepGuarded cfg = t := by
                    simp only [schedulerNext, hcc, hst, hd, htt] at hnext
                    exact hnext
                  rw [← ht] at hsucc
                  rw [stableStepGuarded_successor_conflict_none hcc hsucc] at hev'
                  cases hev'
              | conflict bs cs learned =>
                  have ht : conflictStep cfg cs learned = t := by
                    simp only [schedulerNext, hcc, hst, hd, htt] at hnext
                    exact hnext
                  rw [← ht] at hsucc
                  cases cs with
                  | nil =>
                      simp only [conflictStep] at hsucc
                      rw [successor_localExclude] at hsucc
                      cases hsucc
                      rw [stepLocalExclude_conflict] at hev'
                      cases hev'
                  | cons c rest =>
                      by_cases hl : cfg.branch.level = 0
                      · simp only [conflictStep, if_pos hl, successor_unsat] at hsucc
                        cases hsucc
                      · simp only [conflictStep, if_neg hl] at hsucc
                        rw [successor_analyzeConflict] at hsucc
                        cases hsucc
                        exact ⟨bs, c, rest, learned, rfl, rfl⟩
              | localExcluded bs lit reason learned =>
                  have ht : SchedulerTransition.localExclude
                      (stepLocalExclude cfg learned (branchRegion cfg)) = t := by
                    simp only [schedulerNext, hcc, hst, hd, htt] at hnext
                    exact hnext
                  rw [← ht] at hsucc
                  rw [successor_localExclude] at hsucc
                  cases hsucc
                  rw [stepLocalExclude_conflict] at hev'
                  cases hev'

/-! ## §3 The one-step and run-level scan stability -/

/-- **THE C1 ONE-STEP LAW**: at any successor carrying recorded evidence,
the database scan is stable. The classification exposes the predecessor's
nonempty terminal conflict; the event bridge and the database-stability
transfer close it, transported along the recording site's definitional
shape. -/
theorem scanDatabase_stable_of_recordedStep {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {t : SchedulerTransition leaf}
    (hnext : schedulerNext cfg = t) (hsucc : t.successor = some cfg') :
    ScanStableRecorded cfg' := by
  intro ev' hev'
  obtain ⟨bs, c, rest, learned, htt, hcfg'⟩ :=
    schedulerNext_successor_conflict_terminal hnext hsucc hev'
  rw [hcfg']
  have horig : (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.branch.trail cfg.branch.level c)).original
      = cfg.original := rfl
  have hev_eq : nextPruningEvent cfg.original cfg.props cfg.branch.frame
      cfg.branch.learned = .conflict (c :: rest) :=
    nextPruningEvent_eq_of_terminalResult_conflict htt
  rw [horig, stepAnalyzeConflictCounted_branch]
  exact scanDatabase_stable_of_nextPruningEvent_conflict_cons hev_eq

/-- **PROVED**: every reachable configuration satisfies the site predicate
(structural induction on reachability; each step by the one-step law). -/
theorem scanStableRecorded_of_reachable {leaf : Assignment → Bool}
    {cfg₀ : SchedulerConfig leaf} (h : SchedulerReachable cfg₀) :
    ScanStableRecorded cfg₀ := by
  induction h with
  | init orig original props =>
      intro ev hev
      simp [SchedulerConfig.init] at hev
  | step hnext hsucc ih =>
      exact scanDatabase_stable_of_recordedStep hnext hsucc

/-! ## §4 The site-form `hdb` producers -/

/-- **THE C1 SITE-FORM `hdb` PRODUCER**: at a reachable configuration
carrying recorded evidence, the branch database is unfalsified — from the
run-level scan stability plus the two per-state inputs this site needs
(branch reachability and frame inhabitedness; the latter is C2's named
input, kernel-refuted as a universal invariant). -/
theorem databaseUnfalsified_of_reachable_recorded {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (hreach : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hbr : ReachableState leaf cfg.orig cfg.branch)
    (hinhab : ∃ a, FrameCovers cfg.branch.frame a) :
    DatabaseUnfalsified cfg.branch :=
  databaseUnfalsified_of_scanDatabase_stable hbr hinhab
    (scanStableRecorded_of_reachable hreach ev hconf)

/-- The `SupportedReach`-indexed form (the field shape
`SupportedPhasePremises.hdb` needs, restricted to evidence sites). -/
theorem supportedDatabaseUnfalsified_of_recorded {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence}
    (hreach : SupportedReach orig original props cfg)
    (hconf : cfg.conflict = some ev)
    (hbr : ReachableState leaf orig cfg.branch)
    (hinhab : ∃ a, FrameCovers cfg.branch.frame a) :
    DatabaseUnfalsified cfg.branch := by
  have hbr' : ReachableState leaf cfg.orig cfg.branch :=
    (by rwa [← SupportedReach.orig_eq hreach] at hbr)
  exact databaseUnfalsified_of_reachable_recorded (orig := cfg.orig)
    hreach.reachable hconf hbr' hinhab

end LeanFzn.Solver.UIP
