/-
Purpose: canonical learned databases and recorded payloads on actual scheduler runs.
Dependencies: LcgCanonicalRun supplies closure/terminal/restoration preservation;
Scheduler case lemmas identify the exact runtime transitions.
DAG: canonical emissions -> this syntax invariant -> mixed semantic run certification.
-/
import LeanFzn.Solver.UIP.Proofs.LcgCanonicalRun
namespace LeanFzn.Solver.UIP.LcgCanonicalScheduler
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgCanonicalClauses LeanFzn.Solver.UIP.LcgCanonicalRun

structure CanonicalCfg {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop where
  db : DatabaseCanonical cfg.branch.learned
  evidence : ∀ ev, cfg.conflict = some ev → DatabaseCanonical ev.learned ∧
    ∀ an, ev.analysis = some an → ClauseCanonical an.learned

theorem canonicalCfg_none {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    (hdb : DatabaseCanonical cfg.branch.learned) (hn : cfg.conflict = none) : CanonicalCfg cfg where
  db := hdb
  evidence := by intro ev he; rw [hn] at he; cases he

theorem canonicalCfg_same {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (hd : cfg'.branch.learned = cfg.branch.learned)
    (hc : cfg'.conflict = cfg.conflict) : CanonicalCfg cfg' where
  db := by rw [hd]; exact h.db
  evidence := by intro ev he; rw [hc] at he; exact h.evidence ev he

theorem canonicalCfg_change_db {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (hd : DatabaseCanonical cfg'.branch.learned)
    (hc : cfg'.conflict = cfg.conflict) : CanonicalCfg cfg' where
  db := hd
  evidence := by intro ev he; rw [hc] at he; exact h.evidence ev he

theorem canonicalCfg_analyze {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (c : Clause) (learned : List Clause)
    (hl : DatabaseCanonical learned) : CanonicalCfg (stepAnalyzeConflict cfg c learned) where
  db := h.db
  evidence := by
    intro ev he
    change some { clause := c, learned := learned, analysis := recordedAnalysis cfg c } = some ev at he
    cases he
    exact ⟨hl, fun an han => recordedAnalysis_canonical han⟩

theorem canonicalCfg_consume {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (hc : stepConsume cfg = some next) : CanonicalCfg next := by
  cases hp : cfg.pending with
  | nil => simp [stepConsume, hp] at hc
  | cons f rest =>
      simp only [stepConsume, hp, Option.some.injEq] at hc
      subst next
      apply canonicalCfg_none
      · rw [resumePending_learned]
        exact h.db
      · rfl


/-- Counted analysis changes only resolution metadata in recorded evidence. -/
theorem canonicalCfg_countResolutions {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (n : Nat) : CanonicalCfg (cfg.countResolutions n) where
  db := h.db
  evidence := by
    intro ev he
    change (cfg.conflict.map fun ev => { ev with resolutions := ev.resolutions + n }) = some ev at he
    obtain ⟨ev0, he0, hev⟩ := Option.map_eq_some_iff.mp he
    rw [← hev]
    exact h.evidence ev0 he0

/-- Canonical databases, pending conflict payloads and analyses are preserved
by every actual dispatcher successor. -/
theorem canonicalCfg_step {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (h : CanonicalCfg cfg) (hp : EmissionCanonical cfg.props)
    (hsucc : (schedulerNext cfg).successor = some cfg') : CanonicalCfg cfg' := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha,
          successor_chronologicalFallback] at hsucc
        cases hsucc
        exact canonicalCfg_none h.db rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp,
              successor_chronologicalFallback] at hsucc
            cases hsucc
            exact canonicalCfg_none h.db rfl
        | some cp =>
            cases hr : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
                cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hr,
                  successor_localExclude] at hsucc
                cases hsucc
                exact canonicalCfg_none (databaseCanonical_append (h.evidence ev hc).1 h.db) rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hr,
                  successor_learnBackjumpAssert] at hsucc
                cases hsucc
                apply canonicalCfg_none
                · exact databaseCanonical_append (h.evidence ev hc).1
                    (perform_canonical hp h.db ((h.evidence ev hc).2 an ha) hr)
                · rfl
  · rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none => simp [consumeStep, hcons] at hsucc
    | some next =>
        simp only [consumeStep, hcons, successor_chronologicalFallback] at hsucc
        cases hsucc
        exact canonicalCfg_consume h hcons
  · rcases hrest with ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ |
      ⟨bs, cs, learned, ht, hsj⟩ | ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj, successor_propagate] at hsucc
      cases hsucc
      exact canonicalCfg_change_db h (stepNarrowSync_canonical hp h.db hd) rfl
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w => simp [hl] at hsucc
      | none =>
          cases hs : splitData cfg.branch.frame with
          | none =>
              simp only [hl, hs, successor_localExclude] at hsucc
              cases hsucc
              exact canonicalCfg_none h.db rfl
          | some p =>
              obtain ⟨l, v, vs, doms⟩ := p
              simp only [hl, hs] at hsucc
              split at hsucc
              · rw [successor_decide] at hsucc
                cases hsucc
                exact canonicalCfg_same h rfl rfl
              · rw [successor_decide] at hsucc
                cases hsucc
                exact canonicalCfg_same h rfl rfl
    · have hlearned := terminalResult_payload_canonical hp h.db ht
      rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep, successor_localExclude] at hsucc
          cases hsucc
          exact canonicalCfg_none (databaseCanonical_append hlearned h.db) rfl
      | cons c rest =>
          by_cases hz : cfg.branch.level = 0
          · simp [conflictStep, hz] at hsucc
          · simp only [conflictStep, if_neg hz, successor_analyzeConflict] at hsucc
            cases hsucc
            exact canonicalCfg_countResolutions (canonicalCfg_analyze h c learned hlearned) _
    · exact absurd ht terminalResult_ne_localExcluded

/-- Initial clause syntax and canonical emissions suffice for canonicality
throughout every actual supported run; no run-level conclusion is a premise. -/
theorem canonicalCfg_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hdb : DatabaseCanonical original) (hp : EmissionCanonical props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → CanonicalCfg cfg := by
  intro cfg hr
  induction hr with
  | init hent => exact canonicalCfg_none hdb rfl
  | step hr hs ih =>
      obtain ⟨_, _, hpr⟩ := SupportedReach.triple_eq hr
      exact canonicalCfg_step ih (by rw [hpr]; exact hp) hs

/-- The clamped registered kit derives the syntax invariant directly from
its family gate and normalized original clauses. Compiled originals are empty. -/
theorem canonicalCfg_of_families {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause}
    {dcs : List LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint}
    (hdb : DatabaseCanonical original)
    (hfam : ∀ dc ∈ dcs, LeanFzn.Solver.UIP.LcgFamilies.lcgFamB dc = true) :
    ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original
        (clampProps orig (dcs.filterMap propagatorOfProved)) cfg → CanonicalCfg cfg :=
  canonicalCfg_of_supportedRun hdb
    (clampProps_canonical orig (LcgCanonicalFamilies.emissionCanonical_of_families hfam))

end LeanFzn.Solver.UIP.LcgCanonicalScheduler
