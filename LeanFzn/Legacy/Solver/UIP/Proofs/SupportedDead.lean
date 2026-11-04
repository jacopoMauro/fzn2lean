/-
File: LeanFzn/Solver/UIP/Proofs/SupportedDead.lean

Purpose: the E1 dead-site layer at S1's root-indexed execution. Everything
is indexed by `SupportedReach orig original props`, so each hypothesis is a
fact about exactly one supported run:

  §1 `supportedFrameDead_of_recordedEvidence` — the frame of a supported
     configuration carrying RECORDED conflict evidence is dead (`hclos` +
     `hbr` only; the analysis is irrelevant, so ONE lemma discharges both
     `hdeadFallbackNone` and `hdeadFallbackNoCp`).
  §2 `supportedHdeadStableNone_of_shape` — the stable-none site's deadness
     (`stableNone_dead` with the unsupported-head case REFUTED by the run's
     shape discipline, not assumed).
  §3 `supportedHlent_of_hbr` — the database-entailment fact the UNSAT
     wrapper consumes, from the branch invariant's `WellFormed` conjunct.
  §4 `supportedDeadEvidence_of_premises` — `SupportedDeadEvidence` for the
     run: the status induction over the real dispatcher trees.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedDead` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRunAssembly
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDeadSites
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedProviders
import LeanFzn.Legacy.Solver.UIP.Proofs.UnitRunSupported
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C2d
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.RunAssembly

/-! ## §1 Recorded-evidence frame deadness -/

/-- **THE RECORDED-EVIDENCE DEADNESS PRODUCER**: at a supported
configuration whose conflict evidence is recorded, the branch frame holds
no leaf solution. The route analysis over the dispatcher trees shows the
evidence is RECORDED only at the analyze site (`conflictStep`'s nonempty,
non-level-0 arm), whose branch is the terminal conflict's branch; every
other arm clears the evidence (contradiction) and the analyze site
produces the deadness via `frameDead_of_terminalConflict` at the
pre-state. Neither the analysis nor the checkpoint lookup is used. -/
theorem supportedFrameDead_of_recordedEvidence {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  intro cfg hreach
  induction hreach with
  | init =>
      intro ev hconf
      exact absurd hconf (by simp [SchedulerConfig.init])
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      intro ev hconf
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev₀, hc₀, hnev⟩ | ⟨hconf₀, hdead₀, hnc⟩ | ⟨hconf₀, hact₀, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep) — clears everywhere
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev₀.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            rw [stepChronologicalFallback_conflict] at hconf
            cases hconf
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                rw [stepChronologicalFallback_conflict] at hconf
                cases hconf
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    rw [stepLocalExclude_conflict] at hconf
                    cases hconf
                | some restored =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    rw [stepLearnBackjumpAssert_conflict] at hconf
                    cases hconf
      · -- ===== ROUTE 2: dead branch — the consume route clears
        rw [hnc] at hs
        unfold consumeStep at hs
        split at hs
        · rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          rw [stepConsume_conflict hcs] at hconf
          cases hconf
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate — the conflict field is unchanged; the
          -- narrowed frame descends from the branch frame, so the
          -- predecessor's deadness transfers
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          rw [stepPropagate_conflict] at hconf
          intro a ha hcov
          exact ih hconf a ha (filterFrame_refines d.filtered
            (by simpa [stepPropagate, narrowState] using hcov))
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l k v vs hsp
              split at hs
              · -- SKIP arm — the conflict field is unchanged; the pinned
                -- child descends from the parent frame
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                rw [stepDecideSkip_conflict] at hconf
                intro a ha hcov
                exact ih hconf a ha
                  (covers_parent_of_covers_pinChild hsp a hcov)
              · -- FRESH arm — the conflict field is unchanged; the pinned
                -- child descends from the parent frame
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                rw [stepDecide_conflict] at hconf
                intro a ha hcov
                exact ih hconf a ha
                  (covers_parent_of_covers_pinChild hsp a hcov)
            · -- no split data: localExclude (clears)
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              rw [stepLocalExclude_conflict] at hconf
              cases hconf
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              -- empty clause list: local exclusion (clears)
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              rw [stepLocalExclude_conflict] at hconf
              cases hconf
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: terminal, no successor
                simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- THE RECORDING SITE: the recorded config IS the terminal
                -- conflict's branch (unchanged), so the predecessor's
                -- terminal event proves the deadness — the analysis
                -- (present or absent) is irrelevant.
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
                exact frameDead_of_terminalConflict (hclos hrec) (hbr hrec)
                  (by rw [← SupportedReach.orig_eq hrec]; exact ht)
        · -- ARM 6: localExcluded → localExclude (clears)
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          rw [stepLocalExclude_conflict] at hconf
          cases hconf

/-! ## §2 The stable-none deadness producer -/

/-- **THE STABLE-NONE DEADNESS PRODUCER**: `stableNone_dead` with its
unsupported-head case REFUTED by the run's shape discipline (no box domain
can carry a `setOfInt`/`array` value at a reachable head slot), so no
fragment conditional remains. -/
theorem supportedHdeadStableNone_of_shape {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf},
      SupportedReach orig original props cfg →
      terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs →
      leafWitness leaf cfg = none →
      splitData cfg.branch.frame cfg.prio = none →
        ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  intro cfg bs hreach _ hwit hsp
  exact stableNone_dead hwit hsp
    (fun h => absurd h (unsupportedHead_absent_of_shape hshape (hbr hreach)))

/-! ## §3 The database-entailment producer -/

/-- **THE `hlent` PRODUCER**: the database-entailment fact the supported
UNSAT wrapper consumes is the `WellFormed` conjunction of the branch
invariant — no residual. -/
theorem supportedHlent_of_hbr {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LearnedEntailed leaf cfg.branch.learned :=
  fun hreach => (hbr hreach).wf.2.2.2.2

/-! ## §4 The supported dead-evidence producer -/

/-- **THE `SupportedDeadEvidence` PRODUCER**: every supported dead
configuration's frame holds no leaf solution. Induction over the real
dispatcher trees: route 1's fallback and rejection arms and the route-3
local-exclusion and analyze arms close with §1/§2 and the existing
terminal-event producers; every arm whose successor is `.active` is
refuted by the successor's status. -/
theorem supportedDeadEvidence_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    SupportedDeadEvidence orig original props leaf := by
  intro d hreach
  induction hreach with
  | init =>
      intro hstatus
      exact absurd hstatus (by simp [SchedulerConfig.init])
  | step hrec hs ih =>
      clear d
      rename_i cfg cfg'
      intro hstatus
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev₀, hc₀, hnev⟩ | ⟨hconf₀, hdead₀, hnc⟩ | ⟨hconf₀, hact₀, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev₀.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
            exact supportedFrameDead_of_recordedEvidence hclos hbr hrec hc₀
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
                exact supportedFrameDead_of_recordedEvidence hclos hbr hrec hc₀
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
                    exact supportedFrameDead_of_recordedEvidence hclos hbr hrec hc₀
                | some restored =>
                    -- the jump successor is active
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    simp [stepLearnBackjumpAssert] at hstatus
      · -- ===== ROUTE 2: dead branch — the consume route resumes ACTIVE
        rw [hnc] at hs
        unfold consumeStep at hs
        split at hs
        · rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest =>
              have hst : next.status = .active := by
                unfold stepConsume at hcs
                rw [hpend] at hcs
                injection hcs with hnext
                subst hnext
                rfl
              rw [hst] at hstatus
              cases hstatus
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate — successor is active
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          simp [stepPropagate] at hstatus
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · -- name the witness-failure fact for the stable-none producer
            rename_i hwn
            split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l k v vs hsp
              split at hs
              · -- SKIP arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                simp [stepDecideSkip] at hstatus
              · -- FRESH arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                simp [stepDecide] at hstatus
            · -- no split data: localExclude with stable-none deadness
              rename_i hsp
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
              exact supportedHdeadStableNone_of_shape hshape hbr hrec ht hwn hsp
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              -- empty clause list: local exclusion with the nil-conflict
              -- deadness at the terminal event
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
              exact deadConflictNil_of_terminalEvent (hclos hrec) (hbr hrec)
                (by rw [← SupportedReach.orig_eq hrec]; exact ht) rfl
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: terminal, no successor
                simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site: successor status = predecessor's = active
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                have hcontra : cfg.status = .dead := by
                  simpa [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                    SchedulerConfig.countResolutions] using hstatus
                rw [hact₀] at hcontra
                cases hcontra
        · -- ARM 6: localExcluded → localExclude with the localExcluded
          -- deadness at the terminal event
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          show ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
          exact deadLocalExcluded_of_terminalEvent (hclos hrec) (hbr hrec)
            (by rw [← SupportedReach.orig_eq hrec]; exact ht)

/-! ## §5 The supported core-gate assembly (exact residual view) -/

/-- **THE SUPPORTED CORE-GATE ASSEMBLY**: every `SupportedArmInvGatesCore`
field that has a landed producer is DISCHARGED here; the remaining fields
are exactly the named premises. This is the honest residual interface the
I1 joint-invariant task consumes (session-12 update: the premises are now
EIGHT — `hshape`, `hclos`, `hunit`, `hpay`, `hplanU`, `hpre`, `hdeadCkpt`,
`hconsumeInv` — `hconsume` was DROPPED, see below):

  * `hbr`, `hentEv` AND the run's `PendingSideInv` are NO LONGER premises:
    the TRIPLE joint induction
    `supportedReachAndEvidence_of_premises` (Proofs/SupportedArms.lean §0)
    produces `ReachableState ∧ hentEv ∧ PendingSideInv` at once (the
    consume arm derives the resumed reachability internally from
    `stepConsume_reachable_of_inv` + the paired pending invariant), and
    `hconsume` is then DERIVED by `supportedHconsume_of_premises`
    (Proofs/PendingRun.lean) from the joint reachability component — the
    former `hconsume ← hbr ← hconsume` cycle is gone;
  * `hclos` — P1 (compiled closure contract; premise-free producer
    `supportedHclos_of_compiled`);
  * `hunit`, `hpay`, `hplanU` — P1 round-2 unit-discipline gates.
    HONEST SUPPLY (N1, at the supported index):
    `hunit ← (unitRunInvariant_of_reachable hSupp hreach.reachable
    hprops).db` (Proofs/SchedulerConflict.lean; `UnitLearned` transports
    to `UnitDB` by defeq); `hplanU ←` the recorded-evidence component
    `(unitRunInvariant_of_reachable …).recorded ev hc` together with the
    singleton-analysis lemma `unitLearned_ofUIP_normalized_of_singleton`
    (`reachable_analysis_success` gives the recorded analysis is
    `(ofUIP …).normalized`, so `an.learned = [q']` normalized; any
    `ev.clause`/`an.learned` bridge is a separate small lemma, NOT
    assumed here); `hpay ← unitPayload_of_unitKit
    (unitRunProfile_proved dcs hSupp)` (transport `original`/`props` by
    the run's equations when needed). These supplies belong to the FINAL
    instantiation site; they are premises here, never invented;
  * `hpre` — J1: now SUCCESS-GUARDED at the actual `perform = some`
    event and carrying the per-site branch reachability (the
    rejection-free shape was uninhabitable at rejecting sites). Its
    producer is `supportedHpre_of_premises` (SupportedProviders §3-bis,
    proved from the chain push bundle and the named site obligations:
    certificate, normalization stability, surviving prefix, enqueue
    freshness, in-range asserting literal);
  * `hident` — J1 (checkpoint identity; produced by
    `supportedHident_of_premises`);
  * `hdeadCheckpointRegion` — E1 residual (rejection premise now part of
    the field; certificate + snapshot producers landed as
    `supportedHdeadCheckpointRegion_of_premises`; `hsurv` remains);
  * `hconsumeInv` — R2's last residual: the consume successor's
    `SchedulerInvariant`. Available: `reachable`
    (`stepConsume_reachable_of_inv`), `checkpoints_identify` (vacuous —
    the consume empties the checkpoint list), `pending_fits`/`branch_fits`
    (the paired `PendingSideInv`'s backing), `coverage`
    (`stepConsume_coverage` + the site's dead evidence), `learned_entailed`
    (`hbr`'s `wf`). MISSING: `log_sound`, which needs the run-level
    producer `∀ cfg, SupportedReach … cfg → ExhaustionLog.Sound leaf
    cfg.log` (an induction over the run whose registration arms consume
    the dead-site gates). -/
theorem supportedCoreGates_of_producers {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig cfg.original cfg.props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch)
    (hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp))
    (hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame},
      SupportedReach orig original props cfg →
      cfg.status = .dead →
      cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next) :
    SupportedArmInvGatesCore orig original props leaf := by
  have hclosF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig original props :=
    fun {cfg} hreach => by
      rw [← SupportedReach.original_eq hreach,
        ← SupportedReach.props_eq hreach]
      exact hclos hreach
  have J : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig cfg :=
    supportedReachAndEvidence_of_premises hclosF hunit hpay hplanU
    (supportedPinGates_of_shape hshape).hpin
    (supportedPinGates_of_shape hshape).hskip
    hpre hshape
  have hbrF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch :=
    fun hreach => (J hreach).1
  have hconsumeF : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame},
      SupportedReach orig original props cfg →
      cfg.pending = f :: rest → stepConsume cfg = some next →
        ReachableState leaf orig next.branch :=
    supportedHconsume_of_premises hshape hbrF (fun hreach => (hclosF hreach).leafFits)
  exact
  { hclos := hclosF
    hunit := hunit
    hpay := hpay
    hplanU := hplanU
    hlevel := supportedHlevel_of_reach
    hpin := (supportedPinGates_of_shape hshape).hpin
    hskip := (supportedPinGates_of_shape hshape).hskip
    hpinSkip := (supportedPinGates_of_shape hshape).hpinSkip
    hentEv := fun hreach hconf => (J hreach).2.1 hconf
    hpre := hpre
    hident := supportedHident_of_premises
    hbc := fun hreach hconf hana hcp hperf =>
      supportedHbc_of_recorded_analysis hbrF
        hreach hconf hana hcp hperf
    hdeadStableNone := fun hreach ht hw hsp =>
      supportedHdeadStableNone_of_shape hshape hbrF
        hreach ht hw hsp
    hdeadFallbackNone := fun hreach hconf _ =>
      supportedFrameDead_of_recordedEvidence hclos hbrF
        hreach hconf
    hdeadFallbackNoCp := fun hreach hconf _ _ =>
      supportedFrameDead_of_recordedEvidence hclos hbrF
        hreach hconf
    hdeadCheckpointRegion := hdeadCkpt
    hconsumeInv := hconsumeInv
    hconsume := hconsumeF }

/-! ## §6 The N1 supply of the unit trio

The P1 repair gates the closure's learned-dependent fields by `UnitDB`;
the three facts the gate records carry (`hunit`, `hpay`, `hplanU`) are NOT
assumed anywhere — they are the unit kit's own run facts, supplied here
from N1 (`unitRunInvariant_of_reachable`) for any supported run whose
props are the kit image (`props = dcs.filterMap propagatorOfProved` with
every `unitFamilyB dc = true`). A caller with the kit equation discharges
the trio with these three lemmas. -/

/-- N1 supplies the unit-database discipline at the supported index. -/
theorem supportedHunit_of_unitRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hgate : UnitKitGate (leaf := leaf) orig original props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      UnitDB cfg.branch.learned :=
  fun hreach =>
    (unitRunInvariant_of_supported hprops hSupp hgate hreach).db

/-- The kit profile supplies the deduction-payload maintenance. -/
theorem supportedHpay_of_unitRun {original : List Clause}
    {props : List Propagator} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    UnitPayload original props := by
  rw [hprops]
  exact unitPayload_of_unitKit (unitRunProfile_proved dcs hSupp)

/-- The recorded evidence's stored analysis is a normalized unit (N1's
singleton-analysis lemma at the recorded event). -/
theorem supportedHplanU_of_unitRun {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hgate : UnitKitGate (leaf := leaf) orig original props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → UnitDB [an.learned] := by
  intro cfg ev an hreach hc ha
  obtain ⟨⟨q, hq, hqn⟩, -⟩ :=
    (unitRunInvariant_of_supported hprops hSupp hgate hreach).recorded ev hc
  obtain ⟨below, uip, hrun, heq⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  rw [hq] at hrun
  obtain ⟨q', hq', hqn'⟩ := unitLearned_ofUIP_normalized_of_singleton hrun
  intro c hc'
  rw [List.mem_singleton] at hc'
  subst hc'
  exact ⟨q', by rw [heq, hq'], hqn'⟩

end LeanFzn.Solver.UIP
