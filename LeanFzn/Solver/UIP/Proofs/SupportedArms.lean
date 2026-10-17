/-
File: LeanFzn/Solver/UIP/Proofs/SupportedArms.lean

Purpose: the supported-run arm assemblies. This module ports B4's per-arm
assembly bodies to S1's root-indexed execution (`SupportedReach orig
original props`), consuming the frozen gate records of `SupportedGates`:

  §1 `supportedArmsPreserveReach_of_gates` — the §5 body of
     `SchedulerArmsPreserve.lean` with the index substituted
     (`SchedulerReachable` → `SupportedReach orig original props`), so the
     per-arm successor preservation is DERIVED from `SupportedArmGates` on
     exactly one supported run.
  §2 `supportedHbr_of_gates` / `supportedBranchInvariant_of_gates` — the
     composed `hbr` output (branch invariant of the supported run) that
     S2/B4 consumers take.
  §3 `SupportedArmInvGatesCore.toSupportedArmInvGates` — fills the two
     dead-site fields with the axiom-clean `SchedulerDeadSites` producers at
     the fixed run triple (their signatures already use `ReachableState leaf
     orig cfg.branch`, so no conversion is needed).
  §4 `SupportedArmInvGates.coreGates` — the 6-field projection (the shared
     gates) so ONE record serves both assemblies.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedArms` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedGates
import LeanFzn.Solver.UIP.Proofs.SchedulerDeadSites
import LeanFzn.Solver.UIP.Proofs.PendingRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §0 The joint reachability/evidence induction (I1 cycle-breaker)

`hentEv`'s only producer needs `hbr` (at the recording site's pre-state) and
`hbr`'s only route needs `hentEv` (jump/localExclude arms) — a genuine
cycle if each is produced separately. ONE induction over the supported run
produces BOTH components jointly, each arm consuming the paired hypothesis
at the immediate predecessor. The step's external premises are the gate
fields `{hclos, hunit, hpay, hplanU, hpin, hskip, hpre, hconsume}` (the
unit-discipline triple is the P1 round-2 repair gate). -/

/-- **THE JOINT STEP**: one dispatcher step preserves the joint invariant
(branch reachability ∧ recorded-evidence entailment). The reach half is the
§1 arm body; the evidence half records/keeps/refutes the evidence exactly
as the `hentEv` producer does, but reads the pre-state's reachability from
the paired hypothesis instead of a global `hbr`. -/
theorem supportedStepReachAndEvidence_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = false →
        ∀ a : Assignment, Assignment.Fits orig a →
          (l.norm.eval a = some true ↔
            a[cfg.branch.frame.2.length]? = some v))
    (hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = true →
        DecideSkipPrefixTyped orig cfg v)
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
    (hshape : ShapeTypedDomains orig)
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg')
    (ih : ReachableState leaf orig cfg.branch ∧
      (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        LearnedEntailed leaf ev.learned) ∧ PendingSideInv orig cfg) :
    ReachableState leaf orig cfg'.branch ∧
      (∀ {ev : ConflictEvidence}, cfg'.conflict = some ev →
        LearnedEntailed leaf ev.learned) ∧ PendingSideInv orig cfg' := by
  have hs' : (schedulerNext cfg).successor = some cfg' := hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (backjumpStep)
    rw [hnext] at hsucc
    unfold backjumpStep at hsucc
    cases ha : ev.analysis with
    | none =>
        -- no analysis → fallback stutter (branch unchanged)
        rw [ha] at hsucc
        simp only [] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        subst hsucc
        refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
        intro ev' hconf'
        rw [stepChronologicalFallback_conflict] at hconf'
        cases hconf'
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- no checkpoint → fallback stutter
            rw [ha] at hsucc
            simp only [] at hsucc
            rw [hcp] at hsucc
            simp only [] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq]
              at hsucc
            subst hsucc
            refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
            intro ev' hconf'
            rw [stepChronologicalFallback_conflict] at hconf'
            cases hconf'
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                -- perform rejected → localExclude with the recorded payload
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_localExclude, Option.some.injEq] at hsucc
                subst hsucc
                refine ⟨reachable_prepend_learned ih.1 (ih.2.1 hc), ?_,
                  pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
                intro ev' hconf'
                rw [stepLocalExclude_conflict] at hconf'
                cases hconf'
            | some restored =>
                -- the recorded jump (S3 pre-reachability + S4 payload
                -- entailment); the raw lemma is self-relative, so its
                -- cfg.orig-indexed inputs are reached through the
                -- supported frame equalities.
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_learnBackjumpAssert, Option.some.injEq]
                  at hsucc
                subst hsucc
                have hres := stepLearnBackjumpAssert_branch_reachable hreach.reachable
                  (by rw [SupportedReach.orig_eq hreach]; exact ih.1)
                  (by rw [SupportedReach.orig_eq hreach,
                          SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hclos hreach)
                  (by rw [SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hpay)
                  (hunit hreach) (hplanU hreach hc ha)
                  hc ha hcp hp
                  (by rw [SupportedReach.orig_eq hreach]
                      exact hpre hreach ih.1 hc ha hcp hp)
                  (ih.2.1 hc)
                  (by show (schedulerNext cfg).successor = some
                        (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                            an.learned) ev restored)
                      rw [hnext]
                      unfold backjumpStep
                      rw [ha]
                      simp only []
                      rw [hcp]
                      simp only []
                      rw [hp]
                      simp only []
                      simp only [successor_learnBackjumpAssert])
                rw [SupportedReach.orig_eq hreach] at hres
                refine ⟨hres, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
                intro ev' hconf'
                rw [stepLearnBackjumpAssert_conflict] at hconf'
                cases hconf'
  · -- ===== ROUTE 2: dead branch — the consume route
    rw [hnext] at hsucc
    unfold consumeStep at hsucc
    split at hsucc
    · -- resumed: the gate supplies the resumed branch's reachability
      rename_i next hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      subst hsucc
      cases hpend : cfg.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
          cases hcs
      | cons f rest =>
          have hres := stepConsume_reachable_of_inv hpend hcs ih.1 ih.2.2
            (SupportedReach.orig_eq hreach) (hclos hreach).leafFits
          refine ⟨hres, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
          intro ev' hconf'
          rw [stepConsume_conflict hcs] at hconf'
          cases hconf'
    · -- frontier exhausted: no successor
      simp only [successor_unsat] at hsucc
      exact absurd hsucc (by simp)
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate (closure contract + the deduction's own evidence)
      rw [hnext] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      subst hsucc
      have hd' : explainedDeduction original props cfg.branch = some d := by
        rw [← SupportedReach.original_eq hreach, ← SupportedReach.props_eq hreach]
        exact hd
      refine ⟨stepPropagate_branch_reachable d (SupportedReach.orig_eq hreach)
        (hclos hreach).leafFits (explainedDeduction_narrow_reachable (hclos hreach) ih.1
        (hunit hreach) hd'), ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
      intro ev' hconf'
      rw [stepPropagate_conflict] at hconf'
      exact ih.2.1 hconf'
    · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
      rw [hnext] at hsucc
      unfold stableStepGuarded at hsucc
      split at hsucc
      · -- witness: terminal, no successor
        simp only [successor_sat] at hsucc
        cases hsucc
      · split at hsucc
        · -- split data: fresh decision or redundant-pin skip
          rename_i l v vs doms hsp
          split at hsucc
          · -- SKIP arm: stepDecideSkip; Bool closed, non-Bool via `hskip`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            refine ⟨?_, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
            · cases v with
              | bool b =>
                  exact reachable_decideSkip_bool ih.1 hsp (by assumption)
              | int i =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
              | setOfInt s =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
              | array a =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
            · intro ev' hconf'
              rw [stepDecideSkip_conflict] at hconf'
              exact ih.2.1 hconf'
          · -- FRESH arm: stepDecide; Bool closed, non-Bool via `hpin`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            have hred' : TrailRedundant cfg.branch.trail l = false := by
              cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
            refine ⟨?_, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
            · cases v with
              | bool b =>
                  have hwl := (splitData_eq_some_iff.mp hsp).2
                  refine reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) ?_ (not_trailRedundant_iff.mp hred')
                  intro a _
                  rw [Literal.norm_eval]
                  simpa using valueLiteral_holds_iff hwl a
              | int i =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
              | setOfInt s =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
              | array a =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
            · intro ev' hconf'
              rw [stepDecide_conflict] at hconf'
              exact ih.2.1 hconf'
        · -- no split data: localExclude with the EMPTY payload
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          refine ⟨reachable_prepend_learned ih.1 (by intro c hc'; simp at hc'), ?_,
            pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
          intro ev' hconf'
          rw [stepLocalExclude_conflict] at hconf'
          cases hconf'
    · -- ARM 8 / ARM 4: the conflict dispatch
      cases cs with
      | nil =>
          -- empty clause list: local exclusion with the payload; the
          -- entailment comes from `terminalResult_spec` + `hclos`
          rw [hnext] at hsucc
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          have hspec := terminalResult_spec (hclos hreach) ih.1
          rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach,
            SupportedReach.props_eq hreach] at ht
          rw [ht] at hspec
          refine ⟨reachable_prepend_learned ih.1
            (fun c hc' a ha =>
              hspec.entailed c hc' c (List.mem_singleton_self c) a ha), ?_,
            pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
          intro ev' hconf'
          rw [stepLocalExclude_conflict] at hconf'
          cases hconf'
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- level 0: root contradiction, no successor
            rw [hnext] at hsucc
            simp only [conflictStep, if_pos hlv, successor_unsat] at hsucc
            cases hsucc
          · -- recorded analyze site: branch unchanged
            rw [hnext] at hsucc
            simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hsucc
            subst hsucc
            refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
            intro ev' hconf'
            rw [stepAnalyzeConflictCounted_conflict] at hconf'
            injection hconf' with hev
            subst hev
            have hspec := terminalResult_spec (hclos hreach) ih.1
            rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach,
              SupportedReach.props_eq hreach] at ht
            rw [ht] at hspec
            exact fun c' hc' a ha =>
              hspec.entailed c' hc' c' (List.mem_singleton_self c') a ha
    · -- ARM 6: localExcluded → localExclude with the payload (spec entailment)
      rw [hnext] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      have hspec := terminalResult_spec (hclos hreach) ih.1
      rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach,
        SupportedReach.props_eq hreach] at ht
      rw [ht] at hspec
      refine ⟨reachable_prepend_learned ih.1
        (fun c hc' a ha =>
          hspec.entailed c hc' c (List.mem_singleton_self c) a ha), ?_,
        pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2⟩
      intro ev' hconf'
      rw [stepLocalExclude_conflict] at hconf'
      cases hconf'

/-- **THE JOINT INVARIANT PRODUCER (I1)**: one induction over the supported
run yields BOTH `hbr` (branch reachability) and `hentEv` (recorded-evidence
entailment) — the acyclic replacement of the mutually dependent
`supportedHentEv_of_premises`/`supportedHbr_of_gates` pair. External
premises: the gate fields `{hclos, hunit, hpay, hplanU, hpin, hskip,
hpre, hconsume}` (the unit-discipline triple is the P1 round-2 repair
gate). -/
theorem supportedReachAndEvidence_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = false →
        ∀ a : Assignment, Assignment.Fits orig a →
          (l.norm.eval a = some true ↔
            a[cfg.branch.frame.2.length]? = some v))
    (hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = true →
        DecideSkipPrefixTyped orig cfg v)
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
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig cfg := by
  intro cfg hreach
  induction hreach with
  | init hent =>
      exact ⟨reachable_seed leaf orig original hent,
        (fun {ev} hconf => absurd hconf (by simp [SchedulerConfig.init])),
        PendingSideInv.init orig original props⟩
  | step hrec hs ih =>
      exact supportedStepReachAndEvidence_of_premises hclos hunit hpay hplanU
        hpin hskip hpre hshape hrec hs ih

/-! ## §1 The supported per-arm assembly (§5 port) -/

/-- **SUPPORTED B4 ARM ASSEMBLY**: the reach-aware successor invariant on
ONE supported run, derived from the supported per-arm gates. Body copied
from `reachableArmsPreserveReach_of_gates` (§5 of
`SchedulerArmsPreserve.lean`) with the index substituted; the gates are the
`SupportedArmGates` fields, whose hypotheses are exactly the supported
index available at each site. -/
theorem supportedArmsPreserveReach_of_gates {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hg : SupportedArmGates orig original props leaf) :
    SupportedArmsPreserveReach orig original props leaf := by
  intro cfg cfg' hreach hsucc hbs
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (backjumpStep)
    rw [hnext] at hsucc
    unfold backjumpStep at hsucc
    cases ha : ev.analysis with
    | none =>
        -- no analysis → fallback stutter (branch unchanged)
        rw [ha] at hsucc
        simp only [] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        subst hsucc
        exact hbs
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- no checkpoint → fallback stutter
            rw [ha] at hsucc
            simp only [] at hsucc
            rw [hcp] at hsucc
            simp only [] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
            subst hsucc
            exact hbs
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                -- perform rejected → localExclude with the recorded payload
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_localExclude, Option.some.injEq] at hsucc
                subst hsucc
                exact reachable_prepend_learned hbs (hg.hentEv hreach hc)
            | some restored =>
                -- the recorded jump (S3 pre-reachability + S4 payload
                -- entailment); `hsucc` is re-derived from the dispatcher
                -- equation (the local copy was unfolded above). The raw
                -- lemma is self-relative, so its `cfg.orig`-indexed inputs
                -- are reached through the supported frame equalities.
                have hres := stepLearnBackjumpAssert_branch_reachable hreach.reachable
                  (by rw [SupportedReach.orig_eq hreach]; exact hbs)
                  (by rw [SupportedReach.orig_eq hreach,
                          SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hg.hclos hreach)
                  (by rw [SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hg.hpay)
                  (hg.hunit hreach) (hg.hplanU hreach hc ha)
                  hc ha hcp hp
                  (by rw [SupportedReach.orig_eq hreach]
                      exact hg.hpre hreach hbs hc ha hcp hp)
                  (hg.hentEv hreach hc)
                  (by show (schedulerNext cfg).successor = some cfg'
                      rw [hnext]
                      exact hsucc)
                rwa [SupportedReach.orig_eq hreach] at hres
  · -- ===== ROUTE 2: dead branch — the consume route
    rw [hnext] at hsucc
    unfold consumeStep at hsucc
    split at hsucc
    · -- resumed: the gate supplies the resumed branch's reachability
      rename_i next hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      subst hsucc
      cases hpend : cfg.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
          cases hcs
      | cons f rest => exact hg.hconsume hreach hpend hcs
    · -- frontier exhausted: no successor
      simp only [successor_unsat] at hsucc
      exact absurd hsucc (by simp)
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate (closure contract + the deduction's own evidence)
      rw [hnext] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      subst hsucc
      have hd' : explainedDeduction original props cfg.branch = some d := by
        rw [← SupportedReach.original_eq hreach, ← SupportedReach.props_eq hreach]
        exact hd
      exact stepPropagate_branch_reachable d (SupportedReach.orig_eq hreach)
        (hg.hclos hreach).leafFits (explainedDeduction_narrow_reachable (hg.hclos hreach) hbs
        (hg.hunit hreach) hd')
    · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
      rw [hnext] at hsucc
      unfold stableStepGuarded at hsucc
      split at hsucc
      · -- witness: terminal, no successor
        simp only [successor_sat] at hsucc
        cases hsucc
      · split at hsucc
        · -- split data: fresh decision or redundant-pin skip
          rename_i l v vs doms hsp
          split at hsucc
          · -- SKIP arm: stepDecideSkip; Bool closed, non-Bool via `hskip`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            cases v with
            | bool b =>
                exact reachable_decideSkip_bool hbs hsp (by assumption)
            | int i =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hbs hsp (by assumption))
            | setOfInt s =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hbs hsp (by assumption))
            | array a =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hbs hsp (by assumption))
          · -- FRESH arm: stepDecide; Bool closed, non-Bool via `hpin`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            have hred' : TrailRedundant cfg.branch.trail l = false := by
              cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
            cases v with
            | bool b =>
                have hwl := (splitData_eq_some_iff.mp hsp).2
                refine reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) ?_ (not_trailRedundant_iff.mp hred')
                intro a _
                rw [Literal.norm_eval]
                simpa using valueLiteral_holds_iff hwl a
            | int i =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hbs hsp hred')
                  (not_trailRedundant_iff.mp hred')
            | setOfInt s =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hbs hsp hred')
                  (not_trailRedundant_iff.mp hred')
            | array a =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hbs hsp hred')
                  (not_trailRedundant_iff.mp hred')
        · -- no split data: localExclude with the EMPTY payload
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          exact reachable_prepend_learned hbs (by intro c hc; simp at hc)
    · -- ARM 8 / ARM 4: the conflict dispatch
      cases cs with
      | nil =>
          -- empty clause list: local exclusion with the payload; the
          -- entailment comes from `terminalResult_spec` + `hclos`
          rw [hnext] at hsucc
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          have hspec := terminalResult_spec (hg.hclos hreach) hbs
          rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach,
            SupportedReach.props_eq hreach] at ht
          rw [ht] at hspec
          exact reachable_prepend_learned hbs
            (fun c hc a ha =>
              hspec.entailed c hc c (List.mem_singleton_self c) a ha)
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- level 0: root contradiction, no successor
            rw [hnext] at hsucc
            simp only [conflictStep, if_pos hlv, successor_unsat] at hsucc
            cases hsucc
          · -- recorded analyze site: branch unchanged
            rw [hnext] at hsucc
            simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hsucc
            subst hsucc
            exact hbs
    · -- ARM 6: localExcluded → localExclude with the payload (spec entailment)
      rw [hnext] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      have hspec := terminalResult_spec (hg.hclos hreach) hbs
      rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach,
        SupportedReach.props_eq hreach] at ht
      rw [ht] at hspec
      exact reachable_prepend_learned hbs
        (fun c hc a ha =>
          hspec.entailed c hc c (List.mem_singleton_self c) a ha)

/-! ## §2 The composed `hbr` output -/

/-- THE B4 `hbr` OUTPUT ON A SUPPORTED RUN: the branch invariant follows
from the supported gates (assembly + induction). This is the shape the
supported progress premises (`hbr` of
`supportedPhaseProgressSorted_of_premises`) consume. -/
theorem supportedBranchInvariant_of_gates {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hg : SupportedArmGates orig original props leaf) :
    SupportedBranchInvariant orig original props leaf :=
  supportedReachableBranch_of_preserve (supportedArmsPreserveReach_of_gates hg)

/-- The `hbr` premise shape of the supported progress instance. -/
theorem supportedHbr_of_gates {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hg : SupportedArmGates orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch :=
  fun h => supportedBranchInvariant_of_gates hg h

/-! ## §3 The full supported record from the residual core -/

/-- **SUPPORTED RECORD PRODUCER**: the full `SupportedArmInvGates` from the
15-field `SupportedArmInvGatesCore`. The two dead-site fields are DISCHARGED
by the axiom-clean `SchedulerDeadSites` producers, whose signatures already
use `ReachableState leaf orig cfg.branch` at the fixed run triple. -/
theorem SupportedArmInvGatesCore.toSupportedArmInvGates {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hc : SupportedArmInvGatesCore orig original props leaf) :
    SupportedArmInvGates orig original props leaf where
  core := hc
  hunit := hc.hunit
  hpay := hc.hpay
  hplanU := hc.hplanU
  hdeadConflictNil := fun hreach hbs ht hcs => by
    rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach, SupportedReach.props_eq hreach] at ht
    exact deadConflictNil_of_terminalEvent (hc.hclos hreach) hbs ht hcs
  hdeadLocalExcluded := fun hreach hbs ht => by
    rw [SupportedReach.orig_eq hreach, SupportedReach.original_eq hreach, SupportedReach.props_eq hreach] at ht
    exact deadLocalExcluded_of_terminalEvent (hc.hclos hreach) hbs ht

/-! ## §4 The shared-gate projection (ONE record, both assemblies) -/

/-- The 6-field projection of the supported core: the shared gates that
`supportedArmsPreserveReach_of_gates` consumes. -/
def SupportedArmInvGatesCore.coreGates {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hc : SupportedArmInvGatesCore orig original props leaf) :
    SupportedArmGates orig original props leaf where
  hclos := hc.hclos
  hunit := hc.hunit
  hpay := hc.hpay
  hplanU := hc.hplanU
  hentEv := hc.hentEv
  hpin := hc.hpin
  hskip := hc.hskip
  hpre := hc.hpre
  hconsume := hc.hconsume

/-- The `hbr` output from the residual core alone (both projections
composed). -/
theorem supportedBranchInvariant_of_core {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hc : SupportedArmInvGatesCore orig original props leaf) :
    SupportedBranchInvariant orig original props leaf :=
  supportedBranchInvariant_of_gates hc.coreGates

/-! ## §5 The supported invariant-discipline assembly (§6 port) -/

/-- **SUPPORTED B4 INVARIANT-DISCIPLINE ASSEMBLY**: the invariant
discipline on ONE supported run (`∀ cfg, SupportedReach … cfg →
SchedulerInvariant cfg`) derived from the supported gate record by induction
over the supported reachability tree. Body copied from
`reachableInvariantDiscipline_of_gates` (§6 of `SchedulerArmsPreserve.lean`)
with the index substituted and the run's frame equalities threaded at the
raw-lemma call sites. -/
theorem supportedInvariantDiscipline_of_gates {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hg : SupportedArmInvGates orig original props leaf) :
    ∀ (cfg : SchedulerConfig leaf),
      SupportedReach orig original props cfg → SchedulerInvariant cfg := by
  intro cfg hreach
  induction hreach with
  | init hent => exact schedulerInvariant_init leaf orig original props hent
  | step hrec hsucc ih =>
      clear cfg
      rename_i cfg cfg'
      have hsuccP : (schedulerNext cfg).successor = some cfg' := hsucc
      have hsucc0 : (schedulerNext cfg).successor = some cfg' := hsucc
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hsuccP
        unfold backjumpStep at hsuccP
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hsuccP
            simp only [] at hsuccP
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsuccP
            subst hsuccP
            exact stepChronologicalFallback_invariant ih
              (hg.core.hdeadFallbackNone hrec hc ha)
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hsuccP
                simp only [] at hsuccP
                rw [hcp] at hsuccP
                simp only [] at hsuccP
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hsuccP
                subst hsuccP
                exact stepChronologicalFallback_invariant ih
                  (hg.core.hdeadFallbackNoCp hrec hc ha hcp)
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    rw [ha] at hsuccP
                    simp only [] at hsuccP
                    rw [hcp] at hsuccP
                    simp only [] at hsuccP
                    rw [hp] at hsuccP
                    simp only [] at hsuccP
                    simp only [successor_localExclude, Option.some.injEq] at hsuccP
                    subst hsuccP
                    exact stepLocalExclude_invariant ih (hg.core.hentEv hrec hc)
                      (hg.core.hdeadCheckpointRegion hrec hc ha hcp hp)
                | some restored =>
                    -- the recorded jump: `cfg'` is pinned by the dispatcher
                    -- equation, so every field argument below is stated at
                    -- the concrete successor the arm's lemmas produce
                    rw [ha] at hsuccP
                    simp only [] at hsuccP
                    rw [hcp] at hsuccP
                    simp only [] at hsuccP
                    rw [hp] at hsuccP
                    simp only [] at hsuccP
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hsuccP
                    have hpinj : cfg' = stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                          an.learned) ev restored := hsuccP.symm
                    subst hpinj
                    have hreach' : ReachableState leaf cfg.orig
                        (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                            an.learned) ev restored).branch :=
                      stepLearnBackjumpAssert_branch_reachable hrec.reachable
                        ih.reachable
                        (by rw [SupportedReach.orig_eq hrec,
                                SupportedReach.original_eq hrec,
                                SupportedReach.props_eq hrec]
                            exact hg.core.hclos hrec)
                        (by rw [SupportedReach.original_eq hrec,
                                SupportedReach.props_eq hrec]
                            exact hg.core.hpay)
                        (hg.core.hunit hrec) (hg.core.hplanU hrec hc ha)
                        hc ha hcp hp
                        (by rw [SupportedReach.orig_eq hrec]
                            exact hg.core.hpre hrec
                              (by rw [← SupportedReach.orig_eq hrec];
                                  exact ih.reachable)
                              hc ha hcp hp)
                        (hg.core.hentEv hrec hc)
                        (by
                          show (schedulerNext cfg).successor =
                            some (stepLearnBackjumpAssert cfg
                              (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                                an.learned) ev restored)
                          exact hsucc0)
                    have hrestored : ReachableState leaf orig restored :=
                      perform_reachable_of_pre (hg.core.hclos hrec)
                        (hg.core.hpay) (hg.core.hunit hrec)
                        (hg.core.hplanU hrec hc ha)
                        (hg.core.hpre hrec
                          (by rw [← SupportedReach.orig_eq hrec];
                              exact ih.reachable)
                          hc ha hcp hp)
                        (by rw [← SupportedReach.orig_eq hrec, ← SupportedReach.original_eq hrec,
                                ← SupportedReach.props_eq hrec]
                            exact hp)
                    exact schedulerInvariant_after_backjump hreach'
                      (hg.core.hident hrec hc ha hcp hp)
                      (stepLearnBackjumpAssert_pending_fits ih.pending_fits)
                      (stepLearnBackjumpAssert_branch_fits hreach')
                      (stepLearnBackjumpAssert_log_sound ih.log_sound)
                      (stepLearnBackjumpAssert_coverage ih.coverage
                        (by rw [SupportedReach.orig_eq hrec]
                            exact hg.core.hbc hrec hc ha hcp hp)
                        (stepLearnBackjumpAssert_learned_mono
                          (restorationKeepsLearned_of_perform_cfg hp)))
                      (jump_learned_entailed (hg.core.hentEv hrec hc) hrestored)
      · -- ===== ROUTE 2: dead branch — the consume route
        rw [hnc] at hsuccP
        unfold consumeStep at hsuccP
        split at hsuccP
        · -- resumed: the gate supplies the resumed invariant
          rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hsuccP
          subst hsuccP
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest => exact hg.core.hconsumeInv hrec hdead hpend hcs
        · -- frontier exhausted: no successor
          simp only [successor_unsat] at hsuccP
          exact absurd hsuccP (by simp)
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hsuccP
          simp only [successor_propagate, Option.some.injEq] at hsuccP
          subst hsuccP
          refine stepPropagate_invariant ?_ ih (hg.core.hlevel hrec)
            (hg.core.hunit hrec) hd
          rw [SupportedReach.orig_eq hrec, SupportedReach.original_eq hrec,
            SupportedReach.props_eq hrec]
          exact hg.core.hclos hrec
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hsuccP
          unfold stableStepGuarded at hsuccP
          split at hsuccP
          · -- witness: terminal, no successor
            simp only [successor_sat] at hsuccP
            cases hsuccP
          · -- name the witness-failure fact (`leafWitness cfg = none`)
            -- for the stable-none dead-site gate below
            rename_i hwn
            split at hsuccP
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hsuccP
              · -- SKIP arm: stepDecideSkip (Bool closed, non-Bool via the
                -- redundant-site pin gate + the prefix-typing gate)
                simp only [successor_decide, Option.some.injEq] at hsuccP
                subst hsuccP
                cases v with
                | bool b =>
                    exact stepDecideSkip_invariant_bool ih hsp (by assumption)
                | int i =>
                    have hred := (by assumption :
                      TrailRedundant cfg.branch.trail l = true)
                    have hbs' : ReachableState leaf orig cfg.branch := by
                      rw [← SupportedReach.orig_eq hrec]; exact ih.reachable
                    exact stepDecideSkip_invariant ih hsp
                      (hg.core.hpinSkip hrec hbs' hsp hred)
                      (by rw [SupportedReach.orig_eq hrec]
                          exact hg.core.hskip hrec hbs' hsp hred)
                      hred
                | setOfInt s =>
                    have hred := (by assumption :
                      TrailRedundant cfg.branch.trail l = true)
                    have hbs' : ReachableState leaf orig cfg.branch := by
                      rw [← SupportedReach.orig_eq hrec]; exact ih.reachable
                    exact stepDecideSkip_invariant ih hsp
                      (hg.core.hpinSkip hrec hbs' hsp hred)
                      (by rw [SupportedReach.orig_eq hrec]
                          exact hg.core.hskip hrec hbs' hsp hred)
                      hred
                | array a =>
                    have hred := (by assumption :
                      TrailRedundant cfg.branch.trail l = true)
                    have hbs' : ReachableState leaf orig cfg.branch := by
                      rw [← SupportedReach.orig_eq hrec]; exact ih.reachable
                    exact stepDecideSkip_invariant ih hsp
                      (hg.core.hpinSkip hrec hbs' hsp hred)
                      (by rw [SupportedReach.orig_eq hrec]
                          exact hg.core.hskip hrec hbs' hsp hred)
                      hred
              · -- FRESH arm: stepDecide, pinned by the (free-form) pin gate
                simp only [successor_decide, Option.some.injEq] at hsuccP
                subst hsuccP
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                have hbs' : ReachableState leaf orig cfg.branch := by
                  rw [← SupportedReach.orig_eq hrec]; exact ih.reachable
                refine stepDecide_invariant ih (hg.core.hlevel hrec) hsp ?_ hred'
                intro a ha
                rw [SupportedReach.orig_eq hrec] at ha
                exact hg.core.hpin hrec hbs' hsp hred' a ha
            · -- no split data: localExclude with the EMPTY payload
              rename_i hsp
              simp only [successor_localExclude, Option.some.injEq] at hsuccP
              subst hsuccP
              exact stepLocalExclude_invariant ih
                (by intro c hc; simp at hc)
                (C2d.branchRegion_sound (hg.core.hdeadStableNone hrec ht hwn hsp))
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hsuccP
          cases cs with
          | nil =>
              -- empty clause list: database refutation with the payload
              simp only [conflictStep] at hsuccP
              simp only [successor_localExclude, Option.some.injEq] at hsuccP
              subst hsuccP
              have hdead := hg.hdeadConflictNil hrec
                (by rw [← SupportedReach.orig_eq hrec]; exact ih.reachable) ht rfl
              have hspec := terminalResult_spec (hg.core.hclos hrec)
                (by rw [← SupportedReach.orig_eq hrec]; exact ih.reachable)
              rw [SupportedReach.orig_eq hrec, SupportedReach.original_eq hrec,
                SupportedReach.props_eq hrec] at ht
              rw [ht] at hspec
              exact stepLocalExclude_invariant ih
                (fun c hc a ha =>
                  hspec.entailed c hc c (List.mem_singleton_self c) a ha)
                (C2d.branchRegion_sound hdead)
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: root contradiction, no successor
                simp only [conflictStep, if_pos hlv, successor_unsat] at hsuccP
                cases hsuccP
              · -- analyze stutter: only the evidence/stats fields move, so
                -- the invariant transfers field-by-field
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hsuccP
                subst hsuccP
                exact ⟨ih.reachable, ih.checkpoints_identify, ih.pending_fits,
                  ih.branch_fits, ih.log_sound, ih.coverage,
                  ih.learned_entailed⟩
        · -- ARM 6: localExcluded → localExclude with the payload
          rw [hnt] at hsuccP
          simp only [successor_localExclude, Option.some.injEq] at hsuccP
          subst hsuccP
          have hdead := hg.hdeadLocalExcluded hrec
            (by rw [← SupportedReach.orig_eq hrec]; exact ih.reachable) ht
          have hspec := terminalResult_spec (hg.core.hclos hrec)
            (by rw [← SupportedReach.orig_eq hrec]; exact ih.reachable)
          rw [SupportedReach.orig_eq hrec, SupportedReach.original_eq hrec,
            SupportedReach.props_eq hrec] at ht
          rw [ht] at hspec
          exact stepLocalExclude_invariant ih
            (fun c hc a ha =>
              hspec.entailed c hc c (List.mem_singleton_self c) a ha)
            (C2d.branchRegion_sound hdead)

/-- **S2's B4 ADAPTER**: ONE supported residual record yields BOTH B4
outputs the run assembly consumes — the supported successor invariant
(`hpres`) and the invariant discipline (`hinv`), definitionally the
supported counterpart of `RunAssembly.ReachableInvariantDiscipline`. -/
theorem supportedB4 {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hc : SupportedArmInvGatesCore orig original props leaf) :
    SupportedArmsPreserveReach orig original props leaf ∧
      (∀ (cfg : SchedulerConfig leaf),
        SupportedReach orig original props cfg → SchedulerInvariant cfg) :=
  ⟨supportedArmsPreserveReach_of_gates hc.coreGates,
   supportedInvariantDiscipline_of_gates hc.toSupportedArmInvGates⟩

end LeanFzn.Solver.UIP
