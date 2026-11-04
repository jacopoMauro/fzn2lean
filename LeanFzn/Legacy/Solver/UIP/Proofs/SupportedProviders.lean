/-
File: LeanFzn/Solver/UIP/Proofs/SupportedProviders.lean

Purpose: the first supported PRODUCERS, at the frozen field shapes of
`SupportedGates`:

  §1 `SupportedPinGates` — the three typed-pin gates of one supported run
     (the frozen shapes of `SupportedArmGates`/`SupportedArmInvGatesCore`
     for `hpin`/`hpinSkip`/`hskip`), and `supportedPinGates_of_shape`:
     produced from the run's box shape discipline
     (`ShapeTypedDomains orig`, D1's `SupportedInput.shape`). Bool sites are
     closed globally (`valueLiteral_holds_iff`, `decidePinTyped_bool`,
     `decideSkipPrefixTyped_bool`); int sites use the Fits-restricted
     producers (`decidePinFits_int`, `decidePinTyped_int_of_shape`,
     `decideSkipPrefixTyped_int`); unsupported heads (`setOfInt`/`array`)
     cannot produce split data at all (`valueLiteral = none`), so they are
     excluded from the site equation.
  §2 The supported closure provider: a problem-level `ClosureContract` IS
     the supported `hclos` field (it is stated at the run's fixed triple),
     including the compiled route export
     (`CompiledInput.closureContract_of_provenance`). The remaining B2b work
     is producing the contract itself from the compiled input (the
     `hprov`/`hinhab` route, with the empty-frame exclusion replacing
     inhabitedness).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedProviders` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedGates
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerArmsComplete
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The supported typed-pin gates -/

/-- The three typed-pin gate shapes of ONE supported run (the fields
`hpin`/`hpinSkip`/`hskip` of the supported records, frozen here so one
producer serves both records). -/
structure SupportedPinGates (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame cfg.prio = some (l, k, v, vs) →
    TrailRedundant cfg.branch.trail l = false →
      ∀ a : Assignment, Assignment.Fits orig a →
        (l.norm.eval a = some true ↔
          a[k]? = some v)
  hpinSkip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame cfg.prio = some (l, k, v, vs) →
    TrailRedundant cfg.branch.trail l = true → DecidePinTyped cfg k l v
  hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame cfg.prio = some (l, k, v, vs) →
    TrailRedundant cfg.branch.trail l = true →
      DecideSkipPrefixTyped orig cfg k v

/-- **THE PIN PRODUCER**: from the run's shape discipline, all three
typed-pin gates. This is the B4 wiring of the completed typed-pin lemmas at
the supported index; no per-state semantic assumption remains. -/
theorem supportedPinGates_of_shape {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig) :
    SupportedPinGates orig original props leaf where
  hpin := fun {cfg} {l} {k} {v} {vs} hreach hbs hsp hred a hfit => by
    cases v with
    | bool b =>
        have hwl := (splitData_eq_some_iff.mp hsp).2.2.1
        rw [Literal.norm_eval]
        simpa using valueLiteral_holds_iff hwl a
    | int i => exact decidePinFits_int hsp hbs hshape a hfit
    | setOfInt s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])
    | array s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])
  hpinSkip := fun {cfg} {l} {k} {v} {vs} hreach hbs hsp hred => by
    cases v with
    | bool b => exact decidePinTyped_bool hsp
    | int i => exact decidePinTyped_int_of_shape hsp hbs hshape
    | setOfInt s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])
    | array s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])
  hskip := fun {cfg} {l} {k} {v} {vs} hreach hbs hsp hred => by
    cases v with
    | bool b => exact decideSkipPrefixTyped_bool hsp hred
    | int i => exact decideSkipPrefixTyped_int hsp hbs hred hshape
    | setOfInt s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])
    | array s =>
        exact absurd (splitData_eq_some_iff.mp hsp).2.2 (by simp [valueLiteral])

/-! ## §2 The supported closure provider -/

/-- `domSupportedB` unfolds to the per-constraint `unitFamilyB` fact the
compiled closure adapter consumes. -/
theorem unitFamilyB_of_domSupportedB {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : domSupportedB problem = true) :
    ∀ dc ∈ problem.constraints, unitFamilyB dc = true :=
  fun dc hdc => List.all_eq_true.mp h dc hdc

/-- The supported `hclos` field shape: the run's fixed-triple contract. -/
def SupportedHclos (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ClosureContract leaf orig original props

/-- **THE CLOSURE PROVIDER**: a problem-level contract IS the supported
`hclos` field (the field is stated at the run's fixed triple). -/
theorem supportedHclos_of_contract {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (h0 : ClosureContract leaf orig original props) :
    SupportedHclos orig original props leaf :=
  fun _ => h0

/-- The compiled-route export: `CompiledInput.closureContract_of_provenance`
supplies the contract for the compiled triple with NO shape premise — the
gated learned-unit shape is free under the unit discipline
(`hshape_of_unitLearned`), which the run supplies wherever the closure's
learned-dependent fields are consumed. -/
theorem supportedHclos_of_compiled {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true) :
    SupportedHclos problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) leaf :=
  supportedHclos_of_contract (hin.closureContract_of_provenance hSupp)

/-! ## §3 The recorded-evidence entailment producer (`hentEv`) -/

/-- **THE `hentEv` PRODUCER**: at a supported configuration with recorded
evidence, the payload is entailed. Route analysis over the dispatcher trees:
the evidence is RECORDED only at the analyze site (`conflictStep`'s
nonempty, non-level-0 arm), whose payload is the terminal conflict's
`learned` list — entailed by the closure contract via `terminalResult_spec`;
every other arm either keeps the previous evidence (consumed by the
induction hypothesis) or clears it (contradiction). The two site facts
(`hclos` at the run, `hbr` at the run) are available in the provider
context. -/
theorem supportedHentEv_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned := by
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
                simp only [successor_chronologicalFallback, Option.some.injEq] at hs
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
        · -- ARM 1: propagate — the conflict field is unchanged
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          rw [stepPropagate_conflict] at hconf
          exact ih hconf
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
              · -- SKIP arm — the conflict field is unchanged
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                rw [stepDecideSkip_conflict] at hconf
                exact ih hconf
              · -- FRESH arm — the conflict field is unchanged
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                rw [stepDecide_conflict] at hconf
                exact ih hconf
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
              · -- THE RECORDING SITE: the payload is the terminal conflict's
                -- `learned`, entailed by the closure contract
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                rw [stepAnalyzeConflictCounted_conflict] at hconf
                injection hconf with hev
                subst hev
                have hspec := terminalResult_spec (hclos hrec) (hbr hrec)
                rw [SupportedReach.orig_eq hrec] at ht
                rw [ht] at hspec
                exact fun c' hc' a ha =>
                  hspec.entailed c' hc' c' (List.mem_singleton_self c') a ha
        · -- ARM 6: localExcluded → localExclude (clears)
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          rw [stepLocalExclude_conflict] at hconf
          cases hconf

/-- **THE `hpre` PRODUCER (J1 round 2, SUCCESS-GUARDED)**: the restoration
pre-reachability at ACTUAL supported jump sites (the runtime's
`some restored` equation), PROVED from the raw checkpoint-push bundle
(the `reachableCpSnapshots_of_step` chain induction) and the six named
site obligations of `restorationPreReachable_of_success` — NO
`RestorationStepPreserves` hypothesis remains. The run's raw index comes
from the forgetting map (`SupportedReach.reachable`); the chain snapshot is
transported from `cfg.orig` to the run's fixed box by
`SupportedReach.orig_eq`.

Site obligations (owners; each strictly weaker than the conclusion and
jointly the honest residual of this gate): `hcert` (analyzer certificate —
P1/N1 provenance), `hstable`/`hneg` (N1 recording-site normalization makes
both structural on the canonical record), `hsurv` (R2 checkpoint
identity / surviving prefix), `hfresh` (the enqueue absence check — S5/E3;
the certificate's `assertingSurvives` speaks about the NEGATION and cannot
supply it), `hrange` (the asserting literal names an in-range slot). -/
theorem supportedHpre_of_premises {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hpush : ∀ {cfg cfg' : SchedulerConfig leaf},
      SchedulerReachable cfg → (schedulerNext cfg).successor = some cfg' →
      List.Sublist cfg'.checkpoints cfg.checkpoints ∨
        ∃ cp, cfg'.checkpoints = cp :: cfg.checkpoints ∧
          CheckpointSnapshot leaf cfg.orig cp)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hstable : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.norm = an.asserting)
    (hneg : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.atom.slot < orig.length) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
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
          cfg.branch := by
  intro cfg cp ev an restored hreach hbs hconf hana hcp hp
  have hsnap : CheckpointSnapshot leaf orig cp := by
    have h := reachableCpSnapshots_of_step hpush hreach.reachable cp
      (checkpointAt_mem hcp)
    rwa [SupportedReach.orig_eq hreach] at h
  exact restorationPreReachable_of_success_avoiding hsnap hbs
    (hcert hreach hconf hana)
    (hstable hreach hconf hana) (hneg hreach hconf hana)
    (hsurv hreach hconf hana hcp)
    (hrange hreach hconf hana) hp

/-! ## §4-bis The supported snapshot-bundle producer (J1/E1) -/

/-- **THE SNAPSHOT-BUNDLE PRODUCER**: every checkpoint saved along a
supported run is a reachable snapshot of the run's box. Run-level closure
of the reach-aware push bundle (`checkpoints_push_or_sublist_of_successor`):
the decide arm pushes the branch's own snapshot from the paired
predecessor reachability, the jump filters and the consume filters keep
sublists. Non-circular with the joint reachability/evidence induction (the
push arm reads only the paired predecessor component). -/
theorem supportedReachableCpSnapshots_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableCpSnapshots leaf orig cfg := by
  intro cfg hreach
  induction hreach with
  | init => exact reachableCpSnapshots_init orig original props
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases checkpoints_push_or_sublist_of_successor
        (by
          have h := hbr hrec
          rwa [← SupportedReach.orig_eq hrec] at h) hs with
        hsub | ⟨cp, hpush, hsnap⟩
      · exact ReachableCpSnapshots.of_sublist ih hsub
      · intro c hc
        rw [hpush] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rwa [SupportedReach.orig_eq hrec] at hsnap
        · exact ih c hc

/-! ## §5 The supported `hlevel` producer (R2) -/

/-- **THE `hlevel` PRODUCER**: every supported reachable configuration
satisfies the checkpoint-level discipline. No gate premise is needed: the
induction runs on the real dispatcher trees, each arm closing with the
matching `checkpointsBelow_*` closure. The consume arm is exactly the R1
runtime retirement (`checkpointsBelow_consume`, whose filter makes the
resumed level bound hold with no predecessor premise). -/
theorem supportedHlevel_of_reach {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      CheckpointsBelow cfg := by
  intro cfg hreach
  induction hreach with
  | init => exact checkpointsBelow_init leaf orig original props
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            exact checkpointsBelow_chronologicalFallback ih
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
                exact checkpointsBelow_chronologicalFallback ih
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
                    exact checkpointsBelow_localExclude ih
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
                    exact checkpointsBelow_learnBackjumpAssert ih
                      (BackjumpPlan.perform_level hp)
      · -- ===== ROUTE 2: dead branch — the consume route
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
          | cons f rest => exact checkpointsBelow_consume hpend hcs
        · simp only [successor_unsat] at hs
          exact absurd hs (by simp)
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          exact checkpointsBelow_propagate ih
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
              · -- SKIP arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact checkpointsBelow_decideSkip ih
              · -- FRESH arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact checkpointsBelow_decide ih
            · -- no split data: localExclude
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact checkpointsBelow_localExclude ih
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact checkpointsBelow_localExclude ih
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                exact checkpointsBelow_analyzeConflictCounted ih
        · -- ARM 6: localExcluded → localExclude
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact checkpointsBelow_localExclude ih

/-! ## §5-bis The supported `hident` producer (J1) -/

/-- **THE IDENTIFIES+CHAIN INDUCTION**: one pass over the supported run
produces both the per-state checkpoint identity conjunct and the
newest-first `CpChain` — the two ingredients the `hident` engine consumes
and the two maintenance halves the decide push and the jump/consume
filters act on. Only `hconsumeInv` is external (the consume arm reads its
`checkpoints_identify` field); no full `SchedulerInvariant` is ever
required. -/
theorem supportedIdentifiesChain_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      (∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level) ∧
        CpChain cfg.checkpoints := by
  intro cfg hreach
  induction hreach with
  | init =>
      refine ⟨?_, ?_⟩
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst hcp
        simpa only [SchedulerConfig.init, rootCheckpoint] using
          rootCheckpoint_identifies_init leaf orig original
      · exact ⟨fun cp' h => by simp at h, trivial⟩
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            refine ⟨?_, ?_⟩
            · intro cp hcp
              exact ih.1 cp (by simpa only [stepChronologicalFallback] using hcp)
            · simpa only [stepChronologicalFallback] using ih.2
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
                refine ⟨?_, ?_⟩
                · intro cp hcp'
                  exact ih.1 cp
                    (by simpa only [stepChronologicalFallback] using hcp')
                · simpa only [stepChronologicalFallback] using ih.2
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
                    refine ⟨?_, ?_⟩
                    · intro cp' hcp'
                      exact ih.1 cp'
                        (by simpa only [stepLocalExclude] using hcp')
                    · simpa only [stepLocalExclude] using ih.2
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
                    refine ⟨?_, ?_⟩
                    · intro cp' hmem
                      exact stepLearnBackjumpAssert_hident_of_chain ih.2 hcp hp
                        hmem
                    · rw [stepLearnBackjumpAssert_checkpoints]
                      exact CpChain.filter ih.2 _
      · -- ===== ROUTE 2: dead branch — the consume route
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
              refine ⟨?_, ?_⟩
              · unfold stepConsume at hcs
                rw [hpend] at hcs
                injection hcs with hnext
                subst hnext
                intro cp hmem
                simp at hmem
              · unfold stepConsume at hcs
                rw [hpend] at hcs
                injection hcs with hnext
                subst hnext
                trivial
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          refine ⟨?_, ?_⟩
          · intro cp hcp
            exact stepPropagate_checkpoints_identify_of_identifies ih.1
              (supportedHlevel_of_reach hrec) d cp hcp
          · simpa only [stepPropagate] using ih.2
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
              · -- SKIP arm
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact stepDecideSkip_checkpoints_identify_of_identifies ih.1
                    hsp cp hcp
                · simpa only [stepDecideSkip] using ih.2
              · -- FRESH arm: the push site
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact stepDecide_checkpoints_identify_of_identifies ih.1
                    (supportedHlevel_of_reach hrec) hsp cp hcp
                · exact CpChain.of_identifies ih.2 ih.1
                    (supportedHlevel_of_reach hrec)
            · -- no split data: localExclude
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro cp hcp
                exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
              · simpa only [stepLocalExclude] using ih.2
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro cp hcp
                exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
              · simpa only [stepLocalExclude] using ih.2
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site: branch and checkpoint list unchanged
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_⟩
                · intro cp hcp
                  exact ih.1 cp (by simpa only [stepAnalyzeConflictCounted,
                    stepAnalyzeConflict, SchedulerConfig.countResolutions]
                      using hcp)
                · simpa only [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                    SchedulerConfig.countResolutions] using ih.2
        · -- ARM 6: localExcluded → localExclude
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          refine ⟨?_, ?_⟩
          · intro cp hcp
            exact ih.1 cp (by simpa only [stepLocalExclude] using hcp)
          · simpa only [stepLocalExclude] using ih.2

/-- **THE `hident` PRODUCER**: the jump successor's checkpoint-identity
obligation at the supported index, from the chain induction and the engine.
The statement is verbatim the `SupportedArmInvGatesCore.hident` field
type. -/
theorem supportedHident_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        ∀ cp' ∈ (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
            ev restored).checkpoints,
          cp'.Identifies (stepLearnBackjumpAssert cfg
              (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
              ev restored).branch cp'.level := by
  intro cfg cp ev an restored hreach hconf hana hcp hperf cp' hmem
  exact stepLearnBackjumpAssert_hident_of_chain
    (supportedIdentifiesChain_of_premises hreach).2 hcp hperf hmem

/-! ## §6 The supported `hbc` producer (J2) -/

/-- **THE `hbc` PRODUCER**: the jump successor covers every remaining leaf
solution (or falsifies a learned clause), from the recorded analysis's
norm-falsification — no frame-alternative premise survives
(`jumpFrameAlternative_of_recorded_analysis_norm` + the concrete
`backjumpCovers_of_frame_alternative`). -/
theorem supportedHbc_of_recorded_analysis {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        BackjumpCovers leaf orig cfg
          (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
            ev restored) := by
  intro cfg cp ev an restored hreach hconf hana hcp hperform
  exact backjumpCovers_of_frame_alternative
    (jumpFrameAlternative_of_recorded_analysis_norm rfl (hbr hreach) hana rfl
      hperform
      (recordedAnalysis_normFalsified rfl (hbr hreach) hreach.reachable
        hconf hana))

end LeanFzn.Solver.UIP
