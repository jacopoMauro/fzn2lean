/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerConflict.lean

Purpose:
  The conflict→analyzer bridge of the certified first-UIP/backjump
  scheduler. E3 owns exactly three things (PLAN.md E3):

  * `analyzerInputOfConflict` — the adapter turning a RECORDED scheduler
    conflict event (`ConflictEvidence`, C1) into the supported analyzer
    input (`AnalyzerInput`, B1 §2.3). The semantic fields (`entailed`,
    `falsified`) are the closure's own evidence (A3/E1/E2 for the
    supported fragment, A1 for the trail shape): E3 transports them,
    never fabricates them.

  * `AllowanceCertificate` — the computed-allowance certificate: the
    recorded run IS the executable entry point `analyzeAtAllowance`
    (`ConflictResolution`), whose `analysisFuel` dominates both the
    computed literal budget `analysisAllowance` and the historical
    constant; `allowanceCertificate_of_historical` proves the switch to
    the input-dependent allowance loses no result the constant found,
    and `allowanceCertificate_run_eq_loop` reads the certificate back as
    the executable loop at the runtime allowance.

  * the ROUTING case analysis of INTERFACES §9.3 (frozen):
      (a) level 0 (`ConflictShape.root`): the `.unsat` arm of
          `conflictStep`; its justification is `AnalyzerInput` PLUS the
          root-facts bridge — `rootContradiction_sound` is the a-priori
          statement under `RootFactsBridge` (D1a discharges the bridge on
          the public path), and `dead_of_root_contradiction` is the
          `hdead` shape `SchedulerInvariant.unsat_coverage` consumes.
          FINDING (proved `example` at the end): the dispatcher does not
          and cannot consult the analyzer on this arm — `conflictStep`
          returns `.unsat` while the executable run has NO result.
      (b) level > 0 with a completed run (`AnalysisOutcome.success`):
          `stepAnalyzeConflict` stores `ConflictAnalysis.ofUIP below uip`
          (`ofRun_eq_ofUIP` identifies it with the certificate's
          `ofRun` record), and `backjumpStep` routes to the
          learn/backjump/assert transition when the checkpoint exists
          and the restoration performs.
      (c) unsupported (allowance `none`, level > 0), missing checkpoint,
          rejected assertion, or the local closure arm (`.conflict []`,
          `.localExcluded`): `chronologicalFallback` / `localExclude` —
          NEVER `unsat`. `backjumpStep_ne_unsat` proves the recorded-
          evidence dispatcher has no `unsat` arm at all.

  No analyzer is re-implemented and no frozen interface is changed; all
  adapters are local definitions.

Dependencies:
  - LeanFzn.Solver.UIP.SchedulerStep (C1): `conflictStep`, `backjumpStep`,
    `schedulerNext`, `stepAnalyzeConflict`, `ConflictEvidence`.
  - LeanFzn.Solver.Propagation.AnalysisProgress (B1): `AnalyzerInput`, `AnalysisOutcome`,
    `analyzeClassified`, `analyzeAtAllowance_fuel_eq`,
    `analyzeAtAllowance_dominates`.
  - LeanFzn.Solver.UIP.Proofs.SchedulerInvariant (S0): the frozen policy context
    and the `unsat`-arm coverage consumer.

DAG:
  SchedulerStep + AnalysisProgress + Proofs.SchedulerInvariant
    -> Proofs.SchedulerConflict (this file; E3) -> C2c / D1a consumers.

Import line for the coordinator to register:

    import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerConflict
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerInvariant
import LeanFzn.Legacy.Solver.UIP.SchedulerStep
import LeanFzn.Legacy.Solver.Propagation.AnalysisProgress
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Legacy.Solver.UIP.Proofs.DomExplained
import LeanFzn.Legacy.Solver.UIP.Proofs.AnalyzeSingleton
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## The three-way routing verdict -/

/-- E3's routing verdict of one recorded conflict event in the frozen
§9.3 vocabulary: `rootVerdict` is the level-0 route (taken ONLY with
`AnalyzerInput` + `RootFactsBridge` evidence), `analyzable` is the
completed run whose record drives the learn/backjump/assert transition,
and `fallback` is the proved local/chronological step that never yields a
global verdict. -/
inductive ConflictRoute where
  | rootVerdict
  | analyzable (below : List (Literal × Nat)) (uip : Literal)
  | fallback
  deriving DecidableEq, Repr

/-- The route of the executable analysis, computed from
`analyzeAtAllowance` exactly as `AnalysisOutcome` classifies it. -/
def conflictRoute (orig : List Domain) (trail : List TrailEntry) (lvl : Nat) (c : Clause) :
    ConflictRoute :=
  match analyzeAtAllowance orig trail lvl c with
  | some (below, uip) => .analyzable below uip
  | none => if lvl = 0 then .rootVerdict else .fallback

theorem conflictRoute_of_some {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl c = some (below, uip)) :
    conflictRoute orig trail lvl c = .analyzable below uip := by
  unfold conflictRoute
  rw [h]

theorem conflictRoute_of_none_pos {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} (h : analyzeAtAllowance orig trail lvl c = none) (hpos : lvl ≠ 0) :
    conflictRoute orig trail lvl c = .fallback := by
  unfold conflictRoute
  rw [h]
  simp [hpos]

theorem conflictRoute_of_none_zero {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} (h : analyzeAtAllowance orig trail lvl c = none) (h0 : lvl = 0) :
    conflictRoute orig trail lvl c = .rootVerdict := by
  unfold conflictRoute
  rw [h]
  simp [h0]

/-! ## The conflict→analyzer adapter (INTERFACES §2.3) -/

/-- E3's conflict→analyzer adapter: a recorded scheduler conflict event
plus the closure's evidence yields the supported analyzer input. `hne`,
`hent`, `hfals` are exactly the conflict-event obligations of the
supported fragment (A3/E1/E2 derive them from the closure contract); the
adapter only transports them. -/
def analyzerInputOfConflict {leaf : Assignment → Bool}
    {bs : BranchState leaf} (ev : ConflictEvidence) (hne : 1 ≤ ev.clause.length)
    (hent : LearnedEntailed leaf [ev.clause])
    (hfals : FalsifiedByTrail bs ev.clause) : AnalyzerInput leaf bs :=
  ⟨ev.clause, hne, hent, hfals⟩

@[simp] theorem analyzerInputOfConflict_conflict {leaf : Assignment → Bool}
    {bs : BranchState leaf} (ev : ConflictEvidence) (hne : 1 ≤ ev.clause.length)
    (hent : LearnedEntailed leaf [ev.clause])
    (hfals : FalsifiedByTrail bs ev.clause) :
    (analyzerInputOfConflict (bs := bs) ev hne hent hfals).conflict
      = ev.clause := rfl

@[simp] theorem analyzerInputOfConflict_nonempty {leaf : Assignment → Bool}
    {bs : BranchState leaf} (ev : ConflictEvidence) (hne : 1 ≤ ev.clause.length)
    (hent : LearnedEntailed leaf [ev.clause])
    (hfals : FalsifiedByTrail bs ev.clause) :
    (analyzerInputOfConflict (bs := bs) ev hne hent hfals).nonempty = hne := rfl

/-- The recorded-evidence constructor of the analyzer input at the
dispatch site: the payload `stepAnalyzeConflict` stores is exactly the
one `analyzerInputOfConflict` consumes, and the adapter's projections are
definitional. -/
example {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {c : Clause} {learned : List Clause}
    (hne : 1 ≤ c.length) (hent : LearnedEntailed leaf [c])
    (hfals : FalsifiedByTrail cfg.branch c) :
    (analyzerInputOfConflict (bs := cfg.branch)
        { clause := c, learned := learned,
          analysis := (analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level c).map
            (fun p => (ConflictAnalysis.ofUIP p.1 p.2).normalized) } hne hent hfals).conflict
      = c := rfl

/-! ## The reachable-event discharge (R1's success bridge consumed)

`ReachableEventResidual` names the runtime obligations of one recorded
event that reachability does NOT discharge, each with its owner. The
adapter below is the concrete-event form of `analyzerInputOfConflict`:
reachability supplies the analysis-success content (R1), the residual
supplies the semantic fields from the closure's own evidence. -/

/-- The residual obligations of one recorded conflict event, with owners:
* `nonempty` — owner A3/D0: the closure's conflict payload is nonempty
  for the supported fragment (`conflictEvidence_at`);
* `entailed` — owner A3/D0: `ClosureContract.conflictEntailed`
  (`LearnedEntailed` on the reported clauses);
* `falsified` — owner A3/S3: the branch-relative `conflictExcludes`
  field, read as trail falsification.
Reachability alone fabricates neither entailment nor falsification. -/
structure RecordedEventResidual (leaf : Assignment → Bool)
    (bs : BranchState leaf) (c : Clause) : Prop where
  nonempty : 1 ≤ c.length
  entailed : LearnedEntailed leaf [c]
  falsified : FalsifiedByTrail bs c

/-- **CONCRETE EVENT DISCHARGE**: for a reachable configuration carrying
recorded evidence, the analyzer input for the event is the adapter's
output as soon as the residual above is supplied by its owners
(entailment/falsification are never fabricated by reachability). -/
def analyzerInput_of_reachable_event {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (_hreach : SchedulerReachable cfg) (_hconf : cfg.conflict = some ev)
    (hres : RecordedEventResidual leaf cfg.branch ev.clause) :
    AnalyzerInput leaf cfg.branch :=
  analyzerInputOfConflict ev hres.nonempty hres.entailed hres.falsified

/-- **THE SUCCESS DISCHARGE** (R1's `reachable_analysis_success`, consumed
at the concrete event): the recorded analysis of a reachable event is a
genuine successful computed-allowance run producing exactly the `ofUIP`
record — so the analyzer input's run is never assumed. -/
theorem reachable_event_analysis_success {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (hreach : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (an : ConflictAnalysis) (hana : ev.analysis = some an) :
    ∃ (below : List (Literal × Nat)) (uip : Literal),
      analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level ev.clause
        = some (below, uip) ∧ an = (ConflictAnalysis.ofUIP below uip).normalized :=
  reachable_analysis_success leaf cfg ev an hreach hconf hana

/-! ## The root-facts bridge and the a-priori root statement -/

/-- The root-facts bridge (INTERFACES §9.3 item 2): every trail fact of
the level-0 branch holds at every leaf solution. E3 consumes it; the
a-priori instantiation for compiled inputs is D1a's obligation (root
facts from the compiled problem). -/
def RootFactsBridge (leaf : Assignment → Bool) (bs : BranchState leaf) : Prop :=
  ∀ a, leaf a = true → ∀ e ∈ bs.trail, e.literal.eval a = some true

/-- Evaluation of a negated literal is the Boolean flip. -/
theorem literal_eval_negate (l : Literal) (a : Assignment) :
    l.negate.eval a = (l.eval a).map (fun b => !b) := by
  unfold Literal.negate Literal.eval
  cases h : l.atom.eval a with
  | none => rfl
  | some v => cases v <;> cases l.positive <;> rfl

/-- `.rootContradiction` soundness (a-priori form, §2.3): an entailed
conflict clause all of whose literals are trail-falsified excludes every
leaf solution, given the root-facts bridge. This is the evidence the
level-0 `.unsat` arm of `conflictStep` needs and does not itself
provide. -/
theorem rootContradiction_sound {leaf : Assignment → Bool}
    {bs : BranchState leaf} (hin : AnalyzerInput leaf bs)
    (hbridge : RootFactsBridge leaf bs) :
    ∀ a, leaf a = true → False := by
  intro a hleaf
  obtain ⟨q, hq, hqtrue⟩ :=
    hin.entailed hin.conflict (List.mem_singleton_self _) a hleaf
  obtain ⟨e, he, heq⟩ := hin.falsified q hq
  have htrue := hbridge a hleaf e he
  rw [heq, literal_eval_negate] at htrue
  have hfalse : q.eval a = some false := by
    cases hq' : q.eval a with
    | none =>
        rw [hq'] at htrue
        cases htrue
    | some v =>
        rw [hq'] at htrue
        simp only [Option.map_some, Option.some.injEq] at htrue
        cases v
        · rfl
        · simp at htrue
  rw [hfalse] at hqtrue
  cases hqtrue

/-- The `hdead` shape `SchedulerInvariant.unsat_coverage` consumes: a root
contradiction (the a-priori statement above) makes every frame dead. -/
theorem dead_of_root_contradiction {leaf : Assignment → Bool}
    (h : ∀ a, leaf a = true → False) (f : BranchFrame) :
    ∀ a, leaf a = true → FrameCovers f a → False :=
  fun a ha _ => h a ha

/-- The level-0 consumer of the reachable-event discharge: a reachable
root event with the residual and the root-facts bridge is a global
exclusion (the `rootContradiction_sound` statement), so the `.unsat` arm's
justification is exactly the transported evidence, never fabricated
analysis. -/
theorem rootContradiction_of_reachable_event {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (hreach : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hres : RecordedEventResidual leaf cfg.branch ev.clause)
    (hbridge : RootFactsBridge leaf cfg.branch) :
    ∀ a, leaf a = true → False :=
  rootContradiction_sound
    (analyzerInputOfConflict ev hres.nonempty hres.entailed hres.falsified)
    hbridge

/-! ## The computed-allowance certificate -/

/-- E3's computed-allowance certificate for one recorded conflict event:
the executable entry point's result `r` together with the fact that the
runtime allowance strictly exceeds the analyzer's termination potential
(R1a: replaces the former `ge_computed`/`ge_historical` domination fields —
the allowance is now the potential plus one, proved sufficient by
`AnalysisCompletion.analysis_complete`). -/
structure AllowanceCertificate (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) (r : List (Literal × Nat) × Literal) : Prop where
  /-- the recorded run is the executable entry point's result -/
  run : analyzeAtAllowance orig trail lvl c = some r
  /-- the runtime allowance exceeds the termination potential -/
  sufficient : analyzerPotential trail (initAnalysisState c) < analysisFuel trail c

/-- The certificate of a completed run. -/
theorem allowanceCertificate_of_run {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {r : List (Literal × Nat) × Literal}
    (h : analyzeAtAllowance orig trail lvl c = some r) :
    AllowanceCertificate orig trail lvl c r :=
  ⟨h, Nat.lt_succ_self _⟩

/-- The certificate's equation is the executable loop at the runtime
allowance. -/
theorem allowanceCertificate_run_eq_loop {orig : List Domain} {trail : List TrailEntry}
    {lvl : Nat} {c : Clause} {r : List (Literal × Nat) × Literal}
    (h : AllowanceCertificate orig trail lvl c r) :
    analyzeLoop orig trail lvl (analysisFuel trail c) (initAnalysisState c)
      = some r :=
  h.run

/-- The scheduler's `ofUIP` record IS `ofRun` (definitional identity): a
certificate stated for `ConflictAnalysis.ofRun` — the record B2's
`analyzeAtAllowance_certificate` consumes — is a certificate for the
record `stepAnalyzeConflict` stores. -/
theorem ofRun_eq_ofUIP (below : List (Literal × Nat)) (uip : Literal) :
    ConflictAnalysis.ofRun below uip = ConflictAnalysis.ofUIP below uip := rfl

/-! ## The dispatch arms (policy §9.3) -/

/-- The local closure arm: an empty reported clause list never reaches the
analyzer and never yields a verdict (§9.3 item 3). -/
theorem conflictStep_empty (cfg : SchedulerConfig leaf) (learned : List Clause) :
    conflictStep cfg [] learned
      = .localExclude (stepLocalExclude cfg learned (branchRegion cfg)) := rfl

/-- The root arm: a level-0 nonempty conflict routes to `.unsat`. The
dispatcher supplies NO analysis evidence here — the caller's
`AnalyzerInput` + `RootFactsBridge` (`rootContradiction_sound`) is the
whole justification (§9.3 item 2; the `example` at the end exhibits the
gap). -/
theorem conflictStep_of_level_zero {cfg : SchedulerConfig leaf} {c : Clause}
    {rest : List Clause} {learned : List Clause} (h : cfg.branch.level = 0) :
    conflictStep cfg (c :: rest) learned = .unsat := by
  simp only [conflictStep, h, if_true]

/-- The analyzable arm: a positive level records the allowance run as the
successor's evidence — `stepAnalyzeConflict`, whose `analysis` field is
computed by `analyzeAtAllowance`; the O1 wiring routes it through
`stepAnalyzeConflictCounted`, which additionally records the executed
run's pivot expansions into `events.reasonResolutions`. -/
theorem conflictStep_of_level_pos {cfg : SchedulerConfig leaf} {c : Clause}
    {rest : List Clause} {learned : List Clause} (h : cfg.branch.level ≠ 0) :
    conflictStep cfg (c :: rest) learned
      = .analyzeConflict (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) c := by
  simp only [conflictStep, h, if_false]

/- The recorded evidence's `analysis` field is the mapped allowance run,
by R1's `stepAnalyzeConflict_conflict_eq` (imported from
`Proofs/SchedulerReachable.lean`): `stepAnalyzeConflict_analysis_some` and
`_none` below rewrite with the same equation. -/

/-- Case (b) recording: a completed run stores the first-UIP record in
NORMALIZED form (the N1 recording-site normalization). -/
theorem stepAnalyzeConflict_analysis_some {cfg : SchedulerConfig leaf}
    {c : Clause} {learned : List Clause} {below : List (Literal × Nat)}
    {uip : Literal}
    (h : analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level c
      = some (below, uip))
    (hg : learnedRepeats cfg (ConflictAnalysis.ofUIP below uip).normalized.learned = false) :
    (stepAnalyzeConflict cfg c learned).conflict
      = some { clause := c, learned := learned,
               analysis := some ((ConflictAnalysis.ofUIP below uip).normalized) } := by
  simp only [stepAnalyzeConflict_conflict_eq, recordedAnalysis, h, Option.map_some,
    Option.filter_some, hg, Bool.not_false, if_true]

/-- Case (c) recording: no result stores `none` (the fallback trigger). -/
theorem stepAnalyzeConflict_analysis_none {cfg : SchedulerConfig leaf}
    {c : Clause} {learned : List Clause}
    (h : analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level c = none) :
    (stepAnalyzeConflict cfg c learned).conflict
      = some { clause := c, learned := learned, analysis := none } := by
  simp only [stepAnalyzeConflict_conflict_eq, recordedAnalysis, h, Option.map_none,
    Option.filter_none]

/-! ## The recorded-evidence dispatcher's arms -/

/-- First fallback arm: no analysis result (allowance exhausted or
unsupported input) routes chronologically. -/
theorem backjumpStep_of_analysis_none {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} (h : ev.analysis = none) :
    backjumpStep cfg ev
      = .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) := by
  simp only [backjumpStep, h]

/-- Missing-checkpoint arm: a completed analysis whose target has no
checkpoint falls back chronologically. -/
theorem backjumpStep_of_checkpoint_none {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (han : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = none) :
    backjumpStep cfg ev
      = .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) := by
  simp only [backjumpStep, han, hcp]

/-- Rejected-assertion arm: the restoration failed on the restored
ancestor, so the CHECKPOINT's region — not the current branch's — is
locally excluded. -/
theorem backjumpStep_of_perform_none {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf}
    (han : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = none) :
    backjumpStep cfg ev
      = .localExclude (stepLocalExclude cfg ev.learned (checkpointRegion cp)) := by
  simp only [backjumpStep, han, hcp, hp]

/-- Case (b) routing: the completed-jump arm. -/
theorem backjumpStep_of_perform_some {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf} {restored : BranchState leaf}
    (han : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    backjumpStep cfg ev
      = .learnBackjumpAssert (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          ev restored)
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) an := by
  simp only [backjumpStep, han, hcp, hp]

/-- THE FROZEN POLICY (§9.3): the recorded-evidence step has NO `unsat`
arm — every arm is a proved fallback, a local exclusion, or a completed
learn/backjump/assert. -/
theorem backjumpStep_ne_unsat (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) :
    backjumpStep cfg ev ≠ SchedulerTransition.unsat := by
  cases ha : ev.analysis with
  | none =>
      rw [backjumpStep_of_analysis_none ha]
      intro hh; cases hh
  | some an =>
      cases hc : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          rw [backjumpStep_of_checkpoint_none ha hc]
          intro hh; cases hh
      | some cp =>
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
              cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              rw [backjumpStep_of_perform_none ha hc hp]
              intro hh; cases hh
          | some restored =>
              rw [backjumpStep_of_perform_some ha hc hp]
              intro hh; cases hh

/-- The recorded-evidence phase performs exactly `backjumpStep` on the
recorded payload. -/
theorem schedulerNext_of_conflict {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} (h : cfg.conflict = some ev) :
    schedulerNext cfg = backjumpStep cfg ev := by
  unfold schedulerNext
  rw [h]

/-- Case (c) at the dispatcher: in the recorded-evidence phase the
scheduler never returns `unsat`, whatever the analysis outcome. -/
theorem schedulerNext_conflict_phase_ne_unsat {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} (h : cfg.conflict = some ev) :
    schedulerNext cfg ≠ SchedulerTransition.unsat := by
  rw [schedulerNext_of_conflict h]
  exact backjumpStep_ne_unsat cfg ev

/-- Case (c): an unsupported run routes to the chronological fallback and
NEVER to `unsat`. -/
theorem schedulerNext_unsupported_route {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} (hev : cfg.conflict = some ev)
    (ha : ev.analysis = none) :
    schedulerNext cfg
        = .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) ∧
      schedulerNext cfg ≠ SchedulerTransition.unsat := by
  rw [schedulerNext_of_conflict hev, backjumpStep_of_analysis_none ha]
  exact ⟨rfl, by intro hh; cases hh⟩

/-- Case (c): a completed analysis without a checkpoint falls back. -/
theorem schedulerNext_missing_checkpoint_route {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hev : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = none) :
    schedulerNext cfg
      = .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) := by
  rw [schedulerNext_of_conflict hev, backjumpStep_of_checkpoint_none ha hcp]

/-- Case (c): a rejected assertion excludes the checkpoint's region. -/
theorem schedulerNext_local_exclude_route {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf}
    (hev : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = none) :
    schedulerNext cfg
      = .localExclude (stepLocalExclude cfg ev.learned (checkpointRegion cp)) := by
  rw [schedulerNext_of_conflict hev, backjumpStep_of_perform_none ha hcp hp]

/-- Case (b): a completed analysis with a successful restoration performs
the learn/backjump/assert transition. -/
theorem schedulerNext_analyzable_route {cfg : SchedulerConfig leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf} {restored : BranchState leaf}
    (hev : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    schedulerNext cfg
      = .learnBackjumpAssert (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          ev restored)
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) an := by
  rw [schedulerNext_of_conflict hev, backjumpStep_of_perform_some ha hcp hp]

/-! ## The classification of the executable analysis -/

theorem analyzeClassified_eq_of_allowance {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl c = some (below, uip)) :
    analyzeClassified orig trail lvl c = AnalysisOutcome.success below uip := by
  unfold analyzeClassified
  rw [h]

theorem analyzeClassified_eq_of_none {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} (h : analyzeAtAllowance orig trail lvl c = none) :
    analyzeClassified orig trail lvl c
      = (if lvl = 0 then AnalysisOutcome.rootContradiction
         else AnalysisOutcome.unsupported) := by
  unfold analyzeClassified
  rw [h]

/-- §9.3 item 1: `.unsupported` is exactly "no result above the root" —
the fallback trigger, never a verdict. -/
theorem analyzeClassified_unsupported {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause}
    (h : analyzeClassified orig trail lvl c = AnalysisOutcome.unsupported) :
    analyzeAtAllowance orig trail lvl c = none ∧ lvl ≠ 0 := by
  unfold analyzeClassified at h
  cases h' : analyzeAtAllowance orig trail lvl c with
  | none =>
      by_cases h0 : lvl = 0
      · simp only [h'] at h
        simp only [h0, if_true] at h
        cases h
      · exact ⟨by first | rfl | exact h', h0⟩
  | some p =>
      obtain ⟨b, u⟩ := p
      simp only [h'] at h
      cases h

/-- §9.3 item 2: `.rootContradiction` is exactly "no result at level 0" —
the route that requires `AnalyzerInput` + `RootFactsBridge`. -/
theorem analyzeClassified_rootContradiction {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause}
    (h : analyzeClassified orig trail lvl c = AnalysisOutcome.rootContradiction) :
    analyzeAtAllowance orig trail lvl c = none ∧ lvl = 0 := by
  unfold analyzeClassified at h
  cases h' : analyzeAtAllowance orig trail lvl c with
  | none =>
      by_cases h0 : lvl = 0
      · exact ⟨by first | rfl | exact h', h0⟩
      · simp only [h'] at h
        simp only [h0, if_false] at h
        cases h
  | some p =>
      obtain ⟨b, u⟩ := p
      simp only [h'] at h
      cases h

/-- §2.3 item 18: the `.success` classification is exactly the completed
run's result — the certificate inputs for real conflict events. -/
theorem analyzeClassified_eq_success_iff {orig : List Domain} {trail : List TrailEntry} {lvl : Nat}
    {c : Clause} {below : List (Literal × Nat)} {uip : Literal} :
    analyzeClassified orig trail lvl c = AnalysisOutcome.success below uip ↔
      analyzeAtAllowance orig trail lvl c = some (below, uip) := by
  unfold analyzeClassified
  cases h : analyzeAtAllowance orig trail lvl c with
  | none =>
      dsimp only
      constructor
      · intro hc
        by_cases h0 : lvl = 0
        · rw [if_pos h0] at hc
          cases hc
        · rw [if_neg h0] at hc
          cases hc
      · intro hc
        cases hc
  | some p =>
      obtain ⟨b, u⟩ := p
      dsimp only
      constructor
      · intro hc
        cases hc
        rfl
      · intro hc
        cases hc
        rfl

/-! ## FINDING — the root arm does not consult the analyzer -/

/-- The executable analysis has NO result on the trail-empty,
single-`intNe`-literal clause: the falsifier lookup fails, so `markLit`
stops the loop with `none`. -/
theorem analyzeAtAllowance_intNe_nil :
    analyzeAtAllowance [Dom.ofList [.int 0, .int 1]] ([] : List TrailEntry) 0
      [⟨.intNe 0 0, true⟩] = none := by decide

/-- FINDING (root-arm evidence gap, not a soundness bug): the level-0
`.unsat` arm is NOT a function of the executable analysis. At the real
root configuration with the unanalyzable clause `[intNe 0 0]` the
dispatch returns `.unsat` while `analyzeAtAllowance` has no result at all
— so the root verdict's justification must come from the caller's
`AnalyzerInput` + `RootFactsBridge` (`rootContradiction_sound`), exactly
as §9.3 requires. The `.unsat` arm of `conflictStep` is also
level-monotone: it fires for ANY level-0 configuration, whichever the
analysis outcome. -/
example :
    conflictStep (SchedulerConfig.init (leaf := fun _ => false)
      (orig := []) (original := []) (props := []))
      [[(⟨Atom.intNe 0 0, true⟩ : Literal)]] [] = .unsat := by
  rw [conflictStep_of_level_zero]
  rfl


/-! ## N1: normalized-unit learned preservation across the actual arms

The recording-site normalization plus the supported kit's unit profile make
the ACTUAL run's learned clauses normalized units. This section proves the
run invariant by induction over the real dispatcher: every learned-database
update is classified and discharged by a named lemma. No unit-run property
is assumed at any site. -/

/-- **N1 NORMALIZED-UNIT ANALYSIS CLAUSE**: the recording site's stored
analysis of a SINGLETON conflict clause has a normalized-unit learned
clause — `analyzeAtAllowance_singleton_below` empties the below list and
the canonical form maps the remaining head to its own normal form. -/
theorem unitLearned_ofUIP_normalized_of_singleton {trail : List TrailEntry}
    {lvl : Nat} {q : Literal} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance orig trail lvl [q] = some (below, uip)) :
    ∃ q' : Literal,
      (ConflictAnalysis.ofUIP below uip).normalized.learned = [q'] ∧
        q' = q'.norm := by
  have hb := analyzeAtAllowance_singleton_below h
  subst hb
  refine ⟨(uip.negate).norm, ?_, (norm_norm uip.negate).symm⟩
  rw [ConflictAnalysis.normalized_learned, ConflictAnalysis.ofUIP_learned]
  simp

/-- N1 TERMINAL PAYLOAD UNIT: the terminal result's new clauses are
unit-learned under the supported kit — the conflict row's freshness filter
of a normalized-unit payload, the implied row's single-clause payload, and
the stable row's empty list. -/
theorem unitLearned_terminalResult_newClauses {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hdb : UnitLearned bs.learned) :
    UnitLearned (terminalResult orig original props bs).newClauses := by
  have hprof : UnitRunProfile props := by
    rw [hprops]
    exact unitRunProfile_proved dcs hSupp
  cases ht : terminalResult orig original props bs with
  | stable s =>
      show UnitLearned ([] : List Clause)
      exact unitLearned_nil
  | conflict s cs learned =>
      show UnitLearned learned
      obtain ⟨-, hcase⟩ := terminalResult_conflict_cases ht
      rcases hcase with ⟨hevent, hlearned⟩ | ⟨l, c, lr, fl, hevent, -, -, hlearned⟩ |
          ⟨w, -, -, -, hlearned⟩
      · rw [hlearned]
        exact unitLearned_excluded_learned hprof hevent
      · rw [hlearned]
        exact unitLearned_implied_payload hprof hdb hevent
      · rw [hlearned]
        exact unitLearned_nil
  | localExcluded s lit reason learned =>
      exact absurd ht terminalResult_ne_localExcluded

/-- The restored-and-narrowed state's learned database is the plan's
learned clause consed onto the predecessor's (`BackjumpPlan.execute`'s
`learnGlobal` insertion). -/
theorem unitLearned_restoreNarrow {leaf : Assignment → Bool}
    {bs s : BranchState leaf} {p : BackjumpPlan leaf}
    (hdb : UnitLearned bs.learned)
    (hlearned : ∃ q : Literal, p.learned = [q] ∧ q = q.norm)
    (h : p.restoreNarrow bs = some s) :
    UnitLearned s.learned := by
  obtain ⟨q, hq, hqn⟩ := hlearned
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · cases h
    show UnitLearned (p.learned :: bs.learned)
    rw [hq]
    exact unitLearned_append (unitLearned_singleton hqn) hdb

/-- N1 JUMP INSERTION: `BackjumpPlan.perform` preserves the unit-learned
discipline under the kit's unit profile — the plan's analyzed clause is a
normalized unit (N1's singleton-analyzer lemma) and the closure's resumed
learning keeps the database unit-learned. -/
theorem unitLearned_perform {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator}
    {bs restored : BranchState leaf} {p : BackjumpPlan leaf}
    (hProps : UnitRunProfile props) (hdb : UnitLearned bs.learned)
    (hlearned : ∃ q : Literal, p.learned = [q] ∧ q = q.norm)
    (h : p.perform bs orig original props = some restored) :
    UnitLearned restored.learned := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr] at h
      cases h
  | some s =>
      have hRN : UnitLearned s.learned := unitLearned_restoreNarrow hdb hlearned hr
      simp only [hr, Option.map_some, Option.some.injEq] at h
      subst h
      exact unitLearned_explainedClosure orig original props _ hProps
        (by rw [syncAll_learned]; exact hRN)

/-- THE NORMALIZED-UNIT RUN INVARIANT of a scheduler configuration under
the supported kit: the branch's learned database is unit-learned, and every
recorded conflict evidence carries a normalized-unit reported clause
together with a unit-learned payload. -/
structure UnitRunInvariant {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop where
  /-- the branch's learned database is unit-learned -/
  db : UnitLearned cfg.branch.learned
  /-- every recorded evidence: singleton normalized reported clause and a
      unit-learned payload -/
  recorded : ∀ ev : ConflictEvidence, cfg.conflict = some ev →
    (∃ q : Literal, ev.clause = [q] ∧ q = q.norm) ∧ UnitLearned ev.learned

/-- **N1 UNIT-RUN PRESERVATION (one real dispatcher step)**: every successor
of the real dispatcher preserves the normalized-unit run invariant under
the supported kit's unit profile. Arm table = `C2d.schedulerNext_cases`. -/
theorem unitRunInvariant_step {leaf : Assignment → Bool}
    {dcs : List DomConstraint} {cfg cfg' : SchedulerConfig leaf}
    (hprops : cfg.props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinv : UnitRunInvariant cfg) (hreach : SchedulerReachable cfg)
    (hnw : wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame = none)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    UnitRunInvariant cfg' := by
  have hprof : UnitRunProfile cfg.props := by
    rw [hprops]
    exact unitRunProfile_proved dcs hSupp
  rcases C2d.schedulerNext_cases (leaf := leaf) cfg with
    ⟨ev, hc, hnx⟩ | ⟨hconf, hdead, hnx⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence — backjumpStep
    rw [hnx] at hsucc
    unfold backjumpStep at hsucc
    cases ha : ev.analysis with
    | none =>
        simp only [ha, successor_chronologicalFallback, Option.some.injEq] at hsucc
        subst hsucc
        refine ⟨?_, ?_⟩
        · show UnitLearned cfg.branch.learned
          exact hinv.db
        · intro ev' hev'
          rw [stepChronologicalFallback_conflict] at hev'
          cases hev'
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            simp only [ha, hcp, successor_chronologicalFallback,
              Option.some.injEq] at hsucc
            subst hsucc
            refine ⟨?_, ?_⟩
            · show UnitLearned cfg.branch.learned
              exact hinv.db
            · intro ev' hev'
              rw [stepChronologicalFallback_conflict] at hev'
              cases hev'
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                simp only [ha, hcp, hp, successor_localExclude,
                  Option.some.injEq] at hsucc
                subst hsucc
                refine ⟨?_, ?_⟩
                · show UnitLearned (ev.learned ++ cfg.branch.learned)
                  exact unitLearned_append (hinv.recorded ev hc).2 hinv.db
                · intro ev' hev'
                  rw [stepLocalExclude_conflict] at hev'
                  cases hev'
            | some restored =>
                simp only [ha, hcp, hp, successor_learnBackjumpAssert,
                  Option.some.injEq] at hsucc
                subst hsucc
                obtain ⟨⟨q, hq, hqn⟩, hpay⟩ := hinv.recorded ev hc
                have hana : ∃ q' : Literal, an.learned = [q'] ∧ q' = q'.norm := by
                  obtain ⟨below, uip, hrun, heq⟩ :=
                    reachable_analysis_success leaf cfg ev an hreach hc ha
                  rw [hq] at hrun
                  obtain ⟨q', hq', hqn'⟩ :=
                    unitLearned_ofUIP_normalized_of_singleton hrun
                  exact ⟨q', by rw [heq, hq'], hqn'⟩
                refine ⟨?_, ?_⟩
                · show UnitLearned (ev.learned ++ restored.learned)
                  exact unitLearned_append hpay
                    (unitLearned_perform hprof hinv.db hana hp)
                · intro ev' hev'
                  rw [stepLearnBackjumpAssert_conflict] at hev'
                  cases hev'
  · -- ROUTE 2: dead branch — consumeStep
    rw [hnx] at hsucc
    unfold consumeStep at hsucc
    split at hsucc
    · rename_i next hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      subst hsucc
      refine ⟨?_, ?_⟩
      · rw [stepConsume_learned hcs]
        exact hinv.db
      · intro ev' hev'
        rw [stepConsume_conflict hcs] at hev'
        cases hev'
    · simp only [successor_unsat] at hsucc
      cases hsucc
  · -- ROUTE 3: active branch
    rcases hrest with ⟨d, hd, hnx'⟩ | ⟨bs, ht, hnx'⟩ |
      ⟨bs, cs, learned, ht, hnx'⟩ | ⟨bs, lit, reason, learned, ht, hnx'⟩
    · -- propagation
      rw [hnx'] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      subst hsucc
      refine ⟨?_, ?_⟩
      · rw [stepPropagate_branch_learned]
        exact unitLearned_append
          (unitLearned_deduction_learned hd (deduction_reason_unit hprof hinv.db hd))
          hinv.db
      · intro ev' hev'
        rw [stepPropagate_conflict] at hev'
        rw [hconf] at hev'
        cases hev'
    · -- guarded stable dispatch
      rw [hnx'] at hsucc
      unfold stableStepGuarded at hsucc
      split at hsucc
      · simp only [successor_sat] at hsucc
        cases hsucc
      · split at hsucc
        · rename_i l v vs doms hsp
          split at hsucc
          · -- redundant-pin skip: branch learned unchanged
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            refine ⟨?_, ?_⟩
            · rw [stepDecideSkip_learned]
              exact hinv.db
            · intro ev' hev'
              rw [stepDecideSkip_conflict] at hev'
              rw [hconf] at hev'
              cases hev'
          · -- fresh decision: branch learned unchanged
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            refine ⟨?_, ?_⟩
            · rw [stepDecide_learned]
              exact hinv.db
            · intro ev' hev'
              rw [stepDecide_conflict] at hev'
              rw [hconf] at hev'
              cases hev'
        · -- finished-but-failing branch: empty payload
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          refine ⟨?_, ?_⟩
          · show UnitLearned ([] ++ cfg.branch.learned)
            simpa using hinv.db
          · intro ev' hev'
            rw [stepLocalExclude_conflict] at hev'
            cases hev'
    · -- recorded conflict dispatch
      cases cs with
      | nil =>
          rw [hnx'] at hsucc
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          refine ⟨?_, ?_⟩
          · obtain ⟨-, hcase⟩ := terminalResult_conflict_cases ht
            show UnitLearned (learned ++ cfg.branch.learned)
            rcases hcase with ⟨-, hlearned⟩ | ⟨l', c', lr', fl', -, -, hcs', -⟩ |
                ⟨w', -, -, hcs', -⟩
            · rw [hlearned]
              simpa using hinv.db
            · cases hcs'
            · cases hcs'
          · intro ev' hev'
            rw [stepLocalExclude_conflict] at hev'
            cases hev'
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · rw [hnx'] at hsucc
            simp only [conflictStep, if_pos hlv, successor_unsat] at hsucc
            cases hsucc
          · rw [hnx'] at hsucc
            simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hsucc
            subst hsucc
            have hprof : UnitRunProfile cfg.props := by
              rw [hprops]
              exact unitRunProfile_proved dcs hSupp
            obtain ⟨-, hcase⟩ := terminalResult_conflict_cases ht
            have hcq' : (∃ q : Literal, c = [q] ∧ q = q.norm) ∧
                UnitLearned learned := by
              rcases hcase with ⟨hevent, hlearned⟩ |
                  ⟨l', c', lr', fl', hevent, -, hcs', hlearned⟩ |
                  ⟨w', -, hw', -, -⟩
              · have hevent' := hevent
                rw [hprops] at hevent'
                obtain ⟨-, q, hcq, hqn⟩ :=
                  supported_conflict_clause_unit hSupp hinv.db hevent'
                refine ⟨⟨q, hcq, hqn⟩, ?_⟩
                rw [hlearned]
                exact unitLearned_excluded_learned hprof hevent
              · injection hcs' with hc' hrest'
                obtain ⟨q, hq, hqn⟩ := implied_reason_unit hprof hinv.db hevent
                refine ⟨⟨q, by rw [hc', hq], hqn⟩, ?_⟩
                rw [hlearned]
                exact unitLearned_implied_payload hprof hinv.db hevent
              · exact absurd (hnw.symm.trans hw') (by simp)
            obtain ⟨⟨q, hcq, hqn⟩, hpay⟩ := hcq'
            refine ⟨?_, ?_⟩
            · rw [stepAnalyzeConflictCounted_branch]
              exact hinv.db
            · intro ev' hev'
              obtain ⟨hcl, hlearned', -⟩ :=
                stepAnalyzeConflictCounted_evidence hev'
              refine ⟨⟨q, ?_, hqn⟩, ?_⟩
              · rw [hcl, hcq]
              · rw [hlearned']
                exact hpay
    · -- the local-exclusion terminal result
      rw [hnx'] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      refine ⟨?_, ?_⟩
      · have h : UnitLearned
            (terminalResult cfg.orig cfg.original cfg.props cfg.branch).newClauses :=
          unitLearned_terminalResult_newClauses hprops hSupp hinv.db
        rw [ht] at h
        show UnitLearned (learned ++ cfg.branch.learned)
        exact unitLearned_append h hinv.db
      · intro ev' hev'
        rw [stepLocalExclude_conflict] at hev'
        cases hev'

/-- **N1 NORMALIZED-UNIT RUN PRESERVATION**: every reachable configuration
of the supported kit satisfies the unit-run invariant — the ACTUAL run's
learned clauses are normalized units and every recorded evidence carries a
normalized-unit reported clause with a unit-learned payload. No unit-run
property is assumed: the induction applies `unitRunInvariant_step` to each
real dispatcher successor (`W1.schedulerNext_succ_inputs` transports the
kit equation). -/
theorem unitRunInvariant_of_reachable {leaf : Assignment → Bool}
    {dcs : List DomConstraint}
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hnw : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame = none) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.props = dcs.filterMap propagatorOfProved →
      UnitLearned cfg.original → UnitRunInvariant cfg := by
  intro cfg h
  refine SchedulerReachable.rec
    (motive := fun cfg _ =>
      cfg.props = dcs.filterMap propagatorOfProved →
      UnitLearned cfg.original → UnitRunInvariant cfg)
    ?_ ?_ h
  · intro orig' original' props _ _ hent hprops' hunit
    refine ⟨?_, ?_⟩
    · exact hunit
    · intro ev hev
      cases hev
  · intro cfg cfg' t hnext hsucc hrec ih hprops' hunit
    rw [← hnext] at hsucc
    have hpropsOld : cfg.props = dcs.filterMap propagatorOfProved :=
      (W1.schedulerNext_succ_inputs hsucc).2.2.symm.trans hprops'
    have hunitOld : UnitLearned cfg.original :=
      (W1.schedulerNext_succ_inputs hsucc).2.1.symm ▸ hunit
    exact unitRunInvariant_step (cfg := cfg) (cfg' := cfg')
      hpropsOld hSupp (ih hpropsOld hunitOld) hrec (hnw hrec) hsucc

/-! ### N1 regressions (Boolean shape, inhabitedness, verdict neutrality) -/

/-- N1 BOOLEAN REGRESSION: the canonical form of the singleton analysis
record of the `boolEq` conflict is the normalized unit `[posBool 0 false]`. -/
example : (ConflictAnalysis.ofUIP [] (posBool 0 true)).normalized.learned
    = [posBool 0 false] := rfl

/-- N1 BOOLEAN REGRESSION (recording-site end-to-end): the map the recording
site applies to the executable singleton run of the Boolean conflict stores
exactly that normalized unit. -/
example :
    ((analyzeAtAllowance [Dom.ofList [.bool false, .bool true]]
        [{ literal := posBool 0 true, level := 1, reason := none }] 1
        [posBool 0 false]).map
          (fun p => (ConflictAnalysis.ofUIP p.1 p.2).normalized)).map
      ConflictAnalysis.learned = some [posBool 0 false] := by decide

/-- N1 VERDICT NEUTRALITY: normalization preserves the learned literal's
evaluation at every assignment (`Literal.norm_eval`; the full certificate
lift is `RestorationCertificate.normalized`). -/
example (a : Assignment) :
    ((posBool 0 true).negate.norm).eval a
      = ((posBool 0 true).negate).eval a :=
  Literal.norm_eval _ a

/-- N1 INHABITEDNESS: the supported kit's root configuration satisfies the
unit-run invariant (empty database, no recorded evidence) — the invariant
is not vacuous. -/
example {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hunit : UnitLearned original) :
    UnitRunInvariant (SchedulerConfig.init (leaf := leaf) orig original props) := by
  refine ⟨?_, ?_⟩
  · exact hunit
  · intro ev hev
    cases hev

end LeanFzn.Solver.UIP
