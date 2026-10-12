/-
File: LeanFzn/Solver/UIP/Proofs/AnalysisEntail.lean

Purpose: THE ANALYSIS-ENTAILMENT BRIDGE `hAnalysisEntail` — the last
semantic premise of the compiled unit-kit instance. The branch reachable
while a conflict's evidence is RECORDED (SchedulerStep's
`stepAnalyzeConflict`, reached through `conflictStep` from the closure's
`terminalResult = .conflict cs learned`) must learn only globally
entailed clauses; the recorded analysis is
`(analyzeAtAllowance trail level ev.clause).map (ofUIP · ·).normalized`,
so the bridge has to connect the CLAUSE the closure reported (entailed by
`ClosureContract.conflictEntailed` at the recording step) with the
learned clause of the executable first-UIP run.

Two layers, each exported:

§1 THE RECORDED CLAUSE IS ENTAILED (kit-independent).
   `recordedClause_entailed_of_supported`: at every supported-reachable
   configuration carrying recorded evidence, `LearnedEntailed leaf
   [ev.clause]`. The evidence exposes the closure's payload because the
   ONLY transition installing `some` evidence is the recording site
   (`schedulerNext_successor_recording_or_none`, the payload-exposing
   strengthening of `schedulerNext_successor_conflict_classification`),
   whose `terminalResult = .conflict cfg.branch cs learned` and
   `ev.clause = cs.head` are then fed to `ClosureContract.conflictEntailed`
   at the PRE-state (its branch is unchanged by the recording step, so
   the site's own `ReachableState` rewrites back to the pre-state).

§2 THE SINGLETON-ANALYSIS TRANSPORT (the unit kit).
   `analyzeAtAllowance_singleton_uip`: a successful singleton run's
   `below` list is empty AND its UIP is the normalized negation of the
   scanned literal `q.norm` or of its `orderUpgrade` — the markLit
   falsifier shape of the CURRENT level. `learnedEntailed_singleton_run`
   then transports entailment of `q` to entailment of the learned
   singleton `[(uip.negate).norm]` (`orderUpgrade_weaken`,
   `negate_norm_square`, `Literal.norm_eval`).

§3 THE BRIDGE. `unitAnalysisEntailed_site` composes them under the unit
kit (`props = dcs.filterMap propagatorOfProved`, every `unitFamilyB dc =
true`), using `unitRunInvariant_of_reachable`'s `.recorded` component for
`ev.clause = [q]` (N1) and `reachable_analysis_success` for the canonical
record shape. `hAnalysisEntail_unitKit` is the exact family shape the I1
assembly consumes (SupportedReach → ClosureContract → ReachableState →
cfg.conflict = some ev → ev.analysis = some an → LearnedEntailed leaf
[an.learned]), with NO residual beyond the kit equations.

FINDING (recorded, not hidden): the kit-independent §1 shows the general
bridge's only remaining ingredient is the analyzer's resolution-soundness
argument for ARBITRARY conflict clauses, which needs a further premise
than the site shape provides — a root-facts discipline for level-0
falsifiers (`markLit`'s root-drop outcome is justified by level-0 trail
facts holding at every leaf solution, `RootFacts`/`RootFactsBridge` at
the compiled level; `ClosureContract` supplies no such field). The unit
kit avoids the premise entirely: a SUCCESSFUL singleton run can only mark
a CURRENT-level falsifier, so no root-drop occurs (`markLit_inv`'s third
disjunct).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.AnalysisEntail` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.SupportedRun
import LeanFzn.Solver.UIP.Proofs.SchedulerConflict
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Solver.UIP.Proofs.AnalyzeSingleton
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.ExplainedPropagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The recorded clause is entailed (kit-independent)

The successor classification below is the payload-exposing strengthening
of `schedulerNext_successor_conflict_classification`
(`Proofs/SchedulerReachable.lean`): the same case analysis, but the
recording arm keeps the discovered closure payload `cs` and the
`terminalResult` equation that produced it, which is what links
`ev.clause = cs.head` to `ClosureContract.conflictEntailed`. -/

/-- SUCCESSOR CLASSIFICATION WITH THE CLOSURE PAYLOAD EXPOSED: a
non-terminal successor of a configuration with no recorded evidence
either carries no evidence, or is the recording site's successor of the
predicate's closure payload — `terminalResult cfg.original cfg.props
cfg.branch = .conflict cfg.branch cs learned` with `cs = c :: rest`
recorded as `ev.clause = c` and `learned` as `ev.learned`. -/
theorem schedulerNext_successor_recording_or_none {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {t : SchedulerTransition leaf}
    (hc : cfg.conflict = none) (hnext : schedulerNext cfg = t)
    (hsucc : t.successor = some cfg') :
    cfg'.conflict = none ∨
      ∃ (cs learned : List Clause) (c : Clause) (rest : List Clause),
        terminalResult cfg.original cfg.props cfg.branch
            = .conflict cfg.branch cs learned ∧
          cs = c :: rest ∧
          cfg' = stepAnalyzeConflictCounted cfg c learned
            (analyzeEventsExpansions cfg.branch.trail cfg.branch.level c) := by
  cases hst : cfg.status with
  | dead =>
      have ht : consumeStep cfg = t := by
        simp only [schedulerNext, hc, hst] at hnext
        exact hnext
      rw [← ht] at hsucc
      exact Or.inl (consumeStep_successor_conflict hsucc)
  | active =>
      cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
      | some d =>
          have ht : SchedulerTransition.propagate (stepPropagate cfg d) = t := by
            simp only [schedulerNext, hc, hst, hd] at hnext
            exact hnext
          rw [← ht] at hsucc
          rw [successor_propagate] at hsucc
          cases hsucc
          exact Or.inl (by rw [stepPropagate_conflict, hc])
      | none =>
          cases htt : terminalResult cfg.original cfg.props cfg.branch with
          | stable st =>
              have ht : stableStepGuarded cfg = t := by
                simp only [schedulerNext, hc, hst, hd, htt] at hnext
                exact hnext
              rw [← ht] at hsucc
              exact Or.inl (stableStepGuarded_successor_conflict_none hc hsucc)
          | conflict st cs learned =>
              have ht : conflictStep cfg cs learned = t := by
                simp only [schedulerNext, hc, hst, hd, htt] at hnext
                exact hnext
              rw [← ht] at hsucc
              rcases conflictStep_successor_conflict hc hsucc with
                hnone | ⟨c, rest, hcs, heq⟩
              · exact Or.inl hnone
              · have hst : st = cfg.branch :=
                  (nextPruningEvent_of_terminalResult_conflict htt).2.1
                exact Or.inr ⟨cs, learned, c, rest, by rw [← hst], hcs, heq⟩
          | localExcluded st lit reason learned =>
              have ht :
                  SchedulerTransition.localExclude
                    (stepLocalExclude cfg learned (branchRegion cfg)) = t := by
                simp only [schedulerNext, hc, hst, hd, htt] at hnext
                exact hnext
              rw [← ht] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact Or.inl rfl

/-- ONE STEP: the recorded evidence of a real successor carries an
entailed clause. The predecessor with recorded evidence has no successor
carrying evidence (`backjumpStep` clears it), so the only case is the
recording site, where the site's `SideInv`-free premises
(`SupportedReach` of the PRE-state, the site's own `ReachableState` of
the unchanged branch, the closure contract) are read through the payload
equation of §1's classification. -/
theorem recordedClause_entailed_of_step {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    {ev : ConflictEvidence}
    (hcontract : ClosureContract leaf orig original props)
    (hrec : SupportedReach orig original props cfg)
    (hs : (schedulerNext cfg).successor = some cfg')
    (hbr : ReachableState leaf orig cfg'.branch)
    (hconf : cfg'.conflict = some ev) :
    LearnedEntailed leaf [ev.clause] := by
  cases hcf : cfg.conflict with
  | some ev₀ =>
      have hnext : schedulerNext cfg = backjumpStep cfg ev₀ := by
        simp only [schedulerNext, hcf]
      rw [hnext] at hs
      have hnone := backjumpStep_successor_conflict_none hs
      rw [hnone] at hconf
      cases hconf
  | none =>
      rcases schedulerNext_successor_recording_or_none hcf rfl hs with
        hnone | ⟨cs, learned, c, rest, htr, hcs, hcfg⟩
      · rw [hnone] at hconf
        cases hconf
      · rw [hcfg] at hbr hconf
        rw [hcs] at htr
        obtain ⟨hcl, -, -⟩ := stepAnalyzeConflictCounted_evidence hconf
        -- the closure's conflict event at the PRE-state
        have hevnt : nextPruningEvent cfg.original cfg.props cfg.branch.frame
            cfg.branch.learned = .conflict (c :: rest) :=
          (nextPruningEvent_of_terminalResult_conflict htr).1
        rw [SupportedReach.original_eq hrec, SupportedReach.props_eq hrec] at hevnt
        -- the recording step leaves the branch unchanged
        have hbr₀ : ReachableState leaf orig cfg.branch := by
          simpa only [stepAnalyzeConflictCounted_branch, stepAnalyzeConflict_branch]
            using hbr
        have hcsent : LearnedEntailed leaf (c :: rest) :=
          hcontract.conflictEntailed cfg.branch hbr₀ (c :: rest) hevnt
        have hcent : LearnedEntailed leaf [c] := by
          intro c' hc' a ha
          rw [List.mem_singleton] at hc'
          rw [hc']
          exact hcsent c (List.mem_cons_self ..) a ha
        rw [hcl]
        exact hcent

/-- THE RECORDED CLAUSE IS ENTAILED, run level: every supported-reachable
configuration carrying recorded evidence satisfies `LearnedEntailed leaf
[ev.clause]`. Structural induction over `SupportedReach` (the initializer
has no evidence; the step is §1-style `recordedClause_entailed_of_step`,
whose only run-level input is the predecessor's `SupportedReach` for the
static-frame rewrites). -/
theorem recordedClause_entailed_of_supported {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hcontract : ClosureContract leaf orig original props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ {ev : ConflictEvidence}, ReachableState leaf orig cfg.branch →
        cfg.conflict = some ev → LearnedEntailed leaf [ev.clause] := by
  intro cfg hreach
  induction hreach with
  | init =>
      intro ev hbr hconf
      simp [SchedulerConfig.init] at hconf
  | step hrec hs ih =>
      intro ev hbr hconf
      exact recordedClause_entailed_of_step hcontract hrec hs hbr hconf

/-! ## §2 The singleton analysis shape and its entailment transport -/

/-- THE SINGLETON ANALYSIS SHAPE: a successful `analyzeAtAllowance` run on
a singleton clause `[q]` has an EMPTY below list and returns a UIP that is
the normalized negation of the scanned literal's normal form `q.norm` or
of its `orderUpgrade` — the only `markLit` outcome compatible with a
nonempty mark set and a surviving run is the CURRENT-level mark
(`markLit_inv`'s third disjunct), and `nextPivot`'s match returns that
mark's literal (`nextPivot_mark`). -/
theorem analyzeAtAllowance_singleton_uip {trail : List TrailEntry}
    {lvl : Nat} {q : Literal} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance trail lvl [q] = some (below, uip)) :
    below = [] ∧
      ∃ q' : Literal, (q' = q.norm ∨ q' = orderUpgrade trail q.norm) ∧
        uip = q'.negate.norm := by
  unfold analyzeAtAllowance at h
  suffices hgen : ∀ fuel : Nat,
      analyzeStep trail lvl fuel [[q]] none [] [] = some (below, uip) →
      below = [] ∧ ∃ q' : Literal,
        (q' = q.norm ∨ q' = orderUpgrade trail q.norm) ∧
          uip = q'.negate.norm from hgen _ h
  intro fuel
  cases fuel with
  | zero =>
      intro h
      simp only [analyzeStep] at h
      exact absurd h (by simp)
  | succ f₁ =>
      cases f₁ with
      | zero =>
          intro h
          simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
          cases hm0 : markLit trail lvl [] [] q.norm <;> simp_all
      | succ f₂ =>
          cases f₂ with
          | zero =>
              intro h
              simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
              cases hm0 : markLit trail lvl [] [] q.norm <;> simp_all
          | succ f₃ =>
              intro h
              simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
              cases hm : markLit trail lvl [] [] q.norm with
              | none =>
                  simp only [hm] at h
                  cases h
              | some p =>
                  obtain ⟨m₁, l₁⟩ := p
                  simp only [hm] at h
                  change analyzeStep trail lvl (Nat.succ f₃) [] none m₁ l₁ =
                    some (below, uip) at h
                  cases m₁ with
                  | nil =>
                      exact absurd h (by
                        rw [analyzeStep_emptyMarks_none trail lvl (Nat.succ f₃) l₁]
                        simp)
                  | cons e rest =>
                      rcases markLit_inv trail lvl [] [] q.norm (e :: rest) l₁ hm with
                        ⟨m, hm_mem, -, -, -⟩ |
                        ⟨p, hp_mem, -, -, -⟩ |
                        ⟨e₂, -, q', hq', helit, hmarks, hl₁, -⟩ |
                        ⟨e₂, -, q', hq', helit, hmarks, -, -, -⟩ |
                        ⟨e₂, -, q', hq', helit, hmarks, -, -⟩
                      · exact absurd hm_mem (by simp)
                      · exact absurd hp_mem (by simp)
                      · rw [hl₁] at h
                        rw [hmarks] at h
                        simp only [analyzeStep] at h
                        cases hnp : nextPivot trail [e₂] with
                        | none =>
                            simp only [hnp] at h
                            cases h
                        | some e₃ =>
                            obtain ⟨m, hm_mem', hm_lit⟩ :=
                              nextPivot_mark trail [e₂] e₃ hnp
                            have hme : m = e₂ := by simpa using hm_mem'
                            subst hme
                            have hliteq : litEqB m.literal e₃.literal = true := by
                              rw [hm_lit]
                              exact litEqB_self e₃.literal
                            simp only [hnp, List.filter_cons, List.filter_nil,
                              hliteq, Bool.not_true, Bool.false_eq_true,
                              if_false, if_true, List.isEmpty_nil] at h
                            obtain ⟨hbl, huip⟩ := Prod.mk.inj (Option.some.inj h)
                            refine ⟨hbl.symm, q', ?_, ?_⟩
                            · rcases hq' with hqq | hqq
                              · left
                                rw [hqq, norm_norm]
                              · right
                                rw [hqq, norm_norm]
                            · rw [← huip, ← hm_lit, helit]
                      · exact absurd hmarks (by simp)
                      · exact absurd hmarks (by simp)

/-- THE ENTAILMENT TRANSPORT across the singleton analysis: if the scanned
literal `q` holds at every leaf solution, so does the analyzed singleton
clause `[(uip.negate).norm]`. The UIP is (the normalized negation of) `q`
or of `q`'s order upgrade — both WEAKER than `q` (`orderUpgrade_weaken`),
so the witness transfers through `negate_norm_square` and
`Literal.norm_eval`. -/
theorem learnedEntailed_singleton_run {leaf : Assignment → Bool}
    {trail : List TrailEntry} {q uip : Literal}
    (hqent : ∀ a, leaf a = true → q.eval a = some true)
    (huip : ∃ q' : Literal,
      (q' = q.norm ∨ q' = orderUpgrade trail q.norm) ∧ uip = q'.negate.norm) :
    LearnedEntailed leaf [[(uip.negate).norm]] := by
  obtain ⟨q', hq'case, huip'⟩ := huip
  rw [huip', negate_norm_square q']
  intro c hc a hleaf
  rw [List.mem_singleton] at hc
  rw [hc]
  refine ⟨q'.norm, List.mem_singleton_self _, ?_⟩
  rw [Literal.norm_eval q' a]
  rcases hq'case with hqq | hqq
  · rw [hqq, Literal.norm_eval q a]
    exact hqent a hleaf
  · rw [hqq]
    exact orderUpgrade_weaken trail q.norm a (by
      rw [Literal.norm_eval q a]
      exact hqent a hleaf)

/-! ## §3 The site lemma and the family shape

The unit kit's recorded evidence is a normalized singleton
(`unitRunInvariant_of_reachable`'s `.recorded` component), the recorded
analysis is the canonical form of a genuine successful allowance run
(`reachable_analysis_success`), and the closure contract's conflict
entailment reaches the recording step's payload (§1). The chain closes:
`LearnedEntailed leaf [an.learned]` with NO residual beyond the kit
equations. -/

/-- **THE ANALYSIS-ENTAILMENT SITE LEMMA (I1-B, unit kit)**: at a
supported site carrying recorded evidence whose analysis is `some an`, the
analysis's learned clause is globally entailed. -/
theorem unitAnalysisEntailed_site {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hreach : SupportedReach orig original props cfg)
    (hcontract : ClosureContract leaf orig original props)
    (hbr : ReachableState leaf orig cfg.branch)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    LearnedEntailed leaf [an.learned] := by
  -- the recorded clause is entailed (kit-independent §1)
  have hclause : LearnedEntailed leaf [ev.clause] :=
    recordedClause_entailed_of_supported hcontract hreach hbr hconf
  -- the unit kit's recorded event is a NORMALIZED singleton (N1)
  obtain ⟨⟨q, hq, -⟩, -⟩ :=
    (unitRunInvariant_of_reachable (leaf := leaf) hSupp hreach.reachable
      (by rw [SupportedReach.props_eq hreach, hprops])).recorded ev hconf
  -- the recorded analysis is a genuine successful canonical allowance run
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  rw [hq] at hrun
  -- … whose singleton shape empties the below list and pins the UIP
  obtain ⟨hbelow, huipshape⟩ := analyzeAtAllowance_singleton_uip hrun
  -- the clause literal is entailed
  have hqent : ∀ a, leaf a = true → q.eval a = some true := by
    intro a ha
    have h := hclause [q] (by rw [hq]; exact List.mem_singleton_self [q]) a ha
    obtain ⟨l, hl, hev⟩ := h
    rw [List.mem_singleton] at hl
    rwa [hl] at hev
  -- the canonical record's learned clause is the analyzed singleton
  have hlearned : an.learned = [(uip.negate).norm] := by
    rw [hcanon, ConflictAnalysis.normalized_learned,
      ConflictAnalysis.ofUIP_learned, hbelow]
    simp
  rw [hlearned]
  exact learnedEntailed_singleton_run hqent huipshape

/-- **THE `hAnalysisEntail` FAMILY (I1-B)**: the exact premise shape the I1
assembly (`SupportedInstance.supportedHpre_unitKit_of_site` /
`SupportedUnitKit.hent`) consumes, as the constant wrapper over
`unitAnalysisEntailed_site`. No residual beyond the unit-kit equations
`hprops`/`hSupp`. -/
theorem hAnalysisEntail_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned] :=
  fun hreach hcontract hbr hconf hana =>
    unitAnalysisEntailed_site hprops hSupp hreach hcontract hbr hconf hana

/-! ## §4 Consumer-shape regressions (the I1-A interface, verbatim)

The `example`s below are the EXACT premise shapes the I1 assembly
consumes (`SupportedInstance.supportedHpre_unitKit_of_site`'s
`hAnalysisEntail` parameter and its call site
`fun hc' ha' => hAnalysisEntail hreach hcontract hbs hc' ha'`): they
witness that the exported family needs no further argument and is
accepted where the assembly expects it. -/

-- the family literal: accepted as the exact `hAnalysisEntail` parameter type
example {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    (∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned]) :=
  hAnalysisEntail_unitKit hprops hSupp

-- the assembly's call site: the family applied at site facts
example {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hreach : SupportedReach orig original props cfg)
    (hcontract : ClosureContract leaf orig original props)
    (hbs : ReachableState leaf orig cfg.branch)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    LearnedEntailed leaf [an.learned] :=
  (hAnalysisEntail_unitKit hprops hSupp) hreach hcontract hbs hconf hana

-- NON-VACUITY: the concrete Boolean singleton run of
-- `Proofs/SchedulerConflict.lean`'s N1 regressions, read through the
-- shape lemma — the analyzed UIP's normalized negation is exactly the
-- scanned clause literal, so the learned singleton transports the
-- conflict clause's entailment verbatim.
example : (analyzeAtAllowance
      [{ literal := posBool 0 true, level := 1, reason := none }] 1
      [posBool 0 false]).map (fun p => p.2.negate.norm)
    = some (posBool 0 false).norm := by
  rw [show analyzeAtAllowance
      [{ literal := posBool 0 true, level := 1, reason := none }] 1
      [posBool 0 false] = some ([], posBool 0 true) from rfl]
  rfl

end LeanFzn.Solver.UIP
