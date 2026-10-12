/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerFalsified.lean

Purpose:
  Discharge — or precisely bound — the last arm-5 premise S4/S5 left:
  `RecordedAnalysisFalsified`, i.e. "every literal of the RECORDED
  analysis's learned clause is trail-falsified at the pre-jump branch",
  for a `SchedulerReachable` configuration with recorded evidence.

  R1's `reachable_analysis_success` exposes the recorded analysis as
  `an = ConflictAnalysis.ofUIP below uip` with
  `analyzeAtAllowance cfg.branch.trail cfg.branch.level ev.clause
     = some (below, uip)`.
  (`Proofs/SchedulerReachable.lean:406`.)

  FINDING (kernel-checked, §3 below): the EXACT `FalsifiedByTrail` shape
  (`BranchState.lean:130`: `∃ e ∈ trail, e.literal = q.negate`) is NOT
  derivable from a successful run. `BelowFalsified`
  (`AnalysisInvariants.lean:79`) records `e.literal = (p.1.negate).norm`;
  for an `intLe`/`intNe` literal `norm` is the identity, but a below pair
  whose literal is a POSITIVE Boolean literal `posBool s b` has
  `(posBool s b).negate` non-normal, while every trail entry stores the
  normal form (`AnalyzerTrailOk.norm`). The executable run of §3
  produces exactly such a pair, so the raw statement would be false —
  this is the same norm gap already documented for the asserting
  literal (`RestorationCertificate.boolUip_norm_gap`,
  `RestorationCertificate.lean:1016`), and the certificate interface
  already uses the norm shape for `learnedFalsified`
  (`RestorationCertificate.lean:177`).

  DELIVERED:
  * `FalsifiedByTrailNorm` — the norm-relaxed falsification shape;
  * `recordedAnalysis_normFalsified` — PROVED unconditionally from
    `SchedulerReachable cfg` + recorded evidence + branch reachability
    (this is the premise S4/S5 can drop after restating `hfals` in the
    norm shape);
  * `not_satisfiedBy_of_normFalsified` — the ready norm-aware twin of
    `SchedulerCoverage.not_satisfiedBy_of_falsifiedByTrail`, so the
    restatement is a one-line consumer edit, NOT a new residual;
  * `recordedAnalysisFalsified_of_belowStable` — the raw shape under the
    exact missing hypothesis (`∀ p ∈ below, (p.1.negate).norm
    = p.1.negate`), NAMED `BelowNegateStable`; §3 shows the hypothesis is
    not vacuous and exhibits the failed run (smallest witness).

Consumers:
  * S4 `jumpFrameAlternative_of_recorded_analysis` /
    `stepLearnBackjumpAssert_coverage_of_recorded_analysis`
    (`Proofs/SchedulerCoverage.lean:341,408`): replace
    `hfals : FalsifiedByTrail bs an.learned` by
    `FalsifiedByTrailNorm bs an.learned`; the `not_satisfiedBy` step
    uses this file's `not_satisfiedBy_of_normFalsified`; nothing else
    changes (the frame-algebra half is unchanged).
  * S5 arm 5 (`Proofs/SchedulerStep.lean:526`): same restatement.
  * The producer of the premise is `recordedAnalysis_normFalsified`
    below (owner of this file), with `hb`, `hreach`, `hcfg`, `hconf`,
    `hana` all already in scope at the S4/S5 call sites.

Dependencies:
  - LeanFzn.Solver.UIP.Proofs.SchedulerReachable (SchedulerReachable,
    reachable_analysis_success)
  - LeanFzn.Solver.Propagation.AnalysisCompletion (analyzeStep_invariants,
    analyzeStep_uip_on_trail, analyzerInvariant_init,
    analyzerTrailOk_of_reachable)

NO sorry, NO custom axioms.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
import LeanFzn.Solver.Propagation.AnalysisCompletion
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The norm-relaxed falsification shape

`FalsifiedByTrail` demands the exact negation of every clause literal on
the trail. Trail entries store normal forms, so the exact shape is only
demanded by clause databases built from cause literals (the propagation
layer constructs those as exact negations of normalized facts). The
analyzer's learned clause mixes the negated UIP (a cause literal) with
BELOW pairs in normalized form, for which only the normalized negation
is on the trail. This is the shape the repository's certificate
interface already uses (`RestorationCertificate.learnedFalsified`). -/

/-- Norm-relaxed trail falsification: every literal of `c` has the
NORMALIZED negation of itself as a trail entry. This is the strongest
shape a successful first-UIP run can deliver (see §3 for a
kernel-checked witness that the unnormalized shape fails). -/
def FalsifiedByTrailNorm {leaf : Assignment → Bool} (bs : BranchState leaf)
    (c : Clause) : Prop :=
  ∀ q ∈ c, ∃ e ∈ bs.trail, e.literal = (q.negate).norm

/-- The norm shape implies the exact shape whenever every clause literal
has a normal negation (the `BelowNegateStable` hypothesis of §2). For
`intLe`/`intNe` literals this holds unconditionally
(`norm` is the identity there); the gap is exclusively the positive
Boolean literals. -/
theorem falsifiedByTrail_of_norm {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause}
    (hstable : ∀ q ∈ c, (q.negate).norm = q.negate)
    (h : FalsifiedByTrailNorm bs c) : FalsifiedByTrail bs c := by
  intro q hq
  obtain ⟨e, he, hlit⟩ := h q hq
  exact ⟨e, he, (hstable q hq ▸ hlit)⟩

/-- The evaluation half S4's `not_satisfiedBy_of_falsifiedByTrail` needs,
in norm form: a norm-falsified clause is false at every assignment that
satisfies the trail. This is the exact replacement for the raw lemma
(`Proofs/SchedulerCoverage.lean:281`); the only extra step is
`Literal.norm_eval`, and it uses no new assumption. -/
theorem not_satisfiedBy_of_normFalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {a : Assignment}
    (hfals : FalsifiedByTrailNorm bs c)
    (htrail : ∀ e ∈ bs.trail, e.literal.eval a = some true) :
    ∀ q ∈ c, q.eval a = some false := by
  intro q hq
  obtain ⟨e, he, hlit⟩ := hfals q hq
  have hev := htrail e he
  rw [hlit, Literal.norm_eval] at hev
  exact (Literal.eval_negate_false_iff q a).mp hev

/-! ## §2 The recorded-analysis falsification, proved

The producer chain is exactly the one INTERFACES recorded for the
residual: R1's `reachable_analysis_success` exposes `(below, uip)`
together with `an = ConflictAnalysis.ofUIP below uip`;
`analyzeStep_invariants`/`analyzeStep_uip_on_trail` (B2's completion
invariants, at the initial invariant, which needs no premise) then give
`BelowFalsified bs.trail below` and the UIP's trail witness — whose
literal is normal because the branch state is reachable. -/

/-- **RECORDED ANALYSIS FALSIFIED (norm shape)**: for a reachable
configuration with recorded evidence `an`, every literal of `an.learned`
has its normalized negation on the branch trail. This is
`AnalysisContract.falsifiedAtConflict` up to the repository's own
normalization interface, derived with NO residual premise. -/
theorem recordedAnalysis_normFalsified {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hcfg : SchedulerReachable cfg)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    FalsifiedByTrailNorm bs an.learned := by
  obtain ⟨below, uip, hrun, heq⟩ :=
    reachable_analysis_success leaf cfg ev an hcfg hconf hana
  rw [hb] at hrun
  subst heq
  have hL : (ConflictAnalysis.ofUIP below uip).normalized.learned
      = (uip.negate :: below.map (fun p => p.1)).map Literal.norm := rfl
  have hbf : BelowFalsified bs.trail below := by
    unfold analyzeAtAllowance at hrun
    exact analyzeStep_invariants bs.trail bs.level
      (analysisFuel bs.trail ev.clause) [ev.clause] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip hrun
  obtain ⟨m, hm, hmlit, -⟩ :=
    analyzeStep_uip_on_trail bs.trail bs.level
      (analysisFuel bs.trail ev.clause) [ev.clause] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip hrun
  have hnorm : ∀ e ∈ bs.trail, e.literal = e.literal.norm :=
    (analyzerTrailOk_of_reachable hreach).norm
  have huipnorm : uip = uip.norm := by
    have h := hnorm m hm
    rw [hmlit] at h
    exact h
  intro q hq
  rw [hL] at hq
  rcases List.mem_map.mp hq with ⟨q₀, hq₀, rfl⟩
  rcases List.mem_cons.mp hq₀ with rfl | hq₀
  · exact ⟨m, hm, by
      simpa [norm_negate_norm_local, Literal.negate_negate]
        using hmlit.trans huipnorm⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq₀
    obtain ⟨e, hfe, helit, -⟩ := hbf p hp
    exact ⟨e, findEntryOf_mem _ _ _ hfe,
      by simpa [norm_negate_norm_local p.1] using helit⟩

/-- The EXACT `FalsifiedByTrail` shape under the single missing
hypothesis, NAMED: every recorded below literal has a normal negation.
`recordedAnalysis_normFalsified` supplies the rest, so this is the
premise S4/S5 would need to keep if they do not restate `hfals` — and
§3 shows it is not free. -/
def BelowNegateStable (below : List (Literal × Nat)) : Prop :=
  ∀ p ∈ below, (p.1.negate).norm = p.1.negate

theorem recordedAnalysisFalsified_of_belowStable {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c : Clause} {an : ConflictAnalysis}
    {below : List (Literal × Nat)} {uip : Literal}
    (hrun : analyzeAtAllowance bs.trail bs.level c = some (below, uip))
    (han : an = ConflictAnalysis.ofUIP below uip)
    (hstable : BelowNegateStable below) :
    FalsifiedByTrail bs an.learned := by
  subst han
  have hL : (ConflictAnalysis.ofUIP below uip).learned
      = uip.negate :: below.map (fun p => p.1) := rfl
  have hbf : BelowFalsified bs.trail below := by
    unfold analyzeAtAllowance at hrun
    exact analyzeStep_invariants bs.trail bs.level
      (analysisFuel bs.trail c) [c] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip hrun
  obtain ⟨m, hm, hmlit, -⟩ :=
    analyzeStep_uip_on_trail bs.trail bs.level
      (analysisFuel bs.trail c) [c] none [] []
      (analyzerInvariant_init bs.trail bs.level) below uip hrun
  intro q hq
  rw [hL] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨m, hm, by rw [Literal.negate_negate]; exact hmlit⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨e, hfe, helit, -⟩ := hbf p hp
    exact ⟨e, findEntryOf_mem _ _ _ hfe, (hstable p hp ▸ helit)⟩

/-! ## §3 The missing hypothesis is NOT vacuously true

A concrete executable allowance run whose recorded below-list contains
the positive Boolean literal `posBool 0 true`. The trail carries the
level-1 decision `posBool 0 false` and a level-2 decision
`posBool 1 false`; the conflict clause is the Boolean cause clause
`[¬(b₀ = false), ¬(b₁ = false)]` (cause literals are exact negations of
normalized facts). The analyzer records `(posBool 0 true, 1)` below and
returns the level-2 UIP `posBool 1 false`. Its exact negation
`(posBool 0 true).negate` is NOT on the trail — the trail stores
`posBool 0 false` — so the raw `FalsifiedByTrail` shape is refuted,
while `BelowFalsified` (norm shape) holds.

NOTE (honesty): reachability of this concrete configuration is not
claimed here; it is the generic Boolean-decision pattern (a Boolean
decision at a lower level, a later conflict mentioning its cause
literal), and S3/S5's inductive invariant would be the place to
instantiate it. What is kernel-checked below is that the analyzer's own
success output can carry a non-stable below pair — i.e. `BelowFalsified`
does not imply the raw shape — which is exactly the failed hypothesis. -/

/-- The witness trail: trail entries are normalized, as always. -/
def gapTrail : List TrailEntry :=
  [⟨posBool 0 false, 1, none⟩, ⟨posBool 1 false, 2, none⟩]

/-- The witness conflict clause: two Boolean cause literals. -/
def gapClause : Clause :=
  [⟨Atom.boolEq 0 false, false⟩, ⟨Atom.boolEq 1 false, false⟩]

/-- The executable run of the witness: a completed allowance run
(`rfl`, no `native_decide`). -/
theorem analyzeAtAllowance_gap_run :
    analyzeAtAllowance gapTrail 2 gapClause
      = some ([(posBool 0 true, 1)], posBool 1 false) := rfl

/-- `BelowFalsified` holds on the witness (norm tenor), so the missing
link is exclusively the normalization gap. -/
theorem gap_belowFalsified : BelowFalsified gapTrail [(posBool 0 true, 1)] := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact ⟨⟨posBool 0 false, 1, none⟩, rfl, rfl, rfl⟩

/-- `BelowNegateStable` FAILS on the witness recorded by the executable
run: `(posBool 0 true).negate` is not normal. -/
theorem gap_not_belowNegateStable :
    ¬ BelowNegateStable [(posBool 0 true, 1)] :=
  fun h => absurd (h (posBool 0 true, 1) (by simp)) (by decide)

/-- SMALLEST WITNESS (packaged): an executable success whose own
`ofUIP` record is not `FalsifiedByTrail` — the raw premise of
`jumpFrameAlternative_of_recorded_analysis` is not derivable in this
shape. -/
theorem gap_run_not_falsifiedByTrail :
    ¬ FalsifiedByTrail
        (⟨([], []), gapTrail, 2, []⟩ : BranchState (fun _ => true))
        (ConflictAnalysis.ofUIP [(posBool 0 true, 1)] (posBool 1 false)).learned := by
  intro h
  have hmem : posBool 0 true ∈
      (ConflictAnalysis.ofUIP [(posBool 0 true, 1)]
        (posBool 1 false)).learned := by
    simp [ConflictAnalysis.ofUIP]
  obtain ⟨e, he, hlit⟩ := h (posBool 0 true) hmem
  simp only [gapTrail, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact absurd hlit (by decide)
  · exact absurd hlit (by decide)

end LeanFzn.Solver.UIP
