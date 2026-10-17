/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerRunAssembly.lean

Purpose: discharge W1's terminal phase obligations (`W1.PhaseNextSatSolution` /
`W1.PhaseUnsatTerminal`, `Proofs/SchedulerRun.lean:211/223`) from S5's arm
lemmas and the branch-reachability assemblies, and record the exact residual.

CONTENT.

  §1 ROUTE ALGEBRA. `phaseNext`'s intercept arms never emit `.sat`
     (`backjumpStep_ne_sat`, `phaseNext_eq_sat_imp`): every reachable `.sat`
     outcome is `schedulerNext cfg = .sat w`, hence `stableStep cfg = .sat w`
     (`schedulerNext_eq_sat_imp`). Dually, `phaseNext cfg = .unsat` is either
     a dead one-or-two-step site with `stepConsume = none` (`phaseNext_unsat_cases`,
     carrying the site's `status = .dead` provenance lemmas
     `schedulerNext_localExclude_dead` / `backjumpStep_*_dead`), or the bare
     emission of `schedulerNext` (`schedulerNext_eq_unsat_cases`: exhausted
     consume route with `status = .dead`, or the level-0 conflict route).

  §2 SAT TERMINAL — CLOSED (fixed-`orig`). `phaseNext_sat_solution`:
     reachable `.sat w` with `cfg.orig = orig` yields
     `SolutionWitness leaf orig w` from S5's `arm_sat_solution` under the
     branch reachability supplied by `hbr_of_reachPreserve`
     (`Proofs/SchedulerArmsPreserve.lean` §4). No restoration input is needed
     for the SAT arm; `ReachableCpSnapshots`/`reachableCpSnapshots_of_step`
     are the jump-side chain and are NOT on this route.

  §3 UNSAT TERMINAL — CLOSED except the exhausted-frontier run premises. The
     exhausted-frontier sites are refuted from `SchedulerInvariant.coverage`
     + `ReachableDeadEvidence` (the site dead-region evidence, owner S4/P2 —
     the exact `hdead` premise of `arm_unsat_coverage`) + `learned_entailed`;
     `ReachableInvariantDiscipline` (owner C2d/S4) is the invariant-along-
     reachability interface. The level-0 conflict emission of `conflictStep`
     is CLOSED by `rootConflictExcludes_of_terminalEvent`: the actual
     `terminalResult = .conflict` event (exposed by
     `schedulerNext_eq_unsat_cases`) plus the concrete run premises — branch
     reachability `hbr` (B4), the level-0 trail-facts bridge `hbridge`
     (`RootFactsBridge`, producers `rootFactsBridge_init` /
     `rootFactsBridge_of_rootFacts` / `rootFactsBridge_of_explainedClosure` in
     `Proofs/CompiledScheduler.lean`; level-0 propagated trails are D0's
     residual), database entailment `hlent` (S4/D0) and the closure contract
     `hc` along the run (B2/D1). The former conflict-free `RootRouteExcludes`
     shape is DELETED from the active chain and kernel-refuted in
     `Proofs/RootRouteRegression.lean`.

  §4 W1 SHAPE FINDING. W1's `PhaseNextSatSolution`/`PhaseUnsatTerminal` are
     stated WITHOUT the terminal-site agreement `cfg.orig = orig`. Both
     fixed-`orig` wrappers need it (the witness fit is into `orig`; the
     coverage premise is into `cfg.orig`), and `orig` is a free parameter of
     `SchedulerReachable` (R1's `init` takes any box), so the `orig`-free
     shapes are NOT derivable from the arm lemmas. The exact W1 restatement
     (owner W1, additive) is to add the premise `cfg.orig = orig` to both
     defs and pass the induction's ambient `hcor` at the two `hterm_*` call
     sites in `SchedulerRun.lean` §3. `phaseNextSatSolution_of_origAgree` /
     `phaseNextUnsatTerminal_of_origAgree` show the `orig`-free shapes follow
     from the fixed-`orig` wrappers plus the site-agreement residual.

NO `sorry`, NO custom axiom. DAG: Proofs.SchedulerArmsComplete (via
SchedulerArmsPreserve -> Proofs.SchedulerReachClosure -> Proofs.SchedulerRun)
-> this module (leaf). Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly`.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerArmsComplete
import LeanFzn.Solver.UIP.Proofs.SchedulerConflict
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C2d
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b

namespace RunAssembly

/-! ## §1 Route algebra: where `phaseNext` can emit a verdict -/

/-- `backjumpStep` never reports `.sat`: its three landings are the
chronological fallback, the local exclusion and the completed jump. -/
theorem backjumpStep_ne_sat {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) (w : Assignment) :
    backjumpStep cfg ev ≠ .sat w := by
  intro hb
  have hcf := hb
  unfold backjumpStep at hcf
  cases ha : ev.analysis with
  | none =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcf
  | some an =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hcf
      | some cp =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              rw [hp] at hcf
              cases hcf
          | some restored =>
              rw [hp] at hcf
              cases hcf

/-- `backjumpStep` never reports `.unsat` either. -/
theorem backjumpStep_ne_unsat {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) :
    backjumpStep cfg ev ≠ .unsat := by
  intro hb
  have hcf := hb
  unfold backjumpStep at hcf
  cases ha : ev.analysis with
  | none =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcf
  | some an =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hcf
      | some cp =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              rw [hp] at hcf
              cases hcf
          | some restored =>
              rw [hp] at hcf
              cases hcf

/-- The backjump's chronological-fallback landing is dead. -/
theorem backjumpStep_fallback_dead {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {n : SchedulerConfig leaf}
    (h : backjumpStep cfg ev = .chronologicalFallback n) : n.status = .dead := by
  have hcf := h
  unfold backjumpStep at hcf
  cases ha : ev.analysis with
  | none =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcf
      simp
  | some an =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hcf
          simp
      | some cp =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              rw [hp] at hcf
              cases hcf
          | some restored =>
              rw [hp] at hcf
              cases hcf

/-- The backjump's local-exclusion landing is dead. -/
theorem backjumpStep_localExclude_dead {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {n : SchedulerConfig leaf}
    (h : backjumpStep cfg ev = .localExclude n) : n.status = .dead := by
  have hcf := h
  unfold backjumpStep at hcf
  cases ha : ev.analysis with
  | none =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcf
  | some an =>
      rw [ha] at hcf
      simp only [] at hcf
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hcf
      | some cp =>
          rw [hcp] at hcf
          simp only [] at hcf
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              rw [hp] at hcf
              simp only [] at hcf
              cases hcf
              simp
          | some restored =>
              rw [hp] at hcf
              cases hcf

/-- A `.localExclude` outcome of the real dispatcher is a dead site. -/
theorem schedulerNext_localExclude_dead {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {n : SchedulerConfig leaf}
    (h : schedulerNext cfg = .localExclude n) : n.status = .dead := by
  have hcf := h
  unfold schedulerNext at hcf
  cases hc : cfg.conflict with
  | some ev =>
      rw [hc] at hcf
      simp only [] at hcf
      exact backjumpStep_localExclude_dead hcf
  | none =>
      rw [hc] at hcf
      simp only [] at hcf
      cases hs : cfg.status with
      | dead =>
          rw [hs] at hcf
          simp only [] at hcf
          unfold consumeStep at hcf
          cases hsc : stepConsume cfg with
          | some next =>
              rw [hsc] at hcf
              simp only [] at hcf
              cases hcf
          | none =>
              rw [hsc] at hcf
              simp only [] at hcf
              cases hcf
      | active =>
          rw [hs] at hcf
          simp only [] at hcf
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              rw [hd] at hcf
              simp only [] at hcf
              cases hcf
          | none =>
              rw [hd] at hcf
              simp only [] at hcf
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable bs =>
                  rw [ht] at hcf
                  simp only [] at hcf
                  unfold stableStepGuarded at hcf
                  cases hw : leafWitness leaf cfg with
                  | some w' =>
                      rw [hw] at hcf
                      cases hcf
                  | none =>
                      rw [hw] at hcf
                      simp only [] at hcf
                      cases hsp : splitData cfg.branch.frame with
                      | some d =>
                          obtain ⟨l, v, vs, doms⟩ := d
                          rw [hsp] at hcf
                          simp only [] at hcf
                          by_cases hred : TrailRedundant cfg.branch.trail l = true
                          · rw [if_pos hred] at hcf
                            cases hcf
                          · rw [if_neg hred] at hcf
                            cases hcf
                      | none =>
                          rw [hsp] at hcf
                          simp only [] at hcf
                          cases hcf
                          simp
              | conflict bs cs learned =>
                  rw [ht] at hcf
                  simp only [] at hcf
                  unfold conflictStep at hcf
                  cases cs with
                  | nil =>
                      simp only [] at hcf
                      cases hcf
                      simp
                  | cons c rest =>
                      simp only [] at hcf
                      split at hcf
                      · cases hcf
                      · cases hcf
              | localExcluded bs lit reason learned =>
                  rw [ht] at hcf
                  simp only [] at hcf
                  cases hcf
                  simp

/-- A reachable `.sat` outcome of the phase dispatcher is the stable
dispatch's witness: every intercept arm of `phaseNext` returns a
non-`.sat` transition. -/
theorem phaseNext_eq_sat_imp {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (h : phaseNext cfg = .sat w) : schedulerNext cfg = .sat w := by
  cases hnext : schedulerNext cfg with
  | sat w' =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      exact h
  | unsat =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | propagate n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | decide n l =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | learnBackjumpAssert n p an =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | localExclude n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hsc : stepConsume n with
      | some next =>
          rw [hsc] at h
          cases h
      | none =>
          rw [hsc] at h
          cases h
  | chronologicalFallback n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hc : cfg.conflict with
      | none =>
          rw [hc] at h
          simp only [] at h
          cases h
      | some ev =>
          rw [hc] at h
          simp only [] at h
          cases hsc : stepConsume n with
          | some next =>
              rw [hsc] at h
              cases h
          | none =>
              rw [hsc] at h
              cases h
  | analyzeConflict n c =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hc : n.conflict with
      | none =>
          rw [hc] at h
          simp only [] at h
          cases h
      | some ev =>
          rw [hc] at h
          simp only [] at h
          cases hbj : backjumpStep n ev with
          | sat w' =>
              exact absurd hbj (backjumpStep_ne_sat n ev w')
          | unsat =>
              exact absurd hbj (backjumpStep_ne_unsat n ev)
          | propagate m =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | decide m l =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | analyzeConflict m c' =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | learnBackjumpAssert m p an =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | localExclude n' =>
              rw [hbj] at h
              simp only [] at h
              cases hsc : stepConsume n' with
              | some next =>
                  rw [hsc] at h
                  cases h
              | none =>
                  rw [hsc] at h
                  cases h
          | chronologicalFallback n' =>
              rw [hbj] at h
              simp only [] at h
              cases hsc : stepConsume n' with
              | some next =>
                  rw [hsc] at h
                  cases h
              | none =>
                  rw [hsc] at h
                  cases h

/-- A `.sat` outcome of `schedulerNext` is the stable dispatch's witness
(all other arms land on constructive or `.unsat` transitions). -/
theorem schedulerNext_eq_sat_imp {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (h : schedulerNext cfg = .sat w) : stableStepGuarded cfg = .sat w := by
  unfold schedulerNext at h
  cases hc : cfg.conflict with
  | some ev =>
      rw [hc] at h
      simp only [] at h
      exact absurd h (backjumpStep_ne_sat cfg ev w)
  | none =>
      rw [hc] at h
      simp only [] at h
      cases hs : cfg.status with
      | dead =>
          rw [hs] at h
          simp only [] at h
          unfold consumeStep at h
          cases hsc : stepConsume cfg with
          | some next =>
              rw [hsc] at h
              cases h
          | none =>
              rw [hsc] at h
              cases h
      | active =>
          rw [hs] at h
          simp only [] at h
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              rw [hd] at h
              simp only [] at h
              cases h
          | none =>
              rw [hd] at h
              simp only [] at h
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable bs =>
                  rw [ht] at h
                  simp only [] at h
                  exact h
              | conflict bs cs learned =>
                  rw [ht] at h
                  simp only [] at h
                  cases cs with
                  | nil =>
                      unfold conflictStep at h
                      simp only [] at h
                      cases h
                  | cons c rest =>
                      unfold conflictStep at h
                      simp only [] at h
                      split at h <;> cases h
              | localExcluded bs lit reason learned =>
                  rw [ht] at h
                  simp only [] at h
                  cases h

/-- `schedulerNext cfg = .unsat`: either the dead exhausted-frontier consume
route, or the level-0 conflict route WITH its actual terminal event (A1: the
emission is guarded by the real `terminalResult = .conflict` evidence, never
by a bare level-0/no-conflict shape — the latter is refuted by
`RootRouteRegression.not_rootRouteExcludesOld` on a satisfiable empty
initialization). -/
theorem schedulerNext_eq_unsat_cases {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (h : schedulerNext cfg = .unsat) :
    (cfg.pending = [] ∧ cfg.status = .dead) ∨
      (cfg.conflict = none ∧ cfg.status = .active ∧ cfg.branch.level = 0 ∧
        ∃ (bs : BranchState leaf) (cs learned : List Clause),
          cs ≠ [] ∧ terminalResult cfg.orig cfg.original cfg.props cfg.branch =
            .conflict bs cs learned) := by
  unfold schedulerNext at h
  cases hc : cfg.conflict with
  | some ev =>
      rw [hc] at h
      simp only [] at h
      exact absurd h (backjumpStep_ne_unsat cfg ev)
  | none =>
      rw [hc] at h
      simp only [] at h
      cases hs : cfg.status with
      | dead =>
          rw [hs] at h
          simp only [] at h
          unfold consumeStep at h
          left
          exact ⟨(consumeStep_unsat_iff cfg).mp h, rfl⟩
      | active =>
          rw [hs] at h
          simp only [] at h
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              rw [hd] at h
              simp only [] at h
              cases h
          | none =>
              rw [hd] at h
              simp only [] at h
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable bs =>
                  rw [ht] at h
                  simp only [] at h
                  unfold stableStepGuarded at h
                  cases hw : leafWitness leaf cfg with
                  | some w' =>
                      rw [hw] at h
                      cases h
                  | none =>
                      rw [hw] at h
                      simp only [] at h
                      cases hsp : splitData cfg.branch.frame with
                      | some d =>
                          obtain ⟨l, v, vs, doms⟩ := d
                          rw [hsp] at h
                          simp only [] at h
                          by_cases hred : TrailRedundant cfg.branch.trail l = true
                          · rw [if_pos hred] at h
                            cases h
                          · rw [if_neg hred] at h
                            cases h
                      | none =>
                          rw [hsp] at h
                          cases h
              | conflict bs cs learned =>
                  rw [ht] at h
                  simp only [] at h
                  right
                  refine ⟨rfl, rfl, (conflictStep_unsat_iff.mp h).2, bs, cs,
                    learned, ?_, rfl⟩
                  obtain ⟨c, rest, hcs⟩ := (conflictStep_unsat_iff.mp h).1
                  rw [hcs]
                  simp
              | localExcluded bs lit reason learned =>
                  rw [ht] at h
                  simp only [] at h
                  cases h

/-- The sites of a reachable `.unsat` emission of the phase dispatcher: a
dead one/two-step site (with `stepConsume = none`) or the bare emission. -/
theorem phaseNext_unsat_cases {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (h : phaseNext cfg = .unsat) :
    (schedulerNext cfg = .unsat) ∨
    (∃ n : SchedulerConfig leaf, n.orig = cfg.orig ∧ n.pending = [] ∧
      n.status = .dead ∧ (schedulerNext cfg).successor = some n) ∨
    (∃ n d : SchedulerConfig leaf, n.orig = cfg.orig ∧ d.orig = cfg.orig ∧
      d.pending = [] ∧ d.status = .dead ∧
        (schedulerNext cfg).successor = some n ∧
          (schedulerNext n).successor = some d) := by
  cases hnext : schedulerNext cfg with
  | sat w' =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | unsat => exact Or.inl rfl
  | propagate n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | decide n l =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | learnBackjumpAssert n p an =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases h
  | localExclude n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hsc : stepConsume n with
      | some next =>
          rw [hsc] at h
          cases h
      | none =>
          have hp : n.pending = [] := (stepConsume_eq_none_iff n).mp hsc
          have hnd : n.status = .dead := schedulerNext_localExclude_dead hnext
          have hs : (SchedulerTransition.localExclude n).successor = some n :=
            successor_localExclude n
          exact Or.inr (Or.inl ⟨n,
            W1.schedulerNext_succ_orig (by rw [hnext]; exact hs), hp, hnd, hs⟩)
  | chronologicalFallback n =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hc : cfg.conflict with
      | none =>
          rw [hc] at h
          simp only [] at h
          cases h
      | some ev =>
          rw [hc] at h
          simp only [] at h
          cases hsc : stepConsume n with
          | some next =>
              rw [hsc] at h
              cases h
          | none =>
              have hp : n.pending = [] := (stepConsume_eq_none_iff n).mp hsc
              have hbj : backjumpStep cfg ev = .chronologicalFallback n := by
                rw [schedulerNext_eq_backjumpStep_of_conflict_some hc] at hnext
                exact hnext
              have hnd : n.status = .dead := backjumpStep_fallback_dead hbj
              have hs : (SchedulerTransition.chronologicalFallback n).successor
                  = some n := successor_chronologicalFallback n
              exact Or.inr (Or.inl ⟨n,
                W1.schedulerNext_succ_orig (by rw [hnext]; exact hs), hp, hnd, hs⟩)
  | analyzeConflict n c =>
      unfold phaseNext at h
      rw [hnext] at h
      simp only [] at h
      cases hc : n.conflict with
      | none =>
          rw [hc] at h
          simp only [] at h
          cases h
      | some ev =>
          rw [hc] at h
          simp only [] at h
          cases hbj : backjumpStep n ev with
          | sat w' =>
              exact absurd hbj (backjumpStep_ne_sat n ev w')
          | unsat =>
              exact absurd hbj (backjumpStep_ne_unsat n ev)
          | propagate m =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | decide m l =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | analyzeConflict m c' =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | learnBackjumpAssert m p an =>
              rw [hbj] at h
              simp only [] at h
              cases h
          | localExclude n' =>
              rw [hbj] at h
              simp only [] at h
              have hn_orig : n.orig = cfg.orig :=
                W1.schedulerNext_succ_orig (by rw [hnext]; exact successor_analyzeConflict n c)
              have hn' : (SchedulerTransition.localExclude n').successor
                  = some n' := successor_localExclude n'
              cases hsc : stepConsume n' with
              | some next =>
                  rw [hsc] at h
                  cases h
              | none =>
                  have hnraw : (schedulerNext n).successor = some n' := by
                    rw [schedulerNext_eq_backjumpStep_of_conflict_some hc, hbj]
                    exact successor_localExclude n'
                  refine Or.inr (Or.inr ⟨n, n', hn_orig, ?_, ?_, ?_,
                    successor_analyzeConflict n c, hnraw⟩)
                  · exact (W1.schedulerNext_succ_orig hnraw).trans hn_orig
                  · exact (stepConsume_eq_none_iff n').mp hsc
                  · exact backjumpStep_localExclude_dead hbj
          | chronologicalFallback n' =>
              rw [hbj] at h
              simp only [] at h
              have hn_orig : n.orig = cfg.orig :=
                W1.schedulerNext_succ_orig (by rw [hnext]; exact successor_analyzeConflict n c)
              have hn' : (SchedulerTransition.chronologicalFallback n').successor
                  = some n' := successor_chronologicalFallback n'
              cases hsc : stepConsume n' with
              | some next =>
                  rw [hsc] at h
                  cases h
              | none =>
                  have hnraw : (schedulerNext n).successor = some n' := by
                    rw [schedulerNext_eq_backjumpStep_of_conflict_some hc, hbj]
                    exact successor_chronologicalFallback n'
                  refine Or.inr (Or.inr ⟨n, n', hn_orig, ?_, ?_, ?_,
                    successor_analyzeConflict n c, hnraw⟩)
                  · exact (W1.schedulerNext_succ_orig hnraw).trans hn_orig
                  · exact (stepConsume_eq_none_iff n').mp hsc
                  · exact backjumpStep_fallback_dead hbj

/-! ## §2 The SAT terminal wrapper — CLOSED -/

/-- **SAT TERMINAL (fixed `orig`)**: a reachable `.sat w` outcome of the
phase dispatcher is an original-box solution witness — S5's
`arm_sat_solution` under the branch reachability of `hbr_of_reachPreserve`. -/
theorem phaseNext_sat_solution {orig : List Domain} {leaf : Assignment → Bool}
    (hpres : ReachableArmsPreserveReach leaf)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : SchedulerReachable cfg) (horig : cfg.orig = orig)
    (hsat : phaseNext cfg = .sat w) : SolutionWitness leaf orig w := by
  have hst := schedulerNext_eq_sat_imp (phaseNext_eq_sat_imp hsat)
  have hstate : ReachableState leaf cfg.orig cfg.branch := by
    rw [horig]
    exact hbr_of_reachPreserve orig hpres hreach horig
  have hs : SolutionWitness leaf cfg.orig w :=
    arm_sat_solution hstate (stableStep_sat_of_guarded hst)
  rwa [horig] at hs

/-- Consumer form: the SAT wrapper from a fixed-`orig` branch-reachability
interface (e.g. D1's `CompiledPhasePremises.hbr`). -/
theorem phaseNext_sat_solution_of_hbr {orig : List Domain}
    {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → ReachableState leaf orig cfg.branch)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : SchedulerReachable cfg) (horig : cfg.orig = orig)
    (hsat : phaseNext cfg = .sat w) : SolutionWitness leaf orig w := by
  have hst := schedulerNext_eq_sat_imp (phaseNext_eq_sat_imp hsat)
  have hstate : ReachableState leaf cfg.orig cfg.branch := by
    rw [horig]
    exact hbr hreach horig
  have hs : SolutionWitness leaf cfg.orig w :=
    arm_sat_solution hstate (stableStep_sat_of_guarded hst)
  rwa [horig] at hs

/-! ## §3 The UNSAT terminal wrapper -/

/-- The reachable-invariant discipline at the phase terminal sites (owner
C2d/S4: the invariant-along-reachability assembly). -/
def ReachableInvariantDiscipline (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg → SchedulerInvariant cfg

/-- The dead-site evidence: a reachable dead configuration has no leaf
solution inside its frame (owner S4/P2: `arm_localExclude_log_sound`'s
`branchRegion_sound` discipline + `ExhaustionLog.Sound` maintenance; the
exact second premise of S5's `arm_unsat_coverage`). -/
def ReachableDeadEvidence (leaf : Assignment → Bool) : Prop :=
  ∀ {d : SchedulerConfig leaf}, SchedulerReachable d → d.status = .dead →
    ∀ a, leaf a = true → FrameCovers d.branch.frame a → False

/-- **THE LEVEL-0 FRAME BRIDGE**: on a reachable branch every original leaf
solution is covered by the current frame, provided every trail literal holds
at every leaf solution (`RootFactsBridge`). Prefix agreement is
`ReachableState.prefix_forced`; a remaining value the frame dropped has a
recorded trail falsifier (`ReachableState.narrowing_complete`) whose fact
would have to hold at the leaf, contradiction. Instantiates the existing
`frame_covers_of_trail` (`Proofs/BranchState.lean`). -/
theorem frameCovers_of_rootFacts {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hreach : ReachableState leaf orig bs)
    (hbridge : RootFactsBridge leaf bs) {a : Assignment}
    (ha : OriginalLeaves leaf orig a) :
    FrameCovers bs.frame a :=
  frame_covers_of_trail hreach.length_ok ha.2 hreach.prefix_forced
    hreach.narrowing_complete fun e he => hbridge a ha.1 e he

/-- The state carried by a `terminalResult` conflict IS the input branch
state (`terminalResult` returns `.conflict bs cs (filter …)` on its input
`bs`). Extracted from the equation so callers can transfer coverage stated
at the carried state to the configuration's own branch. -/
theorem terminalResult_conflict_state_eq {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {s : BranchState leaf} {cs learned : List Clause}
    (ht : terminalResult orig original props bs = .conflict s cs learned) :
    s = bs :=
  (terminalResult_conflict_cases ht).1

/-- **THE GUARDED ROOT-CONFLICT EXCLUSION (A1)**: a reachable branch whose
closure terminal event IS a conflict (`terminalResult … = .conflict bs cs
learned`, nonempty `cs` at the real emission — see
`schedulerNext_eq_unsat_cases`) excludes every original leaf solution, GIVEN
the actual evidence: the branch is reachable (`ReachableState`), the trail
facts hold at every leaf (`RootFactsBridge`, the level-0 propagated-trail
obligation), the learned database is entailed (`LearnedEntailed`) and the
closure contract supplies the terminal conflict's coverage
(`terminalResult_spec`). No global exclusion is assumed: the old
conflict-free `RootRouteExcludes` shape is kernel-refuted by
`RootRouteRegression.not_rootRouteExcludesOld`. -/
theorem rootConflictExcludes_of_terminalEvent {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs : List Clause} {learned : List Clause}
    (hreach : ReachableState leaf orig cfg.branch)
    (hbridge : RootFactsBridge leaf cfg.branch)
    (hlent : LearnedEntailed leaf cfg.branch.learned)
    (hc : ClosureContract leaf orig cfg.original cfg.props)
    (horig : cfg.orig = orig)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs cs learned) :
    ∀ a, OriginalLeaves leaf orig a → False := by
  have hspec := terminalResult_spec hc hreach
  rw [horig] at ht
  rw [ht] at hspec
  have hbs : bs = cfg.branch := terminalResult_conflict_state_eq ht
  subst hbs
  intro a ha
  exact hspec.coverage a ha.1
    ⟨frameCovers_of_rootFacts hreach hbridge ha,
     (fun e he => hbridge a ha.1 e he),
     (fun c hc' => hlent c hc' a ha.1)⟩

/-- **UNSAT TERMINAL (fixed `orig`)**: a reachable `.unsat` outcome excludes
every original-box leaf. The exhausted-frontier sites are refuted by
coverage + dead-site evidence + entailment; the level-0 conflict route is
closed by `rootConflictExcludes_of_terminalEvent` from the ACTUAL terminal
conflict event plus the concrete run premises `hbr` (branch reachability,
B4), `hbridge` (level-0 trail facts, D0), `hlent` (database entailment,
S4/D0) and `hc` (the closure contract along the run, B2/D1). No global
exclusion conclusion is assumed (A1). -/
theorem phaseNext_unsat_excludes {orig : List Domain} {leaf : Assignment → Bool}
    (hinv : ReachableInvariantDiscipline leaf)
    (hdead : ReachableDeadEvidence leaf)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → ReachableState leaf orig cfg.branch)
    (hbridge : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → RootFactsBridge leaf cfg.branch)
    (hlent : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      LearnedEntailed leaf cfg.branch.learned)
    (hc : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → ClosureContract leaf orig cfg.original cfg.props)
    {cfg : SchedulerConfig leaf} (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig) (hunsat : phaseNext cfg = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False := by
  have exhausted : ∀ {d : SchedulerConfig leaf}, SchedulerReachable d →
      d.pending = [] → d.status = .dead → d.orig = orig →
      ∀ a, OriginalLeaves leaf orig a → False := by
    intro d hd hp hstat hdo a ha
    have hda : OriginalLeaves leaf d.orig a := by rw [hdo]; exact ha
    rcases (hinv hd).coverage a hda with ⟨f, hf, hcov⟩ | ⟨c, hc, hnc⟩
    · unfold SchedulerConfig.frontier at hf
      rw [hp] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rw [hf] at hcov
      exact hdead hd hstat a ha.1 hcov
    · exact hnc ((hinv hd).learned_entailed c hc c
        (List.mem_singleton_self c) a ha.1)
  rcases phaseNext_unsat_cases hunsat with hbare |
    ⟨n, hn_orig, hn_pend, hn_dead, hn_succ⟩ |
    ⟨n, d, hn_orig, hd_orig, hd_pend, hd_dead, hn_succ, hd_succ⟩
  · rcases schedulerNext_eq_unsat_cases hbare with ⟨hp, hstat⟩ |
      ⟨hconf, hact, hlv, bs, cs, learned, hne, ht⟩
    · exact exhausted hreach hp hstat horig
    · exact rootConflictExcludes_of_terminalEvent (hbr hreach horig)
        (hbridge hreach horig) (hlent hreach) (hc hreach horig) horig ht
  · exact exhausted (schedulerReachable_successor hreach hn_succ) hn_pend
      hn_dead (hn_orig.trans horig)
  · exact exhausted (schedulerReachable_successor
      (schedulerReachable_successor hreach hn_succ) hd_succ) hd_pend hd_dead
      (hd_orig.trans horig)

/-! ## §4 The W1 fixed-input instantiations (A2)

With the fixed-input W1 shapes (`cfg.orig = orig →` in both defs), the
assembly's terminal wrappers deliver `PhaseNextSatSolution` /
`PhaseUnsatTerminal` DIRECTLY: the site-agreement residual the orig-free
shapes needed (`hagree`) is gone, so no obligation quantifies over runs on
other boxes. -/

/-- The SAT terminal shape at the real wrapper: branch reachability
(`ReachableArmsPreserveReach`, owner B4) plus the fixed-input site gives
W1's `PhaseNextSatSolution`. -/
theorem phaseNextSatSolution_of_reachPreserve {orig : List Domain}
    {leaf : Assignment → Bool}
    (hpres : ReachableArmsPreserveReach leaf) :
    W1.PhaseNextSatSolution orig leaf :=
  fun cfg w hreach horig hsat =>
    phaseNext_sat_solution hpres hreach horig hsat

/-- The UNSAT terminal shape at the real wrapper: the run premises
`hbr`/`hbridge`/`hlent`/`hc` (owners B4/D0/S4/B2-D1) plus the
dead-site/invariant disciplines give W1's `PhaseUnsatTerminal`. -/
theorem phaseNextUnsatTerminal_of_runPremises {orig : List Domain}
    {leaf : Assignment → Bool}
    (hinv : ReachableInvariantDiscipline leaf)
    (hdead : ReachableDeadEvidence leaf)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → ReachableState leaf orig cfg.branch)
    (hbridge : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → RootFactsBridge leaf cfg.branch)
    (hlent : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      LearnedEntailed leaf cfg.branch.learned)
    (hc : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = orig → ClosureContract leaf orig cfg.original cfg.props) :
    W1.PhaseUnsatTerminal orig leaf :=
  fun cfg hreach horig hunsat a ha =>
    phaseNext_unsat_excludes hinv hdead hbr hbridge hlent hc hreach
      horig hunsat a ha

end RunAssembly

end LeanFzn.Solver.UIP
