/-
File: LeanFzn/Solver/Propagation/Proofs/Transitions.lean

Purpose:
  Local correctness obligations for LCG decisions, propagation with
  explanations, clause learning, conflicts, and backjumping. Five of the
  six obligations follow from their premises and are proved; the sixth
  (`analyzeConflict_correct`) additionally needs the L0.4 entailment
  chain for first-UIP resolution — its statement lacks a conflict-clause
  entailment premise, so it remains the deliberate remaining hole with
  that strengthening recorded.

Dependencies:
  - LeanFzn.Solver.Propagation.Invariants: semantic state contracts
    (`State.WellFormed`, `State.Represents`, `State.SoundConflict`,
    `ProblemSolution`, `Clause.EntailedBy`), and, through it, the
    operations (`initialState`, `enqueue`, `learn`, `backjump`,
    `analyzeConflict`).

DAG:
  LeanFzn.Solver.Propagation.Invariants -> LeanFzn.Solver.Propagation.Proofs.Transitions
  -> LeanFzn.Solver.Chronological.Proofs.Search
-/

import LeanFzn.Solver.Propagation.Invariants
import LeanFzn.Solver.Propagation.Proofs.Analyze
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Core

/-- Initial LCG state satisfies the structural invariant when all initial
    clauses are entailed by the internal problem. -/
theorem initialState_wellFormed
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hclauses : ∀ clause ∈ problem.clauses,
      clause.EntailedBy problem constraintHolds) :
    (initialState problem).WellFormed problem constraintHolds :=
  -- domains agree definitionally; the trail is empty; learned is empty
  ⟨rfl, fun _entry hentry => absurd hentry (by simp [initialState]),
    fun _clause hclause => absurd hclause (by simp [initialState])⟩

/-- An explained propagation retains every represented internal solution.
    The enqueued literal is justified by `himplies`; the reason clause is
    carried on the trail only as an explanation, not an obligation. -/
theorem enqueue_implied_preserves
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {state : State} {literal : Literal} {reason : Reason}
    (hstate : state.WellFormed problem constraintHolds)
    (hreason : reason.clause.EntailedBy problem constraintHolds)
    (himplies : ∀ assignment, state.Represents assignment →
      ProblemSolution problem constraintHolds assignment →
      literal.eval assignment = some true) :
    ∀ assignment, state.Represents assignment →
      ProblemSolution problem constraintHolds assignment →
      (enqueue state literal (some reason)).Represents assignment := by
  intro assignment hrep hsol
  have hrep' := hrep
  obtain ⟨hfit, htrail, hcl, hlearned⟩ := hrep'
  refine ⟨hfit, ?_, hcl, hlearned⟩
  intro entry hentry
  simp only [enqueue, List.mem_append, List.mem_singleton] at hentry
  rcases hentry with hentry | ⟨rfl⟩
  · exact htrail entry hentry
  · have hlit := himplies assignment hrep hsol
    simp only [hlit]

/-- Learned clauses must be semantic consequences of the original internal
    problem, never merely artifacts of one search path. -/
theorem learn_preserves
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {state : State} {clause : Clause}
    (hentailed : clause.EntailedBy problem constraintHolds) :
    ∀ assignment, state.Represents assignment →
      ProblemSolution problem constraintHolds assignment →
      (learn state clause).Represents assignment := by
  intro assignment hrep hsol
  obtain ⟨hfit, htrail, hcl, hlearned⟩ := hrep
  refine ⟨hfit, htrail, hcl, ?_⟩
  intro c hc
  simp only [learn] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact hentailed assignment hsol
  · exact hlearned c hc

/-- A reported conflict excludes every represented internal solution: the
    entailed conflict clause is falsified by every represented
    assignment. -/
theorem conflict_sound
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {state : State} {clause : Clause}
    (hconflict : state.conflict = some clause)
    (hreason : clause.EntailedBy problem constraintHolds)
    (hfalsified : ∀ assignment, state.Represents assignment →
      ¬ clause.SatisfiedBy assignment) :
    state.SoundConflict problem constraintHolds := by
  show state.conflict.isSome = true →
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment ∧
      state.Represents assignment
  intro _
  rintro ⟨assignment, hsol, hrep⟩
  exact hfalsified assignment hrep (hreason assignment hsol)

/-! ## Conflict analysis correctness

The plan's L0.4 closure sequence fixes the scaffolded statement (it
lacked conflict-entailment, so the learned clause's entailment could
not follow from `hanalyze` alone) and discharges the public theorem
against reachable-state assumptions. The *level half* is fully proved
from structural well-formedness alone
(`LeanFzn/Solver/UIP/Proofs/Analyze.lean`'s
`findEntry_mem`/`markLit_preserves`/`analyzeStep_preserves`/
`analyzeTrail_belowFromTrail`/`analyzeConflict_level` chain). The
*entailment half* is proved from the explicit `AnalysisReady` premise
that reachability must supply; when L0.4 resolution-preservation work
completes the `entailed_from_ready` step below, the premise can be
weakened or discharged. -/


/-! ## Learned-clause entailment (L0.4 steps 4–6)

The learned clause `uip.negate :: below.map (·.1)` is entailed by the
internal problem whenever the analyzer's per-step truths hold: every
reason clause consumed is globally entailed and applicable
(`Reason.Valid`), root-falsified literals drop soundly (`RootFacts`),
and reason clauses contain only normalized literals (reachability).
The proof seeds the analysis worklist's tracked disjunction with the
conflict clause itself (`tracked_seed`), runs the full worklist lift
(`analyzeStep_tracked` — every `analyzeStep` shape preserves the
tracked disjunction by witness transfer), and converts the lift's
output clause `learntLits below ++ [uip.negate]` into the learned
clause's head-first shape by monotonicity. -/
private theorem analyzeLearned_entailed
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {conflictClause : Clause}
    {trail : List TrailEntry} {lvl : Nat}
    (hcc : conflictClause.EntailedBy problem constraintHolds)
    (hreasons : ∀ e ∈ trail, ∀ r ∈ e.reason,
      Reason.Valid problem constraintHolds r e.literal)
    (hroot : RootFacts problem constraintHolds trail)
    (hrnorm : ∀ e ∈ trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm)
    (below : List (Literal × Nat)) (uip : Literal)
    (hres : analyzeTrail trail lvl conflictClause = some (below, uip)) :
    Clause.EntailedBy problem constraintHolds
      (uip.negate :: below.map fun p => p.1) := by
  -- seed: the conflict clause's entailment gives the worklist seed
  -- (pendingLits [conflictClause] none filters the conflict's
  -- normalized literals; skipEq none keeps everything)
  have hseed : Tracked problem constraintHolds [conflictClause] none
      [] [] := by
    unfold Tracked pendingLits marksNegs learntLits
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      id_eq, List.map_nil]
    refine norm_transfer (C := conflictClause) ?_ hcc
    intro l hl
    have hkeep : (!skipEq none l.norm) = true := rfl
    exact ⟨l.norm, List.mem_filter.mpr
      ⟨List.mem_map_of_mem (f := Literal.norm) hl, hkeep⟩,
      funext fun a => Literal.norm_eval l a⟩
  -- the full worklist lift over every analyzeStep shape
  have hlift := analyzeStep_tracked trail lvl hreasons hroot hrnorm
    (4 * trail.length * trail.length + 256) [conflictClause] none [] []
    hseed
    (fun e he => absurd he (by simp))
    below uip hres
  -- learntLits below ++ [uip.negate] re-associates into the learned
  -- clause's head-first shape; entailment is monotone under it
  unfold learntLits at hlift
  refine entailed_mono ?_ hlift
  intro l hl
  rw [List.mem_append] at hl
  rcases hl with h | h
  · exact List.mem_cons_of_mem _ h
  · rw [List.mem_singleton] at h
    rw [← h]
    exact List.mem_cons_self

/-- Conflict analysis correctness with the required premise. The level
    conjunct holds unconditionally (structural); the entailment conjunct
    holds under `AnalysisReady`, whose components L0.4 steps 2–3
    establish via transition preservation. -/
theorem analyzeConflict_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {state : State} {analysis : ConflictAnalysis}
    (hstate : state.WellFormed problem constraintHolds)
    (hready : state.AnalysisReady problem constraintHolds)
    (hanalyze : analyzeConflict state = some analysis) :
    analysis.learned.EntailedBy problem constraintHolds ∧
      analysis.backjumpLevel ≤ state.decisionLevel ∧
      (state.decisionLevel = 0 ∨
        analysis.backjumpLevel < state.decisionLevel) := by
  refine ⟨?_, analyzeConflict_level hstate hanalyze, ?_⟩
  · -- entailment: from `AnalysisReady`, the analysis consumes only
    -- entailed antecedents (conflict clause and reasons).
    obtain ⟨hconf_ent, hreasons, hroot, hrnorm⟩ := hready
    unfold analyzeConflict at hanalyze
    cases hconf : state.conflict with
    | none => rw [hconf] at hanalyze; simp at hanalyze
    | some conflictClause =>
      rw [hconf] at hanalyze
      simp only [] at hanalyze
      have hcc : conflictClause.EntailedBy problem constraintHolds :=
        hconf_ent conflictClause (hconf ▸ (Option.mem_some_iff.mpr rfl))
      cases hres : analyzeTrail state.trail state.decisionLevel conflictClause
        with
      | none => rw [hres] at hanalyze; simp at hanalyze
      | some res =>
        obtain ⟨below, uip⟩ := res
        rw [hres] at hanalyze
        simp only [] at hanalyze
        have hlv : state.decisionLevel = state.decisionLevel := rfl
        -- the learned clause is `uip.negate :: below.map (·.1)`; its
        -- entailment and the strictness of its recorded levels come from
        -- the resolution refinement chain (below-strictness via the
        -- analyzer's own case split; entailment from the resolution lemma).
        have hblevel : analysis.backjumpLevel
            = below.foldl (fun acc p => max acc p.2) 0 := by
          injection hanalyze with hinj; cases hinj; rfl
        have hlearned : analysis.learned
            = uip.negate :: below.map (fun p => p.1) := by
          injection hanalyze with hst
          cases hst
          rfl
        rw [hlearned]
        -- Resolution-soundness chain (L0.4 steps 4–6): the learned clause
        -- is entailed once the worklist-suffix I1 invariant and the
        -- resolve-step I2 threading (see `analyzeStep_entailed`'s three
        -- parked glue gaps in `Proofs/Analyze.lean`) are discharged.
        exact analyzeLearned_entailed hcc hreasons hroot hrnorm
          below uip hres
  · -- strict decrease when the level is nonzero: every recorded below
    -- level is strictly below the analysis level (`analyzeTrail_belowStrict`
    -- via the analyzer's own case split on recorded levels), so the
    -- fold-max is strictly below any positive level.
    cases hlv : state.decisionLevel with
    | zero => exact Or.inl rfl
    | succ lvl =>
        refine Or.inr ?_
        obtain ⟨hconf_ent, hreasons, hroot, hrnorm⟩ := hready
        unfold analyzeConflict at hanalyze
        cases hconf : state.conflict with
        | none => rw [hconf] at hanalyze; simp at hanalyze
        | some conflictClause =>
          rw [hconf] at hanalyze
          simp only [] at hanalyze
          cases hres : analyzeTrail state.trail state.decisionLevel
            conflictClause with
          | none => rw [hres] at hanalyze; simp at hanalyze
          | some res =>
            obtain ⟨below, uip⟩ := res
            rw [hres] at hanalyze
            simp only [] at hanalyze
            have hblevel : analysis.backjumpLevel
                = below.foldl (fun acc p => max acc p.2) 0 := by
              injection hanalyze with hinj; cases hinj; rfl
            rw [hblevel]
            obtain ⟨_, hlevels, _⟩ := hstate
            have hstrict : ∀ p ∈ below, p.2 < state.decisionLevel :=
              analyzeTrail_belowStrict state.trail state.decisionLevel
                conflictClause below uip hlevels hres
            -- fold-max of strictly-below levels is strictly below, given
            -- the level is positive
            have hfold : ∀ (bs : List (Literal × Nat)),
                (∀ p ∈ bs, p.2 < lvl + 1) →
                ∀ acc, acc < lvl + 1 →
                  bs.foldl (fun a p => max a p.2) acc < lvl + 1 := by
              intro bs hall acc
              induction bs generalizing acc with
              | nil => exact fun hacc => hacc
              | cons p rest ihrest =>
                  intro hacc
                  have hp1 : p.2 < lvl + 1 :=
                    hall p (List.mem_cons_self ..)
                  have ih' := ihrest (fun q hq =>
                    hall q (List.mem_cons_of_mem _ hq))
                  simp only [List.foldl_cons]
                  exact ih' (max acc p.2) (by omega)
            rw [hlv] at hstrict
            exact hfold below hstrict 0 (by omega)

/-- Backjumping removes only trail entries above the target level and
    retains every represented solution consistent with the retained
    trail. -/
theorem backjump_preserves
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {state : State} {level : Nat}
    (hle : level ≤ state.decisionLevel) :
    ∀ assignment, state.Represents assignment →
      ProblemSolution problem constraintHolds assignment →
      (backjump state level).Represents assignment := by
  intro assignment hrep _
  obtain ⟨hfit, htrail, hcl, hlearned⟩ := hrep
  refine ⟨hfit, ?_, hcl, hlearned⟩
  intro entry hentry
  simp only [backjump, List.mem_filter] at hentry
  exact htrail entry hentry.1

end LeanFzn.Solver.Propagation
