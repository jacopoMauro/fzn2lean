/-
File: LeanFzn/Solver/UIP/Proofs/LcgLiveCoverage.lean
Purpose: global coverage of leaf solutions by the current branch and pending frontier.
Dependencies: LcgRunStep supplies semantic run states; LcgRunDrop supplies sound propagation,
redundant split and conflict deadness. Global coverage closes the exhausted-frontier UNSAT gap.
DAG: LcgRunStep -> LcgLiveCoverage -> LcgPhaseTerminal.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunStep

namespace LeanFzn.Solver.UIP.LcgLiveCoverage
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgRunDrop

/-- Every leaf solution belongs to the active or pending frontier. -/
def LiveCoverage {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop :=
  ∀ a, leaf a = true → FrameCovers cfg.branch.frame a ∨
    ∃ f ∈ cfg.pending, FrameCovers f a

variable {leaf : Assignment → Bool}

theorem stay {cfg cfg' : SchedulerConfig leaf} (h : LiveCoverage cfg)
    (hb : cfg'.branch.frame = cfg.branch.frame) (hp : cfg'.pending = cfg.pending) :
    LiveCoverage cfg' := by
  intro a ha
  rw [hb, hp]
  exact h a ha

theorem replace {cfg cfg' : SchedulerConfig leaf} (h : LiveCoverage cfg)
    (hp : cfg'.pending = cfg.pending)
    (hc : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers cfg'.branch.frame a) : LiveCoverage cfg' := by
  intro a ha
  rcases h a ha with h | ⟨f, hf, hfc⟩
  · exact Or.inl (hc a ha h)
  · exact Or.inr ⟨f, by rwa [hp], hfc⟩

theorem dead_replace {cfg cfg' : SchedulerConfig leaf} (h : LiveCoverage cfg)
    (hp : cfg'.pending = cfg.pending)
    (hd : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a) : LiveCoverage cfg' :=
  replace h hp (fun a ha hc => False.elim (hd a ha hc))

theorem decide {cfg : SchedulerConfig leaf} (h : LiveCoverage cfg)
    {k : Nat} {v : Value} {vs : Domain} {l : Literal}
    (hb : cfg.branch.frame.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    LiveCoverage (stepDecide cfg k v vs l) := by
  intro a ha
  rcases h a ha with hc | ⟨f, hf, hfc⟩
  · rcases (covers_split_at hb a).mp hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨_, List.mem_cons_self .., hc⟩
  · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hfc⟩

theorem consume {cfg next : SchedulerConfig leaf} (h : LiveCoverage cfg)
    {f : BranchFrame} {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (hd : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a)
    (hb : next.branch.frame = f) (hpn : next.pending = rest) : LiveCoverage next := by
  intro a ha
  rcases h a ha with hc | ⟨g, hg, hgc⟩
  · exact False.elim (hd a ha hc)
  · rw [hp] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Or.inl (hb ▸ hgc)
    · exact Or.inr ⟨g, by rwa [hpn], hgc⟩

/-- Every dispatcher successor preserves global live coverage on a semantic kit run. -/
theorem step {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) {cfg cfg' : SchedulerConfig leaf}
    (hr : SupportedReach orig original props cfg) (h : LcgRunState leaf orig cfg)
    (hl : LiveCoverage cfg) (hsucc : (schedulerNext cfg).successor = some cfg') :
    LiveCoverage cfg' := by
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hr
  subst hor hon hpr
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · have hdc := h.dead (Or.inr (by rw [hc]; exact Option.some_ne_none _))
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact stay hl rfl rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact stay hl rfl rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
                cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact stay hl rfl rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                exact dead_replace hl rfl hdc
  · rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none => simp only [consumeStep, hcons] at hsucc; cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil => rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons; cases hcons
        | cons f rest =>
            have hdc := h.dead (Or.inl hdead)
            unfold stepConsume at hcons
            rw [hp] at hcons
            simp only [Option.some.injEq] at hcons
            subst hcons
            exact consume hl hp hdc (by simp [resumePending_frame]) rfl
  · rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj, successor_propagate] at hsucc
      cases hsucc
      apply replace (cfg' := stepPropagate cfg d) hl rfl
      rw [stepPropagate_branch_frame]
      exact propagate_covers K h.good hd
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hw : leafWitness leaf cfg with
      | some w => simp only [hw, successor_sat] at hsucc; cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame cfg.prio with
          | none =>
              simp only [hw, hs, successor_localExclude] at hsucc
              cases hsucc
              exact stay hl rfl rfl
          | some p =>
              obtain ⟨l, k, v, vs⟩ := p
              simp only [hw, hs] at hsucc
              split at hsucc
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                exact replace hl rfl (skip_covers h.core.reach K.int K.fits hs hred)
              · rw [successor_decide] at hsucc
                cases hsucc
                exact decide hl (splitData_eq_some_iff.mp hs).2.1
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep, successor_localExclude] at hsucc
          cases hsucc
          exact stay hl rfl rfl
      | cons c rest =>
          by_cases hz : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hz, successor_unsat] at hsucc; cases hsucc
          · simp only [conflictStep, if_neg hz, successor_analyzeConflict] at hsucc
            cases hsucc
            exact stay hl rfl rfl
    · exact absurd ht terminalResult_ne_localExcluded

/-- Global coverage is initialized and preserved on all actual supported kit runs. -/
theorem of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LiveCoverage cfg := by
  intro cfg hr
  induction hr with
  | init hent =>
      intro a ha
      exact Or.inl (frameSndOrder_root K.fits a ha (by
        intro k hk
        exact absurd hk (by simp)))
  | step hr hs ih => exact step K hr (lcgRunState_of_supportedRun K hr) ih hs

/-- Exhaustion of a dead live frontier excludes every leaf solution. -/
theorem exhausted {cfg : SchedulerConfig leaf} (h : LiveCoverage cfg)
    (hd : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a)
    (hp : cfg.pending = []) : ∀ a, leaf a = true → False := by
  intro a ha
  rcases h a ha with hc | ⟨f, hf, _⟩
  · exact hd a ha hc
  · rw [hp] at hf; cases hf

end LeanFzn.Solver.UIP.LcgLiveCoverage
