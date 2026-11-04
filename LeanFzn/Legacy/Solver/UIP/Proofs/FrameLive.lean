/-
File: LeanFzn/Solver/UIP/Proofs/FrameLive.lean

Purpose: the honest `FrameNonempty` producer for the M6 LCG route. The S1
`selectSlot` policy only splits LIVE slots (`vs ≠ []` after removing the
head), the pin child is the singleton `[v]`, the sparse `filterFrame` rejects
an empty result, and a resumed pending frame is exactly the nonempty retire
sibling. Hence every frame of a run started from a nonempty box is nonempty
at every reachable configuration — the S0 §3.5 gate the sorted rank decrease
consumes.

NO `sorry`, NO custom axiom.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b

namespace LeanFzn.Solver.UIP.FrameLive

variable {leaf : Assignment → Bool}

/-! ## Frame-list helpers -/

theorem nonempty_set {ds : List Domain} {k : Nat} {x : Domain}
    (h : ∀ d ∈ ds, Dom.enum d ≠ []) (hx : Dom.enum x ≠ []) :
    ∀ d ∈ ds.set k x, Dom.enum d ≠ [] := by
  intro d hd
  rcases List.mem_or_eq_of_mem_set hd with hd | rfl
  · exact h d hd
  · exact hx

theorem nonempty_pin {f : BranchFrame} (h : ∀ d ∈ f.doms, Dom.enum d ≠ [])
    (k : Nat) (v : Value) :
    ∀ d ∈ (f.pin k v).doms, Dom.enum d ≠ [] := by
  intro d hd
  rw [BranchFrame.pin_doms] at hd
  exact nonempty_set h (by simp) d hd

theorem nonempty_retire {f : BranchFrame} (h : ∀ d ∈ f.doms, Dom.enum d ≠ [])
    {k : Nat} {vs : Domain} (hvs : vs.enum ≠ []) :
    ∀ d ∈ (f.retire k vs).doms, Dom.enum d ≠ [] := by
  intro d hd
  rw [BranchFrame.retire_doms] at hd
  exact nonempty_set h hvs d hd

theorem filterFrame_nonempty {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) (h : ∀ d ∈ f.doms, Dom.enum d ≠ []) :
    ∀ d ∈ g.doms, Dom.enum d ≠ [] := by
  intro e he
  unfold filterFrame at hg
  split at hg
  · cases hg
    exact h e he
  · rename_i d0 hd0
    split at hg
    · cases hg
    · rename_i hfil
      cases hg
      rcases List.mem_or_eq_of_mem_set he with he | rfl
      · exact h e he
      · exact hfil

/-! ## Closure and perform frames -/

theorem explainedClosure_frame_nonempty (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) (h : ∀ d ∈ bs.frame.doms, Dom.enum d ≠ []) :
    ∀ d ∈ (explainedClosure orig original props bs).frame.doms,
      Dom.enum d ≠ [] := by
  suffices h' : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      (∀ d ∈ bs.frame.doms, Dom.enum d ≠ []) →
      ∀ d ∈ (explainedClosure orig original props bs).frame.doms,
        Dom.enum d ≠ [] from
    h' (Frame.mass bs.frame) bs (Nat.le_refl _) h
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hb
      rw [explainedClosure]
      split
      · exact hb
      · rename_i d hd
        exfalso
        have := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hb
      rw [explainedClosure]
      split
      · exact hb
      · rename_i d hd
        have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
          simp only [stepNarrowSync_frame]
          have := d.decreases
          omega
        have hnb : ∀ x ∈ (stepNarrowSync orig bs d).frame.doms,
            Dom.enum x ≠ [] := by
          rw [stepNarrowSync_frame]
          exact filterFrame_nonempty d.filtered hb
        exact ih _ hmass hnb

theorem perform_frame_nonempty {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hperf : p.perform bs orig original props = some s)
    (hcp : ∀ d ∈ p.checkpoint.frame.doms, Dom.enum d ≠ []) :
    ∀ d ∈ s.frame.doms, Dom.enum d ≠ [] := by
  obtain ⟨g, hg, rfl⟩ :=
    (perform_eq_some_iff (p := p) (bs := bs) (orig := orig)
      (original := original) (props := props)).mp hperf
  have hgne : ∀ d ∈ g.doms, Dom.enum d ≠ [] := filterFrame_nonempty hg hcp
  have hframe : (syncAll orig ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)).frame
      = g := by
    rw [syncAll_frame, BranchState.narrowFrame]
  exact explainedClosure_frame_nonempty orig original props _ (by
    rw [hframe]; exact hgne)

/-! ## The run invariant -/

/-- Pending frames are nonempty. -/
def PendingNonempty (cfg : SchedulerConfig leaf) : Prop :=
  ∀ f ∈ cfg.pending, ∀ d ∈ f.doms, Dom.enum d ≠ []

/-- Saved checkpoint frames are nonempty. -/
def CheckpointsNonempty (cfg : SchedulerConfig leaf) : Prop :=
  ∀ cp ∈ cfg.checkpoints, ∀ d ∈ cp.frame.doms, Dom.enum d ≠ []

/-- The three frame boxes a transition may read. -/
def LiveCfg (cfg : SchedulerConfig leaf) : Prop :=
  FrameNonempty cfg ∧ PendingNonempty cfg ∧ CheckpointsNonempty cfg

theorem liveCfg_init {orig : List Domain} {original : List Clause}
    {props : List Propagator} {prio : List Nat} {actBump : Bool}
    (hne : ∀ d ∈ orig, Dom.enum d ≠ []) :
    LiveCfg (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact hne d (by simpa [SchedulerConfig.init, BranchState.init] using hd)
  · intro f hf
    simp [SchedulerConfig.init, PendingNonempty] at hf
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    intro d hd
    exact hne d (by simpa [rootCheckpoint] using hd)

theorem schedulerNext_succ_live {cfg cfg' : SchedulerConfig leaf}
    (hl : LiveCfg cfg) (hs : (schedulerNext cfg).successor = some cfg') :
    LiveCfg cfg' := by
  obtain ⟨hlive, hpend, hck⟩ := hl
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hconf, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- recorded conflict
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hconf ha] at hs
        simp only [successor_chronologicalFallback, Option.some.injEq] at hs
        subst hs
        exact ⟨hlive, hpend, hck⟩
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hconf ha hcp] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            exact ⟨hlive, hpend, hck⟩
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hconf ha hcp hp] at hs
                simp only [successor_localExclude, Option.some.injEq] at hs
                subst hs
                exact ⟨hlive, hpend, hck⟩
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hconf ha hcp hp] at hs
                simp only [successor_learnBackjumpAssert, Option.some.injEq] at hs
                subst hs
                have hcpne : ∀ d ∈ cp.frame.doms, Dom.enum d ≠ [] :=
                  hck cp (checkpointAt_mem hcp)
                refine ⟨?_, ?_, ?_⟩
                · intro d hd
                  exact perform_frame_nonempty hp hcpne d
                    (by simpa [stepLearnBackjumpAssert] using hd)
                · intro f hf d hd
                  exact hpend f (by simpa [stepLearnBackjumpAssert] using hf) d hd
                · intro cp' hcp' d hd
                  rw [stepLearnBackjumpAssert_checkpoints] at hcp'
                  exact hck cp' (List.mem_filter.mp hcp').1 d
                    (by simpa using hd)
  · -- dead branch: consume
    cases hcons : stepConsume cfg with
    | none =>
        rw [C2d.schedulerNext_eq_consume_none hconf hdead hcons] at hs
        simp at hs
    | some next =>
        rw [C2d.schedulerNext_eq_consume_some hconf hdead hcons] at hs
        simp only [successor_chronologicalFallback, Option.some.injEq] at hs
        subst hs
        cases hpend0 : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend0] at hcons
            cases hcons
        | cons f rest =>
            have hfne : ∀ d ∈ f.doms, Dom.enum d ≠ [] :=
              hpend f (by rw [hpend0]; exact List.mem_cons_self ..)
            have hrest : ∀ g ∈ rest, ∀ d ∈ g.doms, Dom.enum d ≠ [] := by
              intro g hg d hd
              exact hpend g (by rw [hpend0]; exact List.mem_cons_of_mem _ hg) d hd
            unfold stepConsume at hcons
            rw [hpend0] at hcons
            simp only [Option.some.injEq] at hcons
            subst hcons
            refine ⟨?_, ?_, ?_⟩
            · intro d hd
              exact hfne d (by simpa [resumePending_frame] using hd)
            · intro g hg d hd
              exact hrest g (by simpa using hg) d hd
            · intro cp hcp
              simp at hcp
  · -- active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · rw [hnext] at hs
      simp only [successor_propagate, Option.some.injEq] at hs
      subst hs
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [stepPropagate_branch_frame] at hx
        exact filterFrame_nonempty d.filtered hlive x hx
      · intro f hf d hd
        exact hpend f (by simpa using hf) d hd
      · intro cp hcp d hd
        exact hck cp (by simpa [stepPropagate] using hcp) d hd
    · rw [hnext] at hs
      unfold stableStepGuarded at hs
      cases hw : leafWitness leaf cfg with
      | some w =>
          rw [hw] at hs
          simp at hs
      | none =>
          cases hsp : splitData cfg.branch.frame cfg.prio with
          | none =>
              simp only [hw, hsp, successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact ⟨hlive, hpend, hck⟩
          | some q =>
              obtain ⟨l, k, v, vs⟩ := q
              simp only [hw, hsp] at hs
              by_cases hred : TrailRedundant cfg.branch.trail l = true
              · simp only [if_pos hred, successor_decide, Option.some.injEq] at hs
                subst hs
                refine ⟨?_, ?_, ?_⟩
                · intro d hd
                  exact nonempty_pin hlive k v d
                    (by simpa [stepDecideSkip] using hd)
                · intro f hf
                  exact hpend f (by simpa [stepDecideSkip] using hf)
                · intro cp hcp
                  exact hck cp (by simpa [stepDecideSkip] using hcp)
              · simp only [if_neg hred, successor_decide, Option.some.injEq] at hs
                subst hs
                have hvs : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsp
                refine ⟨?_, ?_, ?_⟩
                · intro d hd
                  exact nonempty_pin hlive k v d (by simpa [stepDecide] using hd)
                · intro f hf d hd
                  rw [stepDecide_pending] at hf
                  rcases List.mem_cons.mp hf with rfl | hf
                  · exact nonempty_retire hlive hvs d hd
                  · exact hpend f hf d hd
                · intro cp hcp d hd
                  have hcp' : cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := by
                    simpa [stepDecide] using hcp
                  rcases List.mem_cons.mp hcp' with rfl | hcp''
                  · exact hlive d (by simpa [DecisionCheckpoint.ofBranch] using hd)
                  · exact hck cp hcp'' d hd
    · rw [hnext] at hs
      unfold conflictStep at hs
      cases cs with
      | nil =>
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact ⟨hlive, hpend, hck⟩
      | cons c rest =>
          dsimp only at hs
          by_cases hlev : cfg.branch.level = 0
          · rw [if_pos hlev] at hs
            simp at hs
          · rw [if_neg hlev] at hs
            simp only [successor_analyzeConflict, Option.some.injEq] at hs
            subst hs
            exact ⟨hlive, hpend, hck⟩
    · rw [hnext] at hs
      simp only [successor_localExclude, Option.some.injEq] at hs
      subst hs
      exact ⟨hlive, hpend, hck⟩

/-- **THE HONEST `FrameNonempty` PRODUCER**: every reachable frame of a run
started from a nonempty box has no empty domain. -/
theorem frameNonempty_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hne : ∀ d ∈ orig, Dom.enum d ≠ []) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      FrameNonempty cfg := by
  intro cfg hreach
  have hl : LiveCfg cfg := by
    induction hreach with
    | init hent => exact liveCfg_init hne
    | step h hs ih => exact schedulerNext_succ_live ih hs
  exact hl.1

/-- Nonempty-box transfer from a `gateOk`-passing problem. -/
theorem frameNonempty_of_gateOk {Constraint Objective : Type}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    (hgate : LeanFzn.Solver.Propagation.gateOk problem = true)
    (horig : problem.domains = orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      FrameNonempty cfg := by
  subst horig
  apply frameNonempty_of_supportedRun
  intro d hd hnil
  have hlen := LeanFzn.Solver.Propagation.gate_nonempty hgate d hd
  rw [Dom.length_eq_enum, hnil] at hlen
  simp at hlen

end LeanFzn.Solver.UIP.FrameLive
