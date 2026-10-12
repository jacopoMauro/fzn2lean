/-
Purpose: Prove finite-domain propagation closure preserves solutions and learns only entailed clauses.
Dependencies: Pruning supplies executable closure; Proofs.PruningTypes supplies database composition.
DAG: Pruning + Proofs.PruningTypes -> certified pruning kit -> public LeanFzn.Solver certification.
-/
import LeanFzn.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.Proofs.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

private def EventSafe (leaf : Assignment → Bool) (f : BranchFrame) (e : PruningEvent) : Prop :=
  (∀ a, leaf a = true → FrameCovers f a →
    match e with
    | .stable => True
    | .conflict _ => False
    | .implied l _ _ _ => l.eval a = some true) ∧
  (match e with
    | .conflict cs => EntailedDB leaf cs
    | .implied _ c learnReason _ => learnReason = true → EntailedDB leaf [c]
    | _ => True)

private theorem scanDatabase_safe (leaf : Assignment → Bool) (original : List Clause)
    (f : BranchFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf f (scanDatabase original f db) := by
  induction db with
  | nil => exact ⟨by simp [scanDatabase], trivial⟩
  | cons c rest ih =>
    have hc : ∀ a, leaf a = true → c.SatisfiedBy a := fun a ha => hdb c (by simp) a ha
    have hr : EntailedDB leaf rest := fun q hq a ha => hdb q (by simp [hq]) a ha
    rw [scanDatabase]
    split
    · rename_i he
      exact ⟨fun a ha hf => clauseRemaining_empty_excludes hf he (hc a ha), by intro q hq; simp at hq⟩
    · rename_i l he
      split
      · exact ⟨fun a ha hf => clauseRemaining_singleton_implies hf (hc a ha) he,
          by simp⟩
      · exact ih hr
    · exact ih hr

private theorem scanPropagators_safe (leaf : Assignment → Bool) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (hview : frameViewedB f = true) :
    ∀ ps, (∀ p ∈ ps, p ∈ props) → EventSafe leaf f (scanPropagators f ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨by simp [scanPropagators], trivial⟩
  | cons p rest ih =>
    intro hm
    have hp := hm p (by simp)
    have hr : ∀ q ∈ rest, q ∈ props := fun q hq => hm q (by simp [hq])
    rw [scanPropagators]
    split
    · exact ih hr
    · rename_i c hrun
      refine ⟨fun a ha hf => hc.conflict f hview p hp c hrun a ha hf, ?_⟩
      dsimp only
      split
      · intro q hq; simp at hq
      · rename_i hne
        intro q hq a ha
        have hqc : q = c := by simpa using hq
        subst q
        exact hc.conflictReason f hview p hp c hrun (by intro he; simp [he] at hne) a ha
    · rename_i l r hrun
      split
      · refine ⟨fun a ha hf => hc.implied f hview p hp l r hrun a ha hf, ?_⟩
        intro _ c hmem a ha
        have he : c = r.clause := by simpa using hmem
        subst c
        exact hc.reason f hview p hp l r hrun a ha
      · exact ih hr

private theorem nextPruningEvent_safe (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PropagationContract leaf props)
    (f : BranchFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf f (nextPruningEvent original props f db) := by
  have hd := scanDatabase_safe leaf original f db hdb
  unfold nextPruningEvent
  split
  · split
    · rename_i hv
      exact scanPropagators_safe leaf props hc f hv props (fun _ h => h)
    · exact ⟨by simp, trivial⟩
  · -- a conflict is carried; its safety is the scan's
    rename_i cs heq
    rw [heq] at hd
    exact hd
  · -- an implied event is liveness-gated (P1 S1′)
    rename_i l c lr fl heq
    rw [heq] at hd
    split
    · exact hd
    · exact ⟨by simp, trivial⟩

private theorem fresh_entailed {leaf : Assignment → Bool} {c : Clause}
    {learnReason : Bool} {db : List Clause}
    (h : learnReason = true → EntailedDB leaf [c]) :
    EntailedDB leaf (if learnReason && !(db.contains c) then [c] else []) := by
  split
  · rename_i hf
    exact h (by simpa using (show learnReason = true ∧ !(db.contains c) = true from by simpa using hf).1)
  · intro q hq; simp at hq

theorem propagationClosure_cost_le (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) (g : BranchFrame)
    (h : (propagationClosure original props f db).frame = some g) :
    branchCost g.1 ≤ branchCost f.1 := by
  rw [propagationClosure] at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h
  · rename_i l c learnReason fromLearned he
    cases hfilter : filterFrame l f with
    | none => simp only [hfilter] at h; cases h
    | some refined =>
      by_cases hmass : Frame.mass refined < Frame.mass f
      · simp only [hfilter, dif_pos hmass] at h
        exact Nat.le_trans
          (propagationClosure_cost_le original props refined _ g h)
          (filterFrame_cost_le hfilter)
      · simp only [hfilter, dif_neg hmass] at h
        cases h; exact Nat.le_refl _
termination_by Frame.mass f

private theorem propagationClosure_correct (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (db : List Clause)
    (hdb : EntailedDB leaf db) :
    (∀ a, leaf a = true → FrameCovers f a →
      ∃ g, (propagationClosure original props f db).frame = some g ∧ FrameCovers g a) ∧
    EntailedDB leaf (propagationClosure original props f db).learned := by
  have he := nextPruningEvent_safe leaf original props hc f db hdb
  rw [propagationClosure]
  split
  · exact ⟨fun a _ hf => ⟨f, rfl, hf⟩, by intro c hc; simp at hc⟩
  · rename_i cs hev
    have hcs : EntailedDB leaf cs := by simpa only [hev] using he.2
    refine ⟨?_, ?_⟩
    · intro a ha hf
      have hx := he.1 a ha hf
      simp only [hev] at hx
    · intro c hcm a ha
      exact hcs c (List.mem_filter.mp hcm).1 a ha
  · rename_i l c learnReason fromLearned hev
    have hnew : EntailedDB leaf (if learnReason && !(db.contains c) then [c] else []) :=
      fresh_entailed (by simpa only [hev] using he.2)
    have himplied : ∀ a, leaf a = true → FrameCovers f a → l.eval a = some true := by
      simpa only [hev] using he.1
    cases hfilter : filterFrame l f with
    | none =>
      dsimp only
      refine ⟨?_, hnew⟩
      intro a ha hf
      obtain ⟨g, hg, _⟩ := filterFrame_preserves hf (himplied a ha hf)
      rw [hfilter] at hg
      cases hg
    | some refined =>
      by_cases hmass : Frame.mass refined < Frame.mass f
      · simp only [dif_pos hmass]
        have hrec := propagationClosure_correct leaf original props hc refined _ (hnew.append hdb)
        refine ⟨?_, hnew.append hrec.2⟩
        intro a ha hf
        obtain ⟨g, hg, hgf⟩ := filterFrame_preserves hf (himplied a ha hf)
        rw [hfilter] at hg
        cases hg
        exact hrec.1 a ha hgf
      · simp only [dif_neg hmass]
        exact ⟨fun a _ hf => ⟨f, rfl, hf⟩, hnew⟩
termination_by Frame.mass f

theorem propagationClosure_preserves (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (db : List Clause)
    (hdb : EntailedDB leaf db) (a : Assignment) (ha : leaf a = true) (hf : FrameCovers f a) :
    ∃ g, (propagationClosure original props f db).frame = some g ∧ FrameCovers g a :=
  (propagationClosure_correct leaf original props hc f db hdb).1 a ha hf

theorem propagationClosure_learns (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (db : List Clause)
    (hdb : EntailedDB leaf db) : EntailedDB leaf (propagationClosure original props f db).learned :=
  (propagationClosure_correct leaf original props hc f db hdb).2

/-- Certified finite-domain closure, usable directly by the public pruning driver. -/
def pruningKit (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PropagationContract leaf props) : PruningKit leaf where
  run := propagationClosure original props
  cost_le := propagationClosure_cost_le original props
  preserves := propagationClosure_preserves leaf original props hc
  learns := propagationClosure_learns leaf original props hc

end LeanFzn.Solver.Propagation
