/-
Purpose: Prove finite-domain propagation closure preserves solutions and learns only entailed clauses.
Dependencies: Pruning supplies executable closure; Proofs.PruningTypes supplies database composition.
DAG: Pruning + Proofs.PruningTypes -> certified pruning kit -> public LeanFzn.Solver certification.
-/
import LeanFzn.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.Proofs.PruningTypes
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Semantics.ValueEquality
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

private theorem getD_append_lt {A B : List Domain} {i : Nat} (h : i < A.length) :
    (A ++ B).getD i [] = A.getD i [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_ge {A B : List Domain} {i : Nat} (h : A.length ≤ i) :
    (A ++ B).getD i [] = B.getD (i - A.length) [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-- A filtered frame is a pointwise sub-box of the frame it came from. -/
theorem filterFrame_domSub {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : DomSub (Frame.domains g) (Frame.domains f) := by
  have hpre := filterFrame_prefix h
  have hlen : g.1.length = f.1.length := by
    unfold filterFrame at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; exact filterSlots_length _ _ _
  have hsub := filterFrame_subsets h
  refine ⟨by simp [Frame.domains, hpre, hlen], ?_⟩
  intro i v hv
  unfold Frame.domains at hv ⊢
  rw [hpre] at hv
  have hl : (f.2.map (fun v => [v])).length = f.2.length := by simp
  by_cases hi : i < f.2.length
  · rw [getD_append_lt (by rw [hl]; exact hi)] at hv ⊢
    exact hv
  · have hi' : f.2.length ≤ i := Nat.le_of_not_lt hi
    rw [getD_append_ge (by rw [hl]; exact hi')] at hv ⊢
    rw [hl] at hv ⊢
    exact hsub _ v hv

/-- Faithfulness descends to sub-boxes. -/
theorem FrameFaithful.of_domSub {d' d : List Domain} {a : Assignment}
    (hf : FrameFaithful d a) (hs : DomSub d' d) : FrameFaithful d' a := by
  intro i hi
  obtain ⟨y, hy, hv, hsort⟩ := hf i (by rw [← hs.1]; exact hi)
  exact ⟨y, hy, hv, fun x hx => hsort x (hs.2 i x hx)⟩

private def EventSafe (leaf : Assignment → Bool) (props : List Propagator)
    (f : BranchFrame) (e : PruningEvent) : Prop :=
  (∀ a, leaf a = true → FrameCovers f a →
    match e with
    | .stable => True
    | .conflict _ => False
    | .implied l _ _ _ => l.eval a = some true) ∧
  ((props ≠ [] → ∀ a, leaf a = true → FrameFaithful (Frame.domains f) a) →
    match e with
    | .conflict cs => EntailedDB leaf cs
    | .implied _ c learnReason _ => learnReason = true → EntailedDB leaf [c]
    | _ => True)

private theorem scanDatabase_safe (leaf : Assignment → Bool) (props : List Propagator)
    (original : List Clause)
    (f : BranchFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf props f (scanDatabase original f db) := by
  induction db with
  | nil => exact ⟨by simp [scanDatabase], fun _ => trivial⟩
  | cons c rest ih =>
    have hc : ∀ a, leaf a = true → c.SatisfiedBy a := fun a ha => hdb c (by simp) a ha
    have hr : EntailedDB leaf rest := fun q hq a ha => hdb q (by simp [hq]) a ha
    rw [scanDatabase]
    split
    · rename_i he
      refine ⟨fun a ha hf => clauseRemaining_empty_excludes hf he (hc a ha), fun _ => ?_⟩
      intro q hq a ha
      rw [List.mem_singleton] at hq
      subst hq
      exact hc a ha
    · rename_i l he
      split
      · exact ⟨fun a ha hf => clauseRemaining_singleton_implies hf (hc a ha) he,
          fun _ => by simp⟩
      · exact ih hr
    · exact ih hr

private theorem scanPropagators_safe (leaf : Assignment → Bool) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (hview : frameViewedB f = true) :
    ∀ ps, (∀ p ∈ ps, p ∈ props) → EventSafe leaf props f (scanPropagators f ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨by simp [scanPropagators], fun _ => trivial⟩
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
      · intro _ q hq; simp at hq
      · rename_i hne
        intro hF q hq a ha
        have hqc : q = c := by simpa using hq
        subst q
        exact hc.conflictReason f hview p hp c hrun (by intro he; simp [he] at hne) a ha
          (hF (List.ne_nil_of_mem hp) a ha)
    · rename_i l r hrun
      split
      · refine ⟨fun a ha hf => hc.implied f hview p hp l r hrun a ha hf, ?_⟩
        intro _ _ c hmem a ha
        have he : c = r.clause := by simpa using hmem
        subst c
        exact hc.reason f hview p hp l r hrun a ha
      · exact ih hr

private theorem nextPruningEvent_safe (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PropagationContract leaf props)
    (f : BranchFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf props f (nextPruningEvent original props f db) := by
  have hd := scanDatabase_safe leaf props original f db hdb
  unfold nextPruningEvent
  split
  · split
    · rename_i hv
      exact scanPropagators_safe leaf props hc f hv props (fun _ h => h)
    · exact ⟨by simp, fun _ => trivial⟩
  · -- a conflict is carried; its safety is the scan's
    rename_i cs heq
    rw [heq] at hd
    exact hd
  · -- an implied event is liveness-gated (P1 S1′)
    rename_i l c lr fl heq
    rw [heq] at hd
    split
    · exact hd
    · exact ⟨by simp, fun _ => trivial⟩

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
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (Frame.domains f) a) :
    (∀ a, leaf a = true → FrameCovers f a →
      ∃ g, (propagationClosure original props f db).frame = some g ∧ FrameCovers g a) ∧
    EntailedDB leaf (propagationClosure original props f db).learned := by
  have he := nextPruningEvent_safe leaf original props hc f db hdb
  rw [propagationClosure]
  split
  · exact ⟨fun a _ hf => ⟨f, rfl, hf⟩, by intro c hc; simp at hc⟩
  · rename_i cs hev
    have hcs : EntailedDB leaf cs := by simpa only [hev] using he.2 hF
    refine ⟨?_, ?_⟩
    · intro a ha hf
      have hx := he.1 a ha hf
      simp only [hev] at hx
    · intro c hcm a ha
      exact hcs c (List.mem_filter.mp hcm).1 a ha
  · rename_i l c learnReason fromLearned hev
    have hnew : EntailedDB leaf (if learnReason && !(db.contains c) then [c] else []) :=
      fresh_entailed (by simpa only [hev] using he.2 hF)
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
          (fun hne a ha => (hF hne a ha).of_domSub (filterFrame_domSub hfilter))
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
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (Frame.domains f) a)
    (a : Assignment) (ha : leaf a = true) (hf : FrameCovers f a) :
    ∃ g, (propagationClosure original props f db).frame = some g ∧ FrameCovers g a :=
  (propagationClosure_correct leaf original props hc f db hdb hF).1 a ha hf

theorem propagationClosure_learns (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PropagationContract leaf props) (f : BranchFrame) (db : List Clause)
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (Frame.domains f) a) :
    EntailedDB leaf (propagationClosure original props f db).learned :=
  (propagationClosure_correct leaf original props hc f db hdb hF).2

/-- Frame-in-box test: the frame's full box has the box's slot count and every
value of every slot is a value of the same slot of `box`. Outside the box (never
reached from the root frame) the kit does not prune. -/
def frameInBoxB (box : List Domain) (f : BranchFrame) : Bool :=
  (Frame.domains f).length == box.length &&
    (Frame.domains f).zipIdx.all (fun p =>
      p.1.all (fun v => (box.getD p.2 []).any (fun w => w.eqB v)))

theorem frameInBoxB_domSub {box : List Domain} {f : BranchFrame}
    (h : frameInBoxB box f = true) : DomSub (Frame.domains f) box := by
  unfold frameInBoxB at h
  rw [Bool.and_eq_true] at h
  refine ⟨by simpa using h.1, ?_⟩
  intro i v hv
  have hlen : i < (Frame.domains f).length := by
    refine Classical.byContradiction fun hlt => ?_
    have : (Frame.domains f)[i]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, this] at hv
    simp at hv
  have hall := List.all_eq_true.mp h.2 ((Frame.domains f)[i], i)
    (by
      rw [List.mem_iff_getElem?]
      refine ⟨i, ?_⟩
      simp [List.getElem?_zipIdx, hlen])
  have hvmem : v ∈ (Frame.domains f)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at hv
    simpa using hv
  have h2 := List.any_eq_true.mp (List.all_eq_true.mp hall v hvmem)
  obtain ⟨w, hw, hwv⟩ := h2
  have : w = v := by
    -- eqB is raw equality
    exact (LeanFzn.Semantics.Evaluation.value_eqB_iff.mp hwv)
  rw [← this]
  exact hw

/-- Certified finite-domain closure, usable directly by the public pruning driver.
Frames inside the box `box` (every leaf solution is faithful to it) are saturated;
a frame outside the box is returned unpruned. -/
def pruningKit (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PropagationContract leaf props)
    (box : List Domain)
    (hbox : props ≠ [] → ∀ a, leaf a = true → FrameFaithful box a) :
    PruningKit leaf where
  run := fun f db =>
    if frameInBoxB box f then propagationClosure original props f db
    else { frame := some f }
  cost_le := by
    intro f db g h
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true] at h
      exact propagationClosure_cost_le original props f db g h
    · simp only [hb] at h
      cases h; exact Nat.le_refl _
  preserves := by
    intro f db hdb a ha hf
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true]
      exact propagationClosure_preserves leaf original props hc f db hdb
        (fun hne a ha => (hbox hne a ha).of_domSub (frameInBoxB_domSub hb)) a ha hf
    · simp only [hb]
      exact ⟨f, rfl, hf⟩
  learns := by
    intro f db hdb
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true]
      exact propagationClosure_learns leaf original props hc f db hdb
        (fun hne a ha => (hbox hne a ha).of_domSub (frameInBoxB_domSub hb))
    · simp only [hb]
      intro c hc; simp at hc

end LeanFzn.Solver.Propagation
