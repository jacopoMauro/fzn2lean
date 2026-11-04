/-
Purpose: Prove finite-domain propagation closure preserves solutions and learns only entailed clauses.
Dependencies: Pruning supplies executable closure; Proofs.PruningTypes supplies database composition.
DAG: Pruning + Proofs.PruningTypes -> certified pruning kit -> public LeanFzn.Solver certification.
-/
import LeanFzn.Legacy.Solver.Propagation.Pruning
import LeanFzn.Legacy.Solver.Propagation.Proofs.PruningTypes
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Semantics.ValueEquality
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

private theorem getD_append_lt {A B : List Domain} {i : Nat} (h : i < A.length) :
    (A ++ B).getD i Dom.empty = A.getD i Dom.empty := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem getD_append_ge {A B : List Domain} {i : Nat} (h : A.length ≤ i) :
    (A ++ B).getD i Dom.empty = B.getD (i - A.length) Dom.empty := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-- A filtered frame is a pointwise sub-box of the frame it came from. -/
theorem prefixFilterFrame_domSub {l : Literal} {f g : PrefixFrame}
    (h : prefixFilterFrame l f = some g) : DomSub (PrefixFrame.domains g) (PrefixFrame.domains f) := by
  have hpre := prefixFilterFrame_prefix h
  have hlen : g.1.length = f.1.length := by
    unfold prefixFilterFrame at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; exact filterSlots_length _ _ _
  have hsub := prefixFilterFrame_subsets h
  refine ⟨by simp [PrefixFrame.domains, hpre, hlen], ?_⟩
  intro i v hv
  unfold PrefixFrame.domains at hv ⊢
  rw [hpre] at hv
  have hl : (f.2.map (fun v => Dom.ofList [v])).length = f.2.length := by simp
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
    (f : PrefixFrame) (e : PruningEvent) : Prop :=
  (∀ a, leaf a = true → PrefixCovers f a →
    match e with
    | .stable => True
    | .conflict _ => False
    | .implied l _ _ _ => l.eval a = some true) ∧
  ((props ≠ [] → ∀ a, leaf a = true → FrameFaithful (PrefixFrame.domains f) a) →
    match e with
    | .conflict cs => EntailedDB leaf cs
    | .implied _ c learnReason _ => learnReason = true → EntailedDB leaf [c]
    | _ => True)

private theorem prefixScanDatabase_safe (leaf : Assignment → Bool) (props : List Propagator)
    (original : List Clause)
    (f : PrefixFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf props f (prefixScanDatabase original f db) := by
  induction db with
  | nil => exact ⟨by simp [prefixScanDatabase], fun _ => trivial⟩
  | cons c rest ih =>
    have hc : ∀ a, leaf a = true → c.SatisfiedBy a := fun a ha => hdb c (by simp) a ha
    have hr : EntailedDB leaf rest := fun q hq a ha => hdb q (by simp [hq]) a ha
    rw [prefixScanDatabase]
    split
    · rename_i he
      refine ⟨fun a ha hf => prefixClauseRemaining_empty_excludes hf he (hc a ha), fun _ => ?_⟩
      intro q hq a ha
      rw [List.mem_singleton] at hq
      subst hq
      exact hc a ha
    · rename_i l he
      split
      · exact ⟨fun a ha hf => prefixClauseRemaining_singleton_implies hf (hc a ha) he,
          fun _ => by simp⟩
      · exact ih hr
    · exact ih hr

private theorem prefixScanPropagators_safe (leaf : Assignment → Bool) (props : List Propagator)
    (hc : PrefixPropagationContract leaf props) (f : PrefixFrame) (hview : prefixFrameViewedB f = true) :
    ∀ ps, (∀ p ∈ ps, p ∈ props) → EventSafe leaf props f (prefixScanPropagators f ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact ⟨by simp [prefixScanPropagators], fun _ => trivial⟩
  | cons p rest ih =>
    intro hm
    have hp := hm p (by simp)
    have hr : ∀ q ∈ rest, q ∈ props := fun q hq => hm q (by simp [hq])
    rw [prefixScanPropagators]
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

private theorem prefixNextPruningEvent_safe (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PrefixPropagationContract leaf props)
    (f : PrefixFrame) (db : List Clause) (hdb : EntailedDB leaf db) :
    EventSafe leaf props f (prefixNextPruningEvent original props f db) := by
  have hd := prefixScanDatabase_safe leaf props original f db hdb
  unfold prefixNextPruningEvent
  split
  · split
    · rename_i hv
      exact prefixScanPropagators_safe leaf props hc f hv props (fun _ h => h)
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

theorem prefixPropagationClosure_cost_le (original : List Clause) (props : List Propagator)
    (f : PrefixFrame) (db : List Clause) (g : PrefixFrame)
    (h : (prefixPropagationClosure original props f db).frame = some g) :
    branchCost g.1 ≤ branchCost f.1 := by
  rw [prefixPropagationClosure] at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h
  · rename_i l c learnReason fromLearned he
    cases hfilter : prefixFilterFrame l f with
    | none => simp only [hfilter] at h; cases h
    | some refined =>
      by_cases hmass : PrefixFrame.mass refined < PrefixFrame.mass f
      · simp only [hfilter, dif_pos hmass] at h
        exact Nat.le_trans
          (prefixPropagationClosure_cost_le original props refined _ g h)
          (prefixFilterFrame_cost_le hfilter)
      · simp only [hfilter, dif_neg hmass] at h
        cases h; exact Nat.le_refl _
termination_by PrefixFrame.mass f

private theorem prefixPropagationClosure_correct (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PrefixPropagationContract leaf props) (f : PrefixFrame) (db : List Clause)
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (PrefixFrame.domains f) a) :
    (∀ a, leaf a = true → PrefixCovers f a →
      ∃ g, (prefixPropagationClosure original props f db).frame = some g ∧ PrefixCovers g a) ∧
    EntailedDB leaf (prefixPropagationClosure original props f db).learned := by
  have he := prefixNextPruningEvent_safe leaf original props hc f db hdb
  rw [prefixPropagationClosure]
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
    have himplied : ∀ a, leaf a = true → PrefixCovers f a → l.eval a = some true := by
      simpa only [hev] using he.1
    cases hfilter : prefixFilterFrame l f with
    | none =>
      dsimp only
      refine ⟨?_, hnew⟩
      intro a ha hf
      obtain ⟨g, hg, _⟩ := prefixFilterFrame_preserves hf (himplied a ha hf)
      rw [hfilter] at hg
      cases hg
    | some refined =>
      by_cases hmass : PrefixFrame.mass refined < PrefixFrame.mass f
      · simp only [dif_pos hmass]
        have hrec := prefixPropagationClosure_correct leaf original props hc refined _ (hnew.append hdb)
          (fun hne a ha => (hF hne a ha).of_domSub (prefixFilterFrame_domSub hfilter))
        refine ⟨?_, hnew.append hrec.2⟩
        intro a ha hf
        obtain ⟨g, hg, hgf⟩ := prefixFilterFrame_preserves hf (himplied a ha hf)
        rw [hfilter] at hg
        cases hg
        exact hrec.1 a ha hgf
      · simp only [dif_neg hmass]
        exact ⟨fun a _ hf => ⟨f, rfl, hf⟩, hnew⟩
termination_by PrefixFrame.mass f

theorem prefixPropagationClosure_preserves (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PrefixPropagationContract leaf props) (f : PrefixFrame) (db : List Clause)
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (PrefixFrame.domains f) a)
    (a : Assignment) (ha : leaf a = true) (hf : PrefixCovers f a) :
    ∃ g, (prefixPropagationClosure original props f db).frame = some g ∧ PrefixCovers g a :=
  (prefixPropagationClosure_correct leaf original props hc f db hdb hF).1 a ha hf

theorem prefixPropagationClosure_learns (leaf : Assignment → Bool)
    (original : List Clause) (props : List Propagator)
    (hc : PrefixPropagationContract leaf props) (f : PrefixFrame) (db : List Clause)
    (hdb : EntailedDB leaf db)
    (hF : props ≠ [] → ∀ a, leaf a = true → FrameFaithful (PrefixFrame.domains f) a) :
    EntailedDB leaf (prefixPropagationClosure original props f db).learned :=
  (prefixPropagationClosure_correct leaf original props hc f db hdb hF).2

/-- Frame-in-box test: the frame's full box has the box's slot count and every
value of every slot is a value of the same slot of `box`. Outside the box (never
reached from the root frame) the kit does not prune. -/
def frameInBoxB (box : List Domain) (f : PrefixFrame) : Bool :=
  (PrefixFrame.domains f).length == box.length &&
    (PrefixFrame.domains f).zipIdx.all (fun p =>
      (Dom.enum p.1).all (fun v => (Dom.enum (box.getD p.2 Dom.empty)).any (fun w => w.eqB v)))

theorem frameInBoxB_domSub {box : List Domain} {f : PrefixFrame}
    (h : frameInBoxB box f = true) : DomSub (PrefixFrame.domains f) box := by
  unfold frameInBoxB at h
  rw [Bool.and_eq_true] at h
  refine ⟨by simpa using h.1, ?_⟩
  intro i v hv
  have hlen : i < (PrefixFrame.domains f).length := by
    refine Classical.byContradiction fun hlt => ?_
    have : (PrefixFrame.domains f)[i]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, this] at hv
    simp at hv
  have hall := List.all_eq_true.mp h.2 ((PrefixFrame.domains f)[i], i)
    (by
      rw [List.mem_iff_getElem?]
      refine ⟨i, ?_⟩
      simp [List.getElem?_zipIdx, hlen])
  have hvmem : v ∈ Dom.enum ((PrefixFrame.domains f)[i]) := by
    rw [← domElems_eq_enum, ← DomainLike.mem_iff]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at hv
    simpa using hv
  have h2 := List.any_eq_true.mp (List.all_eq_true.mp hall v hvmem)
  obtain ⟨w, hw, hwv⟩ := h2
  have : w = v := by
    -- eqB is raw equality
    exact (LeanFzn.Semantics.Evaluation.value_eqB_iff.mp hwv)
  rw [← this]
  rw [← domElems_eq_enum, ← DomainLike.mem_iff] at hw
  exact hw

/-- Certified finite-domain closure, usable directly by the public pruning driver.
Frames inside the box `box` (every leaf solution is faithful to it) are saturated;
a frame outside the box is returned unpruned. -/
def pruningKit (leaf : Assignment → Bool) (original : List Clause)
    (props : List Propagator) (hc : PrefixPropagationContract leaf props)
    (box : List Domain)
    (hbox : props ≠ [] → ∀ a, leaf a = true → FrameFaithful box a) :
    PruningKit leaf where
  run := fun f db =>
    if frameInBoxB box f then prefixPropagationClosure original props f db
    else { frame := some f }
  cost_le := by
    intro f db g h
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true] at h
      exact prefixPropagationClosure_cost_le original props f db g h
    · simp only [hb] at h
      cases h; exact Nat.le_refl _
  preserves := by
    intro f db hdb a ha hf
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true]
      exact prefixPropagationClosure_preserves leaf original props hc f db hdb
        (fun hne a ha => (hbox hne a ha).of_domSub (frameInBoxB_domSub hb)) a ha hf
    · simp only [hb]
      exact ⟨f, rfl, hf⟩
  learns := by
    intro f db hdb
    by_cases hb : frameInBoxB box f = true
    · simp only [hb, if_true]
      exact prefixPropagationClosure_learns leaf original props hc f db hdb
        (fun hne a ha => (hbox hne a ha).of_domSub (frameInBoxB_domSub hb))
    · simp only [hb]
      intro c hc; simp at hc

end LeanFzn.Solver.Propagation
