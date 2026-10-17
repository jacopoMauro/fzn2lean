/-
Purpose: preserve Boolean prefix pins through the structural operations used by LCG runs.
Dependencies: LcgRunInvariantFrameShape defines BoolPinsOn and frame synchronization;
PendingBacked supplies canonical-trail membership for sibling resumption.
DAG: shape-aware frame helpers -> Boolean pin preservation -> mixed run invariant.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrameShape
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantReasons

namespace LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgFamilies

theorem boolPinsOn_nil (tr : List TrailEntry) : BoolPinsOn tr [] := by
  intro s b h
  simp at h

theorem boolPinsOn_mono {tr tr' : List TrailEntry} {pre : List Value}
    (hsub : ∀ e ∈ tr, e ∈ tr') (h : BoolPinsOn tr pre) : BoolPinsOn tr' pre := by
  intro s b hb
  obtain ⟨e, he, hl⟩ := h s b hb
  exact ⟨e, hsub e he, hl⟩

/-- Canonical resumption reconstructs Boolean pins as well as integer pins. -/
theorem canonical_boolPinsOn (orig : List Domain) (f : BranchFrame) :
    BoolPinsOn (canonicalTrail orig f) f.2 := by
  intro s b hb
  have hs : s < f.2.length := (List.getElem?_eq_some_iff.mp hb).1
  have hv : f.2[s] = Value.bool b := by
    rw [List.getElem?_eq_getElem hs] at hb
    exact Option.some.inj hb
  refine ⟨⟨(posBool s b).norm, s + 1, none⟩, ?_, rfl⟩
  apply List.mem_append_left
  rw [mem_canonicalPins]
  exact ⟨(Value.bool b, s), mem_zipIdx_iff'.mpr ⟨hs, hv⟩, posBool s b, rfl, rfl⟩

theorem boolPinsOn_filter {tr tr' : List TrailEntry} {f g : BranchFrame} {l : Literal}
    (h : BoolPinsOn tr f.2) (hf : filterFrame l f = some g)
    (hsub : ∀ e ∈ tr, e ∈ tr') : BoolPinsOn tr' g.2 := by
  rw [filterFrame_prefix hf]
  exact boolPinsOn_mono hsub h

theorem boolPinsOn_syncAll {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (h : BoolPinsOn bs.trail bs.frame.2) :
    BoolPinsOn (syncAll orig bs).trail (syncAll orig bs).frame.2 := by
  rw [syncAll_frame]
  exact boolPinsOn_mono (syncAll_trail_sub orig bs) h

theorem boolPinsOn_syncSlot {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (s : Nat) (h : BoolPinsOn bs.trail bs.frame.2) :
    BoolPinsOn (syncSlot orig bs s).trail (syncSlot orig bs s).frame.2 := by
  rw [syncSlot_frame]
  exact boolPinsOn_mono (syncSlot_trail_sub orig bs s) h

/-- Choosing a Boolean extends the prefix and records its new pin. -/
theorem boolPinsOn_append_bool {tr tr' : List TrailEntry} {pre : List Value} {b : Bool}
    (h : BoolPinsOn tr pre) (hsub : ∀ e ∈ tr, e ∈ tr')
    {e : TrailEntry} (he : e ∈ tr') (hl : e.literal = posBool pre.length b) :
    BoolPinsOn tr' (pre ++ [Value.bool b]) := by
  intro s c hc
  by_cases hs : s < pre.length
  · have hc' : pre[s]? = some (.bool c) := by
      rwa [List.getElem?_append_left hs] at hc
    exact boolPinsOn_mono hsub h s c hc'
  · have hlen : s < (pre ++ [Value.bool b]).length :=
      (List.getElem?_eq_some_iff.mp hc).1
    have hse : s = pre.length := by simp only [List.length_append, List.length_singleton] at hlen; omega
    subst s
    have hbc : b = c := by simpa using hc
    subst c
    exact ⟨e, he, hl⟩

/-- Choosing an integer leaves the set of Boolean prefix positions unchanged. -/
theorem boolPinsOn_append_int {tr tr' : List TrailEntry} {pre : List Value} {k : Int}
    (h : BoolPinsOn tr pre) (hsub : ∀ e ∈ tr, e ∈ tr') :
    BoolPinsOn tr' (pre ++ [Value.int k]) := by
  intro s b hb
  by_cases hs : s < pre.length
  · have hb' : pre[s]? = some (.bool b) := by
      rwa [List.getElem?_append_left hs] at hb
    exact boolPinsOn_mono hsub h s b hb'
  · have hlen : s < (pre ++ [Value.int k]).length :=
      (List.getElem?_eq_some_iff.mp hb).1
    have hse : s = pre.length := by simp only [List.length_append, List.length_singleton] at hlen; omega
    subst s
    simp at hb

/-- A sibling resume reconstructs and retains all Boolean prefix pins. -/
theorem boolPinsOn_resume {leaf : Assignment → Bool} (orig : List Domain)
    (bs : BranchState leaf) (f : BranchFrame) :
    BoolPinsOn (resumePending orig bs f).trail f.2 :=
  boolPinsOn_mono (syncAll_trail_sub orig (resumePendingBase orig bs f))
    (canonical_boolPinsOn orig f)

/-- Shape-aware sibling resumption establishes the frame invariant without
an integer-only box hypothesis. -/
theorem frameJ_resume_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) (bs : BranchState leaf)
    {f : BranchFrame} (hb : PendingBacked orig f) :
    FrameJ orig (resumePending orig bs f).trail f := by
  have hfits : ∀ s v, v ∈ (Frame.domains f).getD s [] → v ∈ orig.getD s [] := hb.fit
  exact frameJ_syncAll_shape (bs := resumePendingBase orig bs f) hshape
    (canonical_pinsOn orig f) (canonical_boolPinsOn orig f)
    (narrowing_complete_canonical hb.shape hb.full_len) hfits
    (canonical_agree hb.shape hfits)

/-- The filtered branch followed by whole-frame synchronization preserves
shape-aware frame explanation and Boolean prefix pins. -/
theorem frameJ_narrow_syncAll_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) {tr : List TrailEntry} {F g : BranchFrame}
    {l : Literal} {e : TrailEntry} (hJ : FrameJ orig tr F)
    (hp : BoolPinsOn tr F.2) (hf : filterFrame l F = some g)
    (hel : e.literal = l.norm) (bs : BranchState leaf) (hbs : bs.frame = g)
    (hsub : ∀ x ∈ tr, x ∈ bs.trail) (he : e ∈ bs.trail)
    (hnew : ∀ x ∈ bs.trail, x ∈ tr ∨ x = e) :
    FrameJ orig (syncAll orig bs).trail g ∧
      BoolPinsOn (syncAll orig bs).trail g.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := narrow_pre' hJ hf hel hsub he hnew
  have hbp : BoolPinsOn bs.trail g.2 := boolPinsOn_filter hp hf hsub
  constructor
  · have hh := frameJ_syncAll_shape hshape bs (by rw [hbs]; exact h1)
      (by rw [hbs]; exact hbp) (by rw [hbs]; exact h2)
      (by rw [hbs]; exact h3) (by rw [hbs]; exact h4)
    rwa [hbs] at hh
  · exact boolPinsOn_mono (syncAll_trail_sub orig bs) hbp

/-- Propagation closure preserves Boolean pins: it appends trail entries and
keeps the chosen prefix. -/
theorem boolPinsOn_closure {leaf : Assignment → Bool} {orig : List Domain}
    (original : List Clause) (props : List Propagator) {bs : BranchState leaf}
    (h : BoolPinsOn bs.trail bs.frame.2) :
    BoolPinsOn (explainedClosure orig original props bs).trail
      (explainedClosure orig original props bs).frame.2 := by
  rw [explainedClosure_prefix]
  exact boolPinsOn_mono (explainedClosure_trail_sub orig original props bs) h

theorem frameJ_narrow_sync_shape {orig : List Domain} (hint : ShapeTypedDomains orig)
    {tr : List TrailEntry} {F g : BranchFrame} {l : Literal} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g) (hel : e.literal = l.norm)
    (bs : BranchState leaf) (hbs : bs.frame = g) (hbt : bs.trail = tr ++ [e]) :
    FrameJ orig (syncSlot orig bs l.atom.slot).trail g := by
  have hsub0 : ∀ x ∈ tr, x ∈ bs.trail := fun x hx => by rw [hbt]; exact List.mem_append_left _ hx
  have heN : e ∈ bs.trail := by rw [hbt]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hsubS := syncSlot_trail_sub orig bs l.atom.slot
  have hnc : NarrowingComplete bs.trail orig g := nc_narrow hJ.nc hf hsub0 heN hel
  have hfits : ∀ s v, v ∈ (Frame.domains g).getD s [] → v ∈ orig.getD s [] :=
    fun s v hv => hJ.fits s v (Frame.domains_subsets hf s v hv)
  have hag : ∀ s', SlotAgree bs.trail (Frame.domains g) s' := by
    intro s' x hx hxs v hv
    rw [hbt] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hJ.agree s' x hx hxs v (Frame.domains_subsets hf s' v hv)
    · have : x = e := List.mem_singleton.mp hx
      subst this
      rw [hel, norm_atom_slot] at hxs
      rw [hel, norm_valueHolds]
      rw [← hxs] at hv
      exact filterFrame_holds hf v hv
  have hp : g.2 = F.2 := filterFrame_prefix hf
  refine ⟨?_, ?_, ?_, hfits, ?_⟩
  · intro s
    by_cases hs : s = l.atom.slot
    · subst hs
      by_cases hlt : l.atom.slot < F.2.length
      · have hgF := filterFrame_pre_eq hf hlt
        subst hgF
        exact (hJ.expl _).mono (fun x hx => hsubS x (hsub0 x hx))
      · have hle : g.2.length ≤ l.atom.slot := by rw [hp]; omega
        have := syncSlot_explains_shape (orig := orig) (bs := bs) (s := l.atom.slot) hint
          (by rw [hbs]; exact frame_views hint hfits) (by rw [hbs]; exact hle)
          (by rw [hbs]; exact hnc) (by rw [hbs]; exact hfits _ )
          (by rw [hbs]; exact hag _)
        rw [hbs] at this
        exact this
    · have := (hJ.expl s).mono (fun x hx => hsubS x (hsub0 x hx))
      exact ExplSlot.congr (filterFrame_getD_ne hf hs).symm this
  · intro s k hk
    rw [hp] at hk
    obtain ⟨x, hx, hxl⟩ := hJ.pins s k hk
    exact ⟨x, hsubS x (hsub0 x hx), hxl⟩
  · exact nc_mono hsubS hnc
  · intro s'
    have := syncSlot_slotAgree orig bs l.atom.slot s' (by rw [hbs]; exact hag s')
    rw [hbs] at this; exact this

/-! ## The split (decide) child -/


theorem frameJ_stepNarrowSync_shape {orig : List Domain} (hint : ShapeTypedDomains orig)
    (bs : BranchState leaf) (d : ProductiveDeduction leaf bs)
    (hJ : FrameJ orig bs.trail bs.frame) :
    FrameJ orig (stepNarrowSync orig bs d).trail (stepNarrowSync orig bs d).frame := by
  rw [stepNarrowSync_frame]
  exact frameJ_narrow_sync_shape hint hJ d.filtered
    (e := ⟨d.literal.norm, bs.level, some { clause := d.reason }⟩) rfl
    (narrowState bs d.frame d.literal d.reason d.learned) rfl rfl


theorem frameJ_closure_shape {orig : List Domain} (hint : ShapeTypedDomains orig) (original : List Clause)
    (props : List Propagator) :
    ∀ (bs : BranchState leaf), FrameJ orig bs.trail bs.frame →
      FrameJ orig (explainedClosure orig original props bs).trail
        (explainedClosure orig original props bs).frame := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      FrameJ orig bs.trail bs.frame →
      FrameJ orig (explainedClosure orig original props bs).trail
        (explainedClosure orig original props bs).frame from
    fun bs => h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hJ
    rw [explainedClosure]
    split
    · exact hJ
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hJ
    rw [explainedClosure]
    split
    · exact hJ
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      exact ih _ hmass (frameJ_stepNarrowSync_shape hint bs d hJ)

theorem explDoms_root_shape {orig : List Domain} (hint : ShapeTypedDomains orig) :
    ExplDoms orig [] orig := by
  intro s
  refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 h2 h3 => ?_⟩
  · obtain ⟨-, hall⟩ := domMaxI_spec h
    refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    obtain ⟨k, hk⟩ := slot_viewed hint hv
    have := hall _ hv k hk
    simp [Literal.valueHolds, negLe, hk]
    omega
  · obtain ⟨-, hall⟩ := domMinI_spec h
    refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    obtain ⟨k, hk⟩ := slot_viewed hint hv
    have := hall _ hv k hk
    simp [Literal.valueHolds, posLe, hk]
    omega
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hv' : v ∈ orig.getD s [] := hv
    rw [h] at hv'
    have : v = Value.int c := List.mem_singleton.mp hv'
    subst this
    simp [Literal.valueHolds, posNe, Value.intView]
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    obtain ⟨k, hk⟩ := slot_viewed hint hv
    have := h3 _ hv
    simp [Literal.valueHolds, negNe, hk] at this ⊢
    exact this


/-- The mixed-domain root frame satisfies the structural explanation invariant. -/
theorem frameJ_root_shape {orig : List Domain} (hshape : ShapeTypedDomains orig) :
    FrameJ orig [] (orig, []) where
  expl := by simpa [Frame.domains] using explDoms_root_shape hshape
  pins := fun s k hk => by simp at hk
  nc := fun i w hw hn => by
    exact absurd (by simpa using hw : w ∈ orig.getD (0 + i) []) (by simpa using hn)
  fits := fun s v hv => by simpa [Frame.domains] using hv
  agree := fun s e he => by cases he

/-- Restoration keeps the checkpoint's Boolean pins even when the assertion
is already present and the runtime skips appending it. -/
theorem boolPinsOn_restoreNarrow {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hp : BoolPinsOn p.checkpoint.trail p.checkpoint.frame.2)
    (hr : p.restoreNarrow bs = some restored) :
    BoolPinsOn restored.trail restored.frame.2 := by
  obtain ⟨g, hf, hframe, htrail⟩ := restoreNarrow_shape hr
  rw [hframe, filterFrame_prefix hf, htrail]
  exact boolPinsOn_mono (fun e he => List.mem_append_left _ he) hp

/-- The full performed backjump preserves Boolean prefix pins through
restoration, synchronization and all subsequent propagation. -/
theorem boolPinsOn_perform {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hp : BoolPinsOn p.checkpoint.trail p.checkpoint.frame.2)
    (hr : p.perform bs orig original props = some restored) :
    BoolPinsOn restored.trail restored.frame.2 := by
  unfold BackjumpPlan.perform at hr
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hr
  subst hres
  exact boolPinsOn_closure original props
    (boolPinsOn_syncAll (boolPinsOn_restoreNarrow hp hs))

/-- Boolean decisions preserve shape-aware frame explanation; the selected
Boolean pin supplies the newly fixed slot's bounds and absence. -/
theorem frameJ_split_bool_shape {orig : List Domain} {tr tr' : List TrailEntry} {v : Value} {vs : Domain}
    {doms : List Domain} {pre : List Value} {b : Bool} {e : TrailEntry}
    (hshape : ShapeTypedDomains orig)
    (hJ : FrameJ orig tr (((v :: vs) :: doms), pre)) (hv : v = Value.bool b)
    (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr') (hel : e.literal = posBool pre.length b)
    (hag : ∀ s', SlotAgree tr' (Frame.domains (doms, pre ++ [v])) s') :
    FrameJ orig tr' (doms, pre ++ [v]) := by
  have hb : BoolSlot orig pre.length := by
    have hm : Value.bool b ∈ orig.getD pre.length [] := hJ.fits _ _ (by
      rw [split_domains_parent, hv]
      exact List.mem_cons_self)
    rcases slot_cases hshape pre.length with hi | hb
    · obtain ⟨k, hk⟩ := hi _ hm
      cases hk
    · exact hb
  subst hv
  refine ⟨?_, ?_, ?_, ?_, hag⟩
  · intro s
    by_cases hs : s = pre.length
    · subst hs
      exact explSlot_boolPin hb he hel (split_domains_eq _ vs doms pre)
    · exact ExplSlot.congr (split_domains_ne _ vs doms pre hs).symm ((hJ.expl s).mono hsub)
  · intro s k hk
    by_cases hlt : s < pre.length
    · have hk' : pre[s]? = some (Value.int k) := by
        rwa [List.getElem?_append_left hlt] at hk
      obtain ⟨x, hx, hxl⟩ := hJ.pins s k hk'
      exact ⟨x, hsub x hx, hxl⟩
    · have hlen : s < (pre ++ [Value.bool b]).length :=
        (List.getElem?_eq_some_iff.mp hk).1
      have hs : s = pre.length := by simp only [List.length_append, List.length_singleton] at hlen; omega
      subst s
      simp at hk
  · intro i w horig hnot
    have h1 : w ∈ orig.getD (pre.length + (i + 1)) [] := by
      have : (pre ++ [Value.bool b]).length + i = pre.length + (i + 1) := by simp; omega
      rw [← this]; exact horig
    obtain ⟨x, hx, hxs, hxf⟩ := hJ.nc (i + 1) w h1 (by simpa using hnot)
    refine ⟨x, hsub x hx, ?_, hxf⟩
    show x.literal.atom.slot = (pre ++ [Value.bool b]).length + i
    rw [hxs]; simp; omega
  · intro s w hw
    by_cases hs : s = pre.length
    · subst hs
      rw [split_domains_eq _ vs doms pre] at hw
      have : w = Value.bool b := List.mem_singleton.mp hw
      subst this
      apply hJ.fits pre.length
      rw [split_domains_parent]; exact List.mem_cons_self
    · apply hJ.fits s
      rw [← split_domains_ne (Value.bool b) vs doms pre hs]; exact hw


/-- Shape-aware restoration handles both an appended assertion and the
runtime guard that reuses an assertion already in the checkpoint trail. -/
theorem frameJ_perform_aux_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) {p : BackjumpPlan leaf} {g : BranchFrame}
    (hJ : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hpins : BoolPinsOn p.checkpoint.trail p.checkpoint.frame.2)
    (hf : filterFrame p.asserting p.checkpoint.frame = some g)
    (s : BranchState leaf) (hsf : s.frame = g)
    (hst : s.trail = p.checkpoint.trail ++ p.assertExtra) :
    FrameJ orig (syncAll orig s).trail g := by
  rcases p.assertExtra_cases with hx | hx
  · obtain ⟨e, he, hel⟩ : ∃ e ∈ p.checkpoint.trail, e.literal = p.asserting.norm := by
      refine Classical.byContradiction fun hno => ?_
      exact BackjumpPlan.assertExtra_ne_nil_of_fresh p
        (fun e he h => hno ⟨e, he, h⟩) hx
    refine (frameJ_narrow_syncAll_shape hshape hJ hpins hf hel s hsf
      (fun x hmem => ?_) ?_ (fun x hmem => Or.inl ?_)).1
    · rw [hst, hx]
      simpa using hmem
    · rw [hst, hx]
      simpa using he
    · rw [hst, hx] at hmem
      simpa using hmem
  · let e : TrailEntry := ⟨p.asserting.norm, p.target, some { clause := p.learned }⟩
    have ht : s.trail = p.checkpoint.trail ++ [e] := by rw [hst, hx]; rfl
    refine (frameJ_narrow_syncAll_shape hshape hJ hpins hf (e := e) rfl s hsf
      (fun x hmem => ?_) ?_ (fun x hmem => ?_)).1
    · rw [ht]
      exact List.mem_append_left _ hmem
    · rw [ht]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [ht] at hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact Or.inl hmem
      · exact Or.inr (List.mem_singleton.mp hmem)

/-- A performed backjump preserves the mixed-domain frame invariant and
Boolean pins through its actual propagation closure. -/
theorem frameJ_perform_shape {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hshape : ShapeTypedDomains orig) {p : BackjumpPlan leaf}
    {bs restored : BranchState leaf}
    (hJ : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hpins : BoolPinsOn p.checkpoint.trail p.checkpoint.frame.2)
    (hr : p.perform bs orig original props = some restored) :
    FrameJ orig restored.trail restored.frame ∧
      BoolPinsOn restored.trail restored.frame.2 := by
  constructor
  · unfold BackjumpPlan.perform at hr
    obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hr
    subst hres
    obtain ⟨g, hf, hsf, hst⟩ := restoreNarrow_shape hs
    have hj := frameJ_perform_aux_shape hshape hJ hpins hf s hsf hst
    exact frameJ_closure_shape hshape original props (syncAll orig s)
      (by rw [syncAll_frame, hsf]; exact hj)
  · exact boolPinsOn_perform hpins hr

/-- Both supported decision sorts preserve the Boolean prefix-pin invariant. -/
theorem boolPinsOn_append_value {tr tr' : List TrailEntry} {pre : List Value}
    {v : Value} {l : Literal} {e : TrailEntry} (h : BoolPinsOn tr pre)
    (hval : valueLiteral pre.length v = some l) (hsub : ∀ x ∈ tr, x ∈ tr')
    (he : e ∈ tr') (hel : e.literal = l.norm) : BoolPinsOn tr' (pre ++ [v]) := by
  cases v with
  | int k => exact boolPinsOn_append_int h hsub
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact boolPinsOn_append_bool h hsub he hel
  | _ => cases hval

/-- Both supported value-literal decisions preserve shape-aware frame explanation. -/
theorem frameJ_split_value_shape {orig : List Domain} {tr tr' : List TrailEntry}
    {v : Value} {vs : Domain} {doms : List Domain} {pre : List Value}
    {l : Literal} {e : TrailEntry} (hshape : ShapeTypedDomains orig)
    (hJ : FrameJ orig tr (((v :: vs) :: doms), pre))
    (hval : valueLiteral pre.length v = some l) (hsub : ∀ x ∈ tr, x ∈ tr')
    (he : e ∈ tr') (hel : e.literal = l.norm)
    (hag : ∀ s, SlotAgree tr' (Frame.domains (doms, pre ++ [v])) s) :
    FrameJ orig tr' (doms, pre ++ [v]) := by
  cases v with
  | int k =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact frameJ_split hJ rfl hsub he hel hag
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact frameJ_split_bool_shape hshape hJ rfl hsub he hel hag
  | _ => cases hval

/-- Productive propagation preserves Boolean pins on its unchanged prefix. -/
theorem boolPinsOn_stepNarrowSync {leaf : Assignment → Bool} {orig : List Domain}
    (bs : BranchState leaf) (d : ProductiveDeduction leaf bs)
    (h : BoolPinsOn bs.trail bs.frame.2) :
    BoolPinsOn (stepNarrowSync orig bs d).trail (stepNarrowSync orig bs d).frame.2 := by
  unfold stepNarrowSync
  apply boolPinsOn_syncSlot
  change BoolPinsOn (bs.trail ++ [_]) d.frame.2
  rw [filterFrame_prefix d.filtered]
  exact boolPinsOn_mono (fun e he => List.mem_append_left _ he) h

/-- A value-literal decision agrees with every assignment covered by its child,
for either integer or Boolean values. -/
theorem split_agree_push_value {tr : List TrailEntry} {v : Value} {vs : Domain}
    {doms : List Domain} {pre : List Value} {l : Literal} {lvl : Nat}
    (hag : ∀ s, SlotAgree tr (Frame.domains (((v :: vs) :: doms), pre)) s)
    (hv : valueLiteral pre.length v = some l) :
    ∀ s, SlotAgree (tr ++ [⟨l.norm, lvl, none⟩])
      (Frame.domains (doms, pre ++ [v])) s := by
  intro s x hx hxs w hw
  rcases List.mem_append.mp hx with hx | hx
  · exact hag s x hx hxs w (split_domains_sub v vs doms pre s w hw)
  · have hx' : x = ⟨l.norm, lvl, none⟩ := List.mem_singleton.mp hx
    subst x
    have hs : s = pre.length := by
      rw [norm_atom_slot, valueLiteral_atom_slot hv] at hxs
      exact hxs.symm
    rw [hs, split_domains_eq v vs doms pre] at hw
    have hw' : w = v := List.mem_singleton.mp hw
    subst w
    rw [norm_valueHolds]
    exact valueLiteral_valueHolds_self hv

end LeanFzn.Solver.UIP.LcgRunInv
