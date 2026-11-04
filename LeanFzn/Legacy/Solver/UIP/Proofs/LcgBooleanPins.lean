/-
Purpose: preserve Boolean pins through the structural operations used by LCG runs.
Dependencies: LcgRunInvariantFrameShape defines BoolPinsOn and frame synchronization;
PendingBacked supplies canonical-trail membership for sibling resumption.
DAG: shape-aware frame helpers -> Boolean pin preservation -> mixed run invariant.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrameShape
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantReasons

namespace LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgFamilies

/-! ## Boolean pins from the integer-pin predicate -/

theorem boolPinsOn_of_pinsOn {tr : List TrailEntry} {f : BranchFrame}
    (h : PinsOn tr f) : BoolPinsOn tr f := by
  constructor
  · intro k hk
    obtain ⟨v, l, hv, -, -⟩ := h k hk
    exact ⟨v, hv⟩
  · intro s hs b hb
    obtain ⟨v, l, hv, hl, e, he, hel⟩ := h s hs
    have hv' : v = Value.bool b := by
      have hE1 := enum_getD_of_enum_singleton hb
      have hE2 := enum_getD_of_enum_singleton hv
      have hEq : [Value.bool b] = [v] := by rw [← hE1, hE2]
      simpa using hEq.symm
    subst v
    have hl' : posBool s b = l := by simpa [valueLiteral] using hl
    exact ⟨e, he, by rw [hel, ← hl']⟩

theorem boolPinsOn_nil {f : BranchFrame} (tr : List TrailEntry) (hf : f.order = []) :
    BoolPinsOn tr f := by
  constructor <;> intro k hk <;> (rw [hf] at hk; simp at hk)

theorem boolPinsOn_mono {tr tr' : List TrailEntry} {f : BranchFrame}
    (hsub : ∀ e ∈ tr, e ∈ tr') (h : BoolPinsOn tr f) : BoolPinsOn tr' f := by
  constructor
  · exact h.1
  · intro s hs b hb
    obtain ⟨e, he, hl⟩ := h.2 s hs b hb
    exact ⟨e, hsub e he, hl⟩

/-- Canonical resumption reconstructs Boolean pins as well as integer pins. -/
theorem canonical_boolPinsOn (orig : List Domain) (f : BranchFrame)
    (hp : PrefixPinned f) : BoolPinsOn (canonicalTrail orig f) f := by
  constructor
  · intro s hs
    obtain ⟨v, hv, -, -⟩ := hp.2 s hs
    exact ⟨v, hv⟩
  · intro s hs b hb
    obtain ⟨v, hv, l, hl⟩ := hp.2 s hs
    have hv' : v = Value.bool b := by
      rw [hb] at hv
      simpa using (Option.some.inj hv).symm
    subst v
    obtain ⟨j, hjlt, hjget⟩ := List.getElem_of_mem hs
    refine ⟨⟨posBool s b, j + 1, none⟩, ?_, ?_⟩
    · apply List.mem_append_left
      rw [mem_canonicalPins]
      refine ⟨(s, j), mem_zipIdx_iff'.mpr ⟨hjlt, hjget⟩, Value.bool b, posBool s b,
        hb, rfl, ?_⟩
      rfl
    · rfl

/-- Filtering a frame keeps its Boolean pins (the filtered frame keeps the
decided singletons). -/
theorem boolPinsOn_filter {tr tr' : List TrailEntry} {f g : BranchFrame} {l : Literal}
    (h : BoolPinsOn tr f) (hf : filterFrame l f = some g)
    (hsub : ∀ e ∈ tr, e ∈ tr') : BoolPinsOn tr' g := by
  constructor
  · intro s hs
    have hsF : s ∈ f.order := by rwa [Frame.filterFrame_order hf] at hs
    obtain ⟨v, hv⟩ := h.1 s hsF
    exact ⟨v, filterFrame_singleton hf hv⟩
  · intro s hs b hb
    have hsF : s ∈ f.order := by rwa [Frame.filterFrame_order hf] at hs
    obtain ⟨v, hv⟩ := h.1 s hsF
    have hvb : v = Value.bool b := by
      have hmem : Value.bool b ∈ f.doms.getD s Dom.empty :=
        filterFrame_subsets hf s (Value.bool b) (mem_getD_of_enum_singleton hb)
      have hE : Dom.enum (f.doms.getD s Dom.empty) = [v] :=
        enum_getD_of_enum_singleton hv
      have hmemE : Value.bool b ∈ Dom.enum (f.doms.getD s Dom.empty) := by
        rw [← domElems_eq_enum]
        exact (DomainLike.mem_iff _ _).mp hmem
      rw [hE] at hmemE
      exact (List.mem_singleton.mp hmemE).symm
    subst v
    obtain ⟨y, hy, hyl⟩ := h.2 s hsF b hv
    exact ⟨y, hsub y hy, hyl⟩

theorem boolPinsOn_syncAll {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (h : BoolPinsOn bs.trail bs.frame) :
    BoolPinsOn (syncAll orig bs).trail (syncAll orig bs).frame := by
  rw [syncAll_frame]
  exact boolPinsOn_mono (syncAll_trail_sub orig bs) h

theorem boolPinsOn_syncSlot {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} (s : Nat) (h : BoolPinsOn bs.trail bs.frame) :
    BoolPinsOn (syncSlot orig bs s).trail (syncSlot orig bs s).frame := by
  rw [syncSlot_frame]
  exact boolPinsOn_mono (syncSlot_trail_sub orig bs s) h

/-- Choosing a Boolean at a fresh slot records its new pin. -/
theorem boolPinsOn_append_bool {tr tr' : List TrailEntry} {f : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain} {b : Bool}
    (h : BoolPinsOn tr f) (hd : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hv : v = Value.bool b)
    (hk : k ∉ f.order) (hsub : ∀ e ∈ tr, e ∈ tr')
    {e : TrailEntry} (he : e ∈ tr') (hel : e.literal = posBool k b) :
    BoolPinsOn tr' (f.pin k v) := by
  subst v
  obtain ⟨d, hd', -⟩ := exists_dom_of_enum_cons hd
  constructor
  · intro s hs
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      obtain ⟨w, hw⟩ := h.1 s hs
      refine ⟨w, ?_⟩
      rw [BranchFrame.pin_doms, List.getElem?_set]
      rw [if_neg (fun h => hsk h.symm)]
      exact hw
    · rw [List.mem_singleton] at hs
      subst s
      exact ⟨Value.bool b, by
        rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd').1]
        simp⟩
  · intro s hs c hc
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      have hcF : f.doms[s]?.map Dom.enum = some [Value.bool c] := by
        rw [BranchFrame.pin_doms, List.getElem?_set,
          if_neg (fun h => hsk h.symm)] at hc
        exact hc
      obtain ⟨y, hy, hyl⟩ := h.2 s hs c hcF
      exact ⟨y, hsub y hy, hyl⟩
    · rw [List.mem_singleton] at hs
      subst s
      rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd').1] at hc
      have hbc : b = c := by
        have := Option.some.inj hc
        simpa [Dom.enum_ofList] using this
      subst c
      exact ⟨e, he, hel⟩

/-- Choosing an integer at a fresh slot leaves Boolean pins unchanged. -/
theorem boolPinsOn_append_int {tr tr' : List TrailEntry} {f : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain} {i : Int}
    (h : BoolPinsOn tr f) (hd : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hv : v = Value.int i)
    (hk : k ∉ f.order) (hsub : ∀ e ∈ tr, e ∈ tr') :
    BoolPinsOn tr' (f.pin k v) := by
  subst v
  obtain ⟨d, hd', -⟩ := exists_dom_of_enum_cons hd
  constructor
  · intro s hs
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      obtain ⟨w, hw⟩ := h.1 s hs
      refine ⟨w, ?_⟩
      rw [BranchFrame.pin_doms, List.getElem?_set]
      rw [if_neg (fun h => hsk h.symm)]
      exact hw
    · rw [List.mem_singleton] at hs
      subst s
      exact ⟨Value.int i, by
        rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd').1]
        simp⟩
  · intro s hs c hc
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      have hcF : f.doms[s]?.map Dom.enum = some [Value.bool c] := by
        rw [BranchFrame.pin_doms, List.getElem?_set,
          if_neg (fun h => hsk h.symm)] at hc
        exact hc
      obtain ⟨y, hy, hyl⟩ := h.2 s hs c hcF
      exact ⟨y, hsub y hy, hyl⟩
    · rw [List.mem_singleton] at hs
      subst s
      rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd').1] at hc
      simp [Dom.enum_ofList] at hc

/-- A sibling resume reconstructs and retains all Boolean pins. -/
theorem boolPinsOn_resume {leaf : Assignment → Bool} (orig : List Domain)
    (bs : BranchState leaf) (f : BranchFrame) (hb : PendingBacked orig f) :
    BoolPinsOn (resumePending orig bs f).trail f :=
  boolPinsOn_mono (syncAll_trail_sub orig (resumePendingBase orig bs f))
    (canonical_boolPinsOn orig f hb.pins)

/-- Shape-aware sibling resumption establishes the frame invariant without
an integer-only box hypothesis. -/
theorem frameJ_resume_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) (bs : BranchState leaf)
    {f : BranchFrame} (hb : PendingBacked orig f) :
    FrameJ orig (resumePending orig bs f).trail f := by
  have hfits : ∀ s v, v ∈ (Frame.domains f).getD s Dom.empty →
      v ∈ orig.getD s Dom.empty := hb.fit
  exact frameJ_syncAll_shape (bs := resumePendingBase orig bs f) hshape
    (canonical_pinsOn orig f hb.pins) (canonical_boolPinsOn orig f hb.pins)
    (narrowing_complete_canonical hb.shape hb.full_len) hfits
    (canonical_agree hb.shape hfits)

/-! ## Shape-aware one-step frame lemmas -/

theorem frameJ_narrow_sync_shape {orig : List Domain} (hshape : ShapeTypedDomains orig)
    {tr : List TrailEntry} {F g : BranchFrame} {l : Literal} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g) (hel : e.literal = l.norm)
    (bs : BranchState leaf) (hbs : bs.frame = g) (hbt : bs.trail = tr ++ [e]) :
    FrameJ orig (syncSlot orig bs l.atom.slot).trail g := by
  have hsub0 : ∀ x ∈ tr, x ∈ bs.trail := fun x hx => by rw [hbt]; exact List.mem_append_left _ hx
  have heN : e ∈ bs.trail := by rw [hbt]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hsubS := syncSlot_trail_sub orig bs l.atom.slot
  have hnc : NarrowingComplete bs.trail orig g := nc_narrow hJ.nc hf hsub0 heN hel
  have hfits : ∀ s v, v ∈ (Frame.domains g).getD s Dom.empty →
      v ∈ orig.getD s Dom.empty :=
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
  have hp : g.order = F.order := Frame.filterFrame_order hf
  refine ⟨?_, ?_, ?_, hfits, ?_⟩
  · intro s
    by_cases hs : s ∈ F.order
    · obtain ⟨v, l', hv, -, -⟩ := hJ.pins s hs
      have hgd : Dom.enum ((Frame.domains g).getD s Dom.empty) =
          Dom.enum ((Frame.domains F).getD s Dom.empty) := by
        show Dom.enum (g.doms.getD s Dom.empty) = Dom.enum (F.doms.getD s Dom.empty)
        rw [enum_getD_of_enum_singleton (filterFrame_singleton hf hv),
          enum_getD_of_enum_singleton hv]
      exact ExplSlot.congr hgd.symm
        ((explSlot_decided_shape hshape hJ.pins hJ.fits hs).mono
          (fun x hx => hsubS x (hsub0 x hx)))
    · by_cases hsl : s = l.atom.slot
      · subst hsl
        have hdecg : l.atom.slot ∉ g.order := by rw [hp]; exact hs
        have := syncSlot_explains_shape (orig := orig) (bs := bs) (s := l.atom.slot)
          hshape (by rw [hbs]; exact frame_views hshape hfits) (by rw [hbs]; exact hnc)
          (by rw [hbs]; exact hfits _) (by rw [hbs]; exact hag _)
          (by rw [hbs]; exact hdecg)
        rw [hbs] at this
        exact this
      · exact ExplSlot.congr (congrArg Dom.enum (filterFrame_getD_ne hf hsl)).symm
          ((hJ.expl s).mono (fun x hx => hsubS x (hsub0 x hx)))
  · intro s hs
    rw [hp] at hs
    obtain ⟨v, l', hv, hl', x, hx, hxl⟩ := hJ.pins s hs
    exact ⟨v, l', filterFrame_singleton hf hv, hl', x, hsubS x (hsub0 x hx), hxl⟩
  · exact nc_mono hsubS hnc
  · intro s'
    have := syncSlot_slotAgree orig bs l.atom.slot s' (by rw [hbs]; exact hag s')
    rw [hbs] at this; exact this

theorem frameJ_stepNarrowSync_shape {orig : List Domain} (hint : ShapeTypedDomains orig)
    (bs : BranchState leaf) (d : ProductiveDeduction leaf bs)
    (hJ : FrameJ orig bs.trail bs.frame) :
    FrameJ orig (stepNarrowSync orig bs d).trail (stepNarrowSync orig bs d).frame := by
  rw [stepNarrowSync_frame]
  exact frameJ_narrow_sync_shape hint hJ d.filtered
    (e := ⟨d.literal.norm, bs.level, some { clause := d.reason }⟩) rfl
    (narrowState bs d.frame d.literal d.reason d.learned) rfl rfl

theorem frameJ_closure_shape {orig : List Domain} (hint : ShapeTypedDomains orig)
    (original : List Clause) (props : List Propagator) :
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
    have hvD : v ∈ orig.getD s Dom.empty := (DomainLike.mem_iff _ v).mpr hv
    obtain ⟨k, hk⟩ := slot_viewed hint hvD
    have := hall _ hvD k hk
    simp [Literal.valueHolds, negLe, hk]
    omega
  · obtain ⟨-, hall⟩ := domMinI_spec h
    refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty := (DomainLike.mem_iff _ v).mpr hv
    obtain ⟨k, hk⟩ := slot_viewed hint hvD
    have := hall _ hvD k hk
    simp [Literal.valueHolds, posLe, hk]
    omega
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hv' : v ∈ Dom.enum (orig.getD s Dom.empty) := hv
    rw [h] at hv'
    have : v = Value.int c := List.mem_singleton.mp hv'
    subst this
    simp [Literal.valueHolds, posNe, Value.intView]
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty := (DomainLike.mem_iff _ v).mpr hv
    obtain ⟨k, hk⟩ := slot_viewed hint hvD
    have := h3 _ hvD
    simp [Literal.valueHolds, negNe, hk] at this ⊢
    exact this

/-- The mixed-domain root frame satisfies the structural explanation invariant. -/
theorem frameJ_root_shape {orig : List Domain} (hshape : ShapeTypedDomains orig) :
    FrameJ orig [] { doms := orig, order := [] } where
  expl := by simpa [Frame.domains] using explDoms_root_shape hshape
  pins := fun s hs => by simp at hs
  nc := fun i _ w hw hn => absurd (by simpa [Frame.domains] using hw) hn
  fits := fun s v hv => by simpa [Frame.domains] using hv
  agree := fun s e he => by cases he

/-! ## Split and restoration -/

theorem frameJ_split_bool_shape {orig : List Domain} {tr tr' : List TrailEntry}
    {F : BranchFrame} {k : Nat} {v : Value} {vs : Domain} {b : Bool} {e : TrailEntry}
    (hshape : ShapeTypedDomains orig)
    (hJ : FrameJ orig tr F) (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hv : v = Value.bool b)
    (hk : k ∉ F.order) (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr')
    (hel : e.literal = posBool k b)
    (hag : ∀ s', SlotAgree tr' (Frame.domains (F.pin k v)) s') :
    FrameJ orig tr' (F.pin k v) := by
  subst v
  obtain ⟨dF, hdF, -⟩ := exists_dom_of_enum_cons hd
  have hb : BoolSlot orig k := by
    have hm : Value.bool b ∈ orig.getD k Dom.empty := hJ.fits k _ ((DomainLike.mem_iff _ _).mpr (by
      rw [domElems_eq_enum, split_domains_parent hd]; exact List.mem_cons_self))
    rcases slot_cases hshape k with hi | hb
    · obtain ⟨j, hj⟩ := hi _ hm
      cases hj
    · exact hb
  refine ⟨?_, ?_, ?_, ?_, hag⟩
  · intro s
    by_cases hs : s = k
    · subst s
      exact explSlot_boolPin hb he hel (split_domains_eq hd)
    · exact ExplSlot.congr (congrArg Dom.enum (split_domains_ne hs)).symm
        ((hJ.expl s).mono hsub)
  · intro s hs
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      obtain ⟨v', l', hv', hl', x, hx, hxl⟩ := hJ.pins s hs
      refine ⟨v', l', ?_, hl', x, hsub x hx, hxl⟩
      rw [BranchFrame.pin_doms, List.getElem?_set]
      rw [if_neg (fun h => hsk h.symm)]
      exact hv'
    · rw [List.mem_singleton] at hs
      subst s
      refine ⟨Value.bool b, posBool k b, ?_, ?_, e, he, hel⟩
      · rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hdF).1]
        simp
      · simp [valueLiteral]
  · intro s hs w horig hnot
    have hsorder : s ∉ F.order := by
      rw [BranchFrame.pin_order] at hs
      intro hmem
      exact hs (List.mem_append.mpr (Or.inl hmem))
    by_cases hsk : s = k
    · subst s
      have hwv : w ≠ Value.bool b := by
        intro hw
        apply hnot
        rw [BranchFrame.pin_doms, getD_set_self (List.getElem?_eq_some_iff.mp hdF).1, hw]
        simp
      obtain ⟨c, rfl⟩ := hb w horig
      have hcb : c ≠ b := fun h => hwv (by rw [h])
      refine ⟨e, he, by rw [hel]; rfl, ?_⟩
      rw [hel]
      cases b <;> cases c <;> simp_all [Literal.valueHolds, posBool]
    · have hdom : (Frame.domains (F.pin k (Value.bool b))).getD s Dom.empty =
          (Frame.domains F).getD s Dom.empty := split_domains_ne hsk
      have hwas : w ∉ (Frame.domains F).getD s Dom.empty := by
        rw [← hdom]
        simpa [Frame.domains] using hnot
      obtain ⟨x, hx, hxs, hxf⟩ := hJ.nc s hsorder w horig hwas
      exact ⟨x, hsub x hx, hxs, hxf⟩
  · intro s w hw
    by_cases hsk : s = k
    · subst s
      have hwE : w ∈ Dom.enum
          ((Frame.domains (F.pin k (Value.bool b))).getD k Dom.empty) :=
        (DomainLike.mem_iff _ w).mp hw
      rw [split_domains_eq hd] at hwE
      have : w = Value.bool b := List.mem_singleton.mp hwE
      subst w
      exact hJ.fits k (Value.bool b) ((DomainLike.mem_iff _ _).mpr (by
        rw [domElems_eq_enum, split_domains_parent hd]; exact List.mem_cons_self))
    · exact hJ.fits s w (by rw [← split_domains_ne hsk]; exact hw)

/-- Both supported value-literal decisions preserve shape-aware frame explanation. -/
theorem frameJ_split_value_shape {orig : List Domain} {tr tr' : List TrailEntry}
    {F : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    {l : Literal} {e : TrailEntry} (hshape : ShapeTypedDomains orig)
    (hJ : FrameJ orig tr F) (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hval : valueLiteral k v = some l) (hk : k ∉ F.order)
    (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr') (hel : e.literal = l.norm)
    (hag : ∀ s, SlotAgree tr' (Frame.domains (F.pin k v)) s) :
    FrameJ orig tr' (F.pin k v) := by
  cases v with
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      have hint : ∀ w ∈ orig.getD k Dom.empty, ∃ j : Int, w = Value.int j := by
        intro w hw
        have hm : Value.int i ∈ orig.getD k Dom.empty :=
          hJ.fits k _ ((DomainLike.mem_iff _ _).mpr (by
            rw [domElems_eq_enum, split_domains_parent hd]; exact List.mem_cons_self))
        rcases slot_cases hshape k with hi | hb
        · exact hi w hw
        · obtain ⟨b, hb'⟩ := hb _ hm
          cases hb'
      exact frameJ_split hint hJ hd rfl hk hsub he hel hag
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact frameJ_split_bool_shape hshape hJ hd rfl hk hsub he hel hag
  | _ => cases hval

/-- A value-literal decision agrees with every assignment covered by its child. -/
theorem split_agree_push_value {tr : List TrailEntry} {F : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain} {l : Literal} {lvl : Nat}
    (hag : ∀ s, SlotAgree tr (Frame.domains F) s)
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hval : valueLiteral k v = some l) :
    ∀ s, SlotAgree (tr ++ [⟨l.norm, lvl, none⟩])
      (Frame.domains (F.pin k v)) s := by
  intro s x hx hxs w hw
  rcases List.mem_append.mp hx with hx | hx
  · exact hag s x hx hxs w (split_domains_sub hd s w hw)
  · have hx' : x = ⟨l.norm, lvl, none⟩ := List.mem_singleton.mp hx
    subst x
    have hs : s = k := by
      rw [norm_atom_slot, valueLiteral_atom_slot hval] at hxs
      exact hxs.symm
    have hwE : w ∈ Dom.enum ((Frame.domains (F.pin k v)).getD s Dom.empty) :=
      (DomainLike.mem_iff _ w).mp hw
    rw [hs, split_domains_eq hd] at hwE
    have hw' : w = v := List.mem_singleton.mp hwE
    subst w
    rw [norm_valueHolds]
    exact valueLiteral_valueHolds_self hval

/-- Restoration keeps the checkpoint's Boolean pins even when the assertion
is already present and the runtime skips appending it. -/
theorem boolPinsOn_restoreNarrow {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hp : BoolPinsOn p.checkpoint.trail p.checkpoint.frame)
    (hr : p.restoreNarrow bs = some restored) :
    BoolPinsOn restored.trail restored.frame := by
  obtain ⟨g, hf, hframe, htrail⟩ := restoreNarrow_shape hr
  rw [hframe, htrail]
  exact boolPinsOn_mono (fun e he => List.mem_append_left _ he)
    (boolPinsOn_filter hp hf (fun e he => he))

theorem frameJ_narrow_syncAll_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) {tr : List TrailEntry} {F g : BranchFrame}
    {l : Literal} {e : TrailEntry} (hJ : FrameJ orig tr F)
    (hp : BoolPinsOn tr F) (hf : filterFrame l F = some g)
    (hel : e.literal = l.norm) (bs : BranchState leaf) (hbs : bs.frame = g)
    (hsub0 : ∀ x ∈ tr, x ∈ bs.trail) (he : e ∈ bs.trail)
    (hnew : ∀ x ∈ bs.trail, x ∈ tr ∨ x = e) :
    FrameJ orig (syncAll orig bs).trail g ∧
      BoolPinsOn (syncAll orig bs).trail g := by
  obtain ⟨h1, h2, h3, h4⟩ := narrow_pre' hJ hf hel hsub0 he hnew
  have hbp : BoolPinsOn bs.trail g := boolPinsOn_of_pinsOn h1
  constructor
  · have hh := frameJ_syncAll_shape hshape bs (by rw [hbs]; exact h1)
      (by rw [hbs]; exact hbp) (by rw [hbs]; exact h2)
      (by rw [hbs]; exact h3) (by rw [hbs]; exact h4)
    rwa [hbs] at hh
  · exact boolPinsOn_mono (syncAll_trail_sub orig bs) hbp

theorem frameJ_perform_aux_shape {leaf : Assignment → Bool} {orig : List Domain}
    (hshape : ShapeTypedDomains orig) {p : BackjumpPlan leaf} {g : BranchFrame}
    (hJ : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hf : filterFrame p.asserting p.checkpoint.frame = some g)
    (s : BranchState leaf) (hsf : s.frame = g)
    (hst : s.trail = p.checkpoint.trail ++ p.assertExtra) :
    FrameJ orig (syncAll orig s).trail g := by
  have hpins : BoolPinsOn p.checkpoint.trail p.checkpoint.frame :=
    boolPinsOn_of_pinsOn hJ.pins
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
    (hr : p.perform bs orig original props = some restored) :
    FrameJ orig restored.trail restored.frame ∧
      BoolPinsOn restored.trail restored.frame := by
  unfold BackjumpPlan.perform at hr
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hr
  subst hres
  obtain ⟨g, hf, hsf, hst⟩ := restoreNarrow_shape hs
  have hj := frameJ_perform_aux_shape hshape hJ hf s hsf hst
  have hJ' := frameJ_closure_shape hshape original props (syncAll orig s)
    (by rw [syncAll_frame, hsf]; exact hj)
  exact ⟨hJ', boolPinsOn_of_pinsOn hJ'.pins⟩

/-- Productive propagation preserves Boolean pins on its unchanged prefix. -/
theorem boolPinsOn_stepNarrowSync {leaf : Assignment → Bool} {orig : List Domain}
    (bs : BranchState leaf) (d : ProductiveDeduction leaf bs)
    (h : BoolPinsOn bs.trail bs.frame) :
    BoolPinsOn (stepNarrowSync orig bs d).trail (stepNarrowSync orig bs d).frame := by
  unfold stepNarrowSync
  rw [syncSlot_frame]
  have hb1 : BoolPinsOn (narrowState bs d.frame d.literal d.reason d.learned).trail d.frame := by
    have hb : BoolPinsOn (bs.trail ++
        [{ literal := d.literal.norm, level := bs.level,
           reason := some { clause := d.reason } }]) d.frame :=
      boolPinsOn_filter h d.filtered (fun e he => List.mem_append_left _ he)
    simpa only [narrowState] using hb
  exact boolPinsOn_mono (fun e he => syncSlot_trail_sub
    (orig := orig) (bs := narrowState bs d.frame d.literal d.reason d.learned)
    (s := d.literal.atom.slot) e he) hb1

/-- The propagation closure preserves Boolean pins. -/
theorem boolPinsOn_closure {leaf : Assignment → Bool} {orig : List Domain}
    (original : List Clause) (props : List Propagator) {bs : BranchState leaf}
    (h : BoolPinsOn bs.trail bs.frame) :
    BoolPinsOn (explainedClosure orig original props bs).trail
      (explainedClosure orig original props bs).frame := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      BoolPinsOn bs.trail bs.frame →
      BoolPinsOn (explainedClosure orig original props bs).trail
        (explainedClosure orig original props bs).frame from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) h
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hb
    rw [explainedClosure]
    split
    · exact hb
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hb
    rw [explainedClosure]
    split
    · exact hb
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      exact ih _ hmass (boolPinsOn_stepNarrowSync bs d hb)

theorem boolPinsOn_perform {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hp : BoolPinsOn p.checkpoint.trail p.checkpoint.frame)
    (hr : p.perform bs orig original props = some restored) :
    BoolPinsOn restored.trail restored.frame := by
  unfold BackjumpPlan.perform at hr
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hr
  subst hres
  exact boolPinsOn_closure original props
    (boolPinsOn_syncAll (boolPinsOn_restoreNarrow hp hs))

/-- Both supported decision sorts preserve the Boolean pin invariant. -/
theorem boolPinsOn_append_value {tr tr' : List TrailEntry} {F : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain} {l : Literal} {e : TrailEntry}
    (h : BoolPinsOn tr F) (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hval : valueLiteral k v = some l) (hk : k ∉ F.order)
    (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr') (hel : e.literal = l.norm) :
    BoolPinsOn tr' (F.pin k v) := by
  cases v with
  | int i =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact boolPinsOn_append_int h hd rfl hk hsub
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      exact boolPinsOn_append_bool h hd rfl hk hsub he hel
  | _ => cases hval

end LeanFzn.Solver.UIP.LcgRunInv
