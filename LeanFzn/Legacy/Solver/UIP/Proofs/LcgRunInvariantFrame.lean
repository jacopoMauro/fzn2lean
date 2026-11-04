/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantFrame.lean
U1c (2): the frame/trail invariant `FrameJ` of an INTEGER box and its preservation by
every scheduler arm (propagate, decide, decide-skip, consume, backjump, closure).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantSync
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-! ## Frame-domain reads -/

/-- A map-`enum` singleton read is the enumeration of the slot's `getD`. -/
theorem enum_getD_of_enum_singleton {l : List Domain} {k : Nat} {v : Value}
    (h : l[k]?.map Dom.enum = some [v]) :
    Dom.enum (l.getD k Dom.empty) = [v] := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_singleton h
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]

/-- A map-`enum` head-cons read is the enumeration of the slot's `getD`. -/
theorem enum_getD_of_enum_cons {l : List Domain} {k : Nat} {v : Value}
    {vs : Domain} (h : l[k]?.map Dom.enum = some (v :: vs.enum)) :
    Dom.enum (l.getD k Dom.empty) = v :: vs.enum := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons h
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]

/-- Away from the literal's slot the filter leaves the frame domains unchanged. -/
theorem filterFrame_getD_ne {l : Literal} {f g : BranchFrame} (hg : filterFrame l f = some g)
    {s : Nat} (hs : s ≠ l.atom.slot) :
    (Frame.domains g).getD s Dom.empty = (Frame.domains f).getD s Dom.empty := by
  unfold filterFrame at hg
  split at hg
  · cases hg; rfl
  · rename_i d hd
    split at hg
    · cases hg
    · cases hg
      rw [Frame.domains, Frame.domains, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_set]
      rw [if_neg (fun h => hs h.symm)]

/-- The filtered slot holds the literal at every remaining value. -/
theorem filterFrame_holds {l : Literal} {f g : BranchFrame} (hg : filterFrame l f = some g) :
    ∀ v ∈ (Frame.domains g).getD l.atom.slot Dom.empty, l.valueHolds v = true := by
  intro v hv
  unfold filterFrame at hg
  split at hg
  · rename_i hd
    cases hg
    rw [List.getD_eq_getElem?_getD, Frame.domains, hd] at hv
    simp [Dom.enum_empty] at hv
  · rename_i d hd
    split at hg
    · cases hg
    · cases hg
      have hlt : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      have hgd : (Frame.domains
          { f with doms := f.doms.set l.atom.slot (Dom.filterLitKeep l d) }).getD
          l.atom.slot Dom.empty = Dom.filterLitKeep l d := by
        rw [Frame.domains, getD_set_self hlt]
      rw [hgd] at hv
      exact (Dom.mem_filterLitKeep_iff.mp hv).2

/-! ## The frame invariant -/

/-- Every decided slot holds its pinned singleton and carries its decision
literal on the trail. -/
def PinsOn (tr : List TrailEntry) (f : BranchFrame) : Prop :=
  ∀ k ∈ f.order, ∃ v l, f.doms[k]?.map Dom.enum = some [v] ∧ valueLiteral k v = some l ∧
    ∃ e ∈ tr, e.literal = l

structure FrameJ (orig : List Domain) (tr : List TrailEntry) (F : BranchFrame) : Prop where
  expl : ExplDoms orig tr (Frame.domains F)
  pins : PinsOn tr F
  nc : NarrowingComplete tr orig F
  fits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty
  agree : ∀ s, SlotAgree tr (Frame.domains F) s

/-- A decided slot is explained by its pin entry. -/
theorem explSlot_decided {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hpins : PinsOn tr F)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    {s : Nat} (hs : s ∈ F.order) : ExplSlot orig tr (Frame.domains F) s := by
  obtain ⟨v, l, hv, hl, e, he, hel⟩ := hpins s hs
  have hmem : v ∈ orig.getD s Dom.empty :=
    hfits s v (mem_getD_of_enum_singleton hv)
  obtain ⟨i, rfl⟩ := allInt_getD hint s _ ((DomainLike.mem_iff _ v).mp hmem)
  have hl' : negNe s i = l := by simpa [valueLiteral] using hl
  have hel' : e.literal = negNe s i := by rw [hel, ← hl']
  refine explSlot_pin he hel' ?_
  simpa [Frame.domains] using enum_getD_of_enum_singleton hv

theorem frame_ints {orig : List Domain} {F : BranchFrame} (hint : AllIntBox orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty) :
    ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k := by
  intro d hd v hv
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hd
  have hg : (Frame.domains F).getD i Dom.empty = d := by
    rw [Frame.domains, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [hdi]
  exact allInt_getD hint _ v ((DomainLike.mem_iff _ v).mp
    (hfits _ v (by rw [hg]; exact hv)))

theorem nc_narrow {orig : List Domain} {tr tr' : List TrailEntry} {l : Literal}
    {F g : BranchFrame} (hnc : NarrowingComplete tr orig F)
    (hf : filterFrame l F = some g) (hsub : ∀ e ∈ tr, e ∈ tr')
    {e : TrailEntry} (he : e ∈ tr') (hel : e.literal = l.norm) :
    NarrowingComplete tr' orig g := by
  intro i hi w horig hnot
  have hp : g.order = F.order := Frame.filterFrame_order hf
  rw [hp] at hi
  by_cases hwas : w ∈ F.doms.getD i Dom.empty
  · obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hf hwas hnot
    refine ⟨e, he, ?_, ?_⟩
    · rw [hel, norm_atom_slot, hslot]
    · rw [hel, norm_valueHolds]; exact hfalse
  · obtain ⟨e', he', h1, h2⟩ := hnc i hi w horig hwas
    exact ⟨e', hsub e' he', h1, h2⟩

/-- Filtering a decided singleton never changes the frame. -/
theorem filterFrame_eq_self_of_singleton {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) {v : Value}
    (hk : f.doms[l.atom.slot]?.map Dom.enum = some [v]) (hv : l.valueHolds v = true) :
    g = f := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_singleton hk
  have hlt := (List.getElem?_eq_some_iff.mp hd).1
  have hget : f.doms[l.atom.slot] = d := by
    rw [List.getElem?_eq_getElem hlt] at hd
    exact Option.some.inj hd
  have hfil : Dom.filterLitKeep l d = d :=
    Dom.filterLitKeep_eq_self_of_forall (fun w hw => by
      rw [hde] at hw
      rw [List.mem_singleton] at hw
      subst hw
      exact hv)
  unfold filterFrame at hg
  rw [List.getElem?_eq_getElem hlt, hget] at hg
  simp only at hg
  rw [hfil, hde] at hg
  simp only at hg
  cases hg
  have hset : f.doms.set l.atom.slot d = f.doms := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_set]
    by_cases hjk : l.atom.slot = j
    · subst hjk; rw [if_pos rfl]; simp [hlt, hget]
    · rw [if_neg hjk]
  rw [hset]

/-- Generic "append one filtered literal, then synchronise its slot" step. -/
theorem frameJ_narrow_sync {orig : List Domain} (hint : AllIntBox orig)
    {tr : List TrailEntry} {F g : BranchFrame} {l : Literal} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g) (hel : e.literal = l.norm)
    (bs : BranchState leaf) (hbs : bs.frame = g) (hbt : bs.trail = tr ++ [e]) :
    FrameJ orig (syncSlot orig bs l.atom.slot).trail g := by
  have hsub0 : ∀ x ∈ tr, x ∈ bs.trail := fun x hx => by rw [hbt]; exact List.mem_append_left _ hx
  have heN : e ∈ bs.trail := by rw [hbt]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hsubS := syncSlot_trail_sub orig bs l.atom.slot
  have hnc : NarrowingComplete bs.trail orig g := nc_narrow hJ.nc hf hsub0 heN hel
  have hfits : ∀ s v, v ∈ (Frame.domains g).getD s Dom.empty → v ∈ orig.getD s Dom.empty :=
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
        rw [Frame.domains, Frame.domains,
          enum_getD_of_enum_singleton (filterFrame_singleton hf hv),
          enum_getD_of_enum_singleton hv]
      exact ExplSlot.congr hgd.symm
        ((explSlot_decided hint hJ.pins hJ.fits hs).mono
          (fun x hx => hsubS x (hsub0 x hx)))
    · by_cases hsl : s = l.atom.slot
      · subst hsl
        have hdecg : l.atom.slot ∉ g.order := by rw [hp]; exact hs
        have := syncSlot_explains (orig := orig) (bs := bs) (s := l.atom.slot) hint
          (by rw [hbs]; exact frame_ints hint hfits)
          (by rw [hbs]; exact hnc) (by rw [hbs]; exact hfits _)
          (by rw [hbs]; exact hag _) (by rw [hbs]; exact hdecg)
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

/-! ## The split (decide) child -/

theorem split_domains_ne {F : BranchFrame} {k : Nat} {v : Value} {s : Nat}
    (hs : s ≠ k) :
    (Frame.domains (F.pin k v)).getD s Dom.empty = (Frame.domains F).getD s Dom.empty := by
  show (F.doms.set k (Dom.ofList [v])).getD s Dom.empty = F.doms.getD s Dom.empty
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  rw [if_neg (fun h => hs h.symm)]

theorem split_domains_eq {F : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    Dom.enum ((Frame.domains (F.pin k v)).getD k Dom.empty) = [v] := by
  obtain ⟨d, hd', -⟩ := exists_dom_of_enum_cons hd
  have hlt := (List.getElem?_eq_some_iff.mp hd').1
  show Dom.enum ((F.doms.set k (Dom.ofList [v])).getD k Dom.empty) = [v]
  rw [getD_set_self hlt, Dom.enum_ofList]

theorem split_domains_parent {F : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    Dom.enum ((Frame.domains F).getD k Dom.empty) = v :: vs.enum :=
  enum_getD_of_enum_cons hd

theorem frameJ_split {orig : List Domain} {k : Nat}
    (hint : ∀ w ∈ orig.getD k Dom.empty, ∃ j : Int, w = Value.int j)
    {tr tr' : List TrailEntry} {F : BranchFrame} {v : Value} {vs : Domain}
    {i : Int} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hv : v = Value.int i) (hk : k ∉ F.order)
    (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr') (hel : e.literal = negNe k i)
    (hag : ∀ s', SlotAgree tr' (Frame.domains (F.pin k v)) s') :
    FrameJ orig tr' (F.pin k v) := by
  subst v
  obtain ⟨d, hd', -⟩ := exists_dom_of_enum_cons hd
  have hlt := (List.getElem?_eq_some_iff.mp hd').1
  refine ⟨?_, ?_, ?_, ?_, hag⟩
  · intro s
    by_cases hs : s = k
    · subst s
      exact explSlot_pin he hel (split_domains_eq hd)
    · exact ExplSlot.congr (congrArg Dom.enum (split_domains_ne hs)).symm
        ((hJ.expl s).mono hsub)
  · intro s hs
    rw [BranchFrame.pin_order] at hs
    rcases List.mem_append.mp hs with hs | hs
    · have hsk : s ≠ k := fun h => hk (h ▸ hs)
      obtain ⟨v', l', hv', hl', x, hx, hxl⟩ := hJ.pins s hs
      refine ⟨v', l', ?_, hl', x, hsub x hx, hxl⟩
      rw [BranchFrame.pin_doms, getElem?_set_of_ne hsk]
      exact hv'
    · rw [List.mem_singleton] at hs
      subst s
      refine ⟨Value.int i, negNe k i, ?_, ?_, e, he, hel⟩
      · rw [BranchFrame.pin_doms, List.getElem?_set_self hlt]
        simp
      · simp [valueLiteral]
  · intro s hs w horig hnot
    have hsorder : s ∉ F.order := by
      rw [BranchFrame.pin_order] at hs
      intro hmem
      exact hs (List.mem_append.mpr (Or.inl hmem))
    by_cases hsk : s = k
    · subst s
      have hwv : w ≠ Value.int i := by
        intro hw
        apply hnot
        rw [DomainLike.mem_iff, domElems_eq_enum]
        change w ∈ Dom.enum ((Frame.domains (F.pin k (Value.int i))).getD k Dom.empty)
        rw [split_domains_eq hd, hw]
        exact List.mem_singleton_self _
      obtain ⟨j, rfl⟩ := hint w horig
      have hji : j ≠ i := fun h => hwv (by rw [h])
      refine ⟨e, he, ?_, ?_⟩
      · rw [hel]; rfl
      · rw [hel]
        simpa [Literal.valueHolds, negNe, Value.intView] using hji
    · have hdom : (Frame.domains (F.pin k (Value.int i))).getD s Dom.empty =
          (Frame.domains F).getD s Dom.empty := split_domains_ne hsk
      have hwas : w ∉ (Frame.domains F).getD s Dom.empty := by
        rw [← hdom]
        simpa [Frame.domains] using hnot
      obtain ⟨x, hx, hxs, hxf⟩ := hJ.nc s hsorder w horig hwas
      exact ⟨x, hsub x hx, hxs, hxf⟩
  · intro s w hw
    by_cases hsk : s = k
    · subst s
      have hwE : w ∈ Dom.enum ((Frame.domains (F.pin k (Value.int i))).getD k Dom.empty) :=
        (DomainLike.mem_iff _ w).mp hw
      rw [split_domains_eq hd] at hwE
      have hwv : w = Value.int i := List.mem_singleton.mp hwE
      subst w
      exact hJ.fits k (Value.int i) ((DomainLike.mem_iff _ _).mpr (by
        rw [domElems_eq_enum, split_domains_parent hd]; exact List.mem_cons_self))
    · exact hJ.fits s w (by rw [← split_domains_ne hsk]; exact hw)

/-! ## Whole-frame synchronisation -/

/-- The whole-frame explanation from the undecided-slot explanations and the pins. -/
theorem explDoms_of_remaining {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hpins : PinsOn tr F)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hrem : ∀ i, i < F.doms.length → i ∉ F.order →
      ExplSlot orig tr (Frame.domains F) i) :
    ExplDoms orig tr (Frame.domains F) := by
  intro s
  by_cases hs : s ∈ F.order
  · exact explSlot_decided hint hpins hfits hs
  · by_cases hi : s < F.doms.length
    · exact hrem s hi hs
    · refine explSlot_none ?_
      rw [List.getElem?_eq_none (by omega)]

/-- `syncAll` establishes the whole-frame invariant from its non-semantic parts. -/
theorem frameJ_syncAll {orig : List Domain} (hint : AllIntBox orig) (bs : BranchState leaf)
    (hpins : PinsOn bs.trail bs.frame)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfits : ∀ s v, v ∈ (Frame.domains bs.frame).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hag : ∀ s, SlotAgree bs.trail (Frame.domains bs.frame) s) :
    FrameJ orig (syncAll orig bs).trail bs.frame := by
  have hsub := syncAll_trail_sub orig bs
  have hpins' : PinsOn (syncAll orig bs).trail bs.frame := fun s hs => by
    obtain ⟨v, l, hv, hl, x, hx, hxl⟩ := hpins s hs
    exact ⟨v, l, hv, hl, x, hsub x hx, hxl⟩
  refine ⟨?_, hpins', nc_mono hsub hnc, hfits, fun s => syncAll_slotAgree orig bs s (hag s)⟩
  exact explDoms_of_remaining hint hpins' hfits
    (fun i hi hdec => syncAll_explains hint (frame_ints hint hfits) hfits hnc hag i hi hdec)

/-! ## The canonical (consume) base -/

theorem canonical_pinsOn (orig : List Domain) (f : BranchFrame)
    (hp : PrefixPinned f) :
    PinsOn (canonicalTrail orig f) f := by
  intro s hs
  obtain ⟨v, hv, l, hl⟩ := hp.2 s hs
  obtain ⟨j, hjlt, hjget⟩ := List.getElem_of_mem hs
  refine ⟨v, l, hv, hl, ⟨l.norm, j + 1, none⟩, ?_, valueLiteral_norm_self hl⟩
  apply List.mem_append_left
  rw [mem_canonicalPins]
  exact ⟨(s, j), mem_zipIdx_iff'.mpr ⟨hjlt, hjget⟩, v, l, hv, hl, rfl⟩

theorem canonical_agree {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ s v, v ∈ (Frame.domains f).getD s Dom.empty → v ∈ orig.getD s Dom.empty) :
    ∀ s, SlotAgree (canonicalTrail orig f) (Frame.domains f) s := by
  intro s e he hes v hv
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p, hp, v', l, hv', hl, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨hlt, hget⟩ := mem_zipIdx_iff'.mp hp
    simp only [norm_atom_slot] at hes
    have hps : p.1 = s := by rw [← valueLiteral_atom_slot hl]; exact hes
    subst hps
    have hdom : Dom.enum ((Frame.domains f).getD p.1 Dom.empty) = [v'] := by
      simpa [Frame.domains] using
        enum_getD_of_enum_singleton (l := f.doms) (k := p.1) (v := v') hv'
    have hvE : v ∈ Dom.enum ((Frame.domains f).getD p.1 Dom.empty) :=
      (DomainLike.mem_iff _ v).mp hv
    rw [hdom] at hvE
    have : v = v' := List.mem_singleton.mp hvE
    subst this
    simp only [norm_valueHolds]
    exact valueLiteral_valueHolds_self hl
  · obtain ⟨p, hp, hpord, q, hq, l, hl, hlk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
    obtain ⟨hqlt, hqe⟩ := mem_zipIdx_iff'.mp hq
    obtain ⟨hplt, hpd⟩ := mem_zipIdx_iff'.mp hp
    have hqmem : q.1 ∈ Dom.enum (orig.getD p.2 Dom.empty) := by
      rw [← hqe]; exact List.getElem_mem hqlt
    have hw : q.1 ∈ orig.getD p.2 Dom.empty := by
      rw [DomainLike.mem_iff, domElems_eq_enum]; exact hqmem
    have hs : p.2 = s := by
      simp only [literal_negate_norm_atom_slot] at hes
      rw [← valueLiteral_atom_slot hl]; exact hes
    rw [← hs] at hv
    have hdom : (Frame.domains f).getD p.2 Dom.empty = p.1 := by
      rw [Frame.domains, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hplt]
      exact hpd
    rw [hdom] at hv
    refine falsifier_holds_of_not_kept (j := p.2) hshape hw hl hlk ?_ hv
    intro v' hv'
    exact hfit _ _ (by rw [hdom]; exact hv')

theorem frameJ_resume {orig : List Domain} (hint : AllIntBox orig) (bs : BranchState leaf)
    {f : BranchFrame} (hb : PendingBacked orig f) :
    FrameJ orig (resumePending orig bs f).trail f := by
  have hfits : ∀ s v, v ∈ (Frame.domains f).getD s Dom.empty → v ∈ orig.getD s Dom.empty := hb.fit
  exact frameJ_syncAll (bs := resumePendingBase orig bs f) hint (canonical_pinsOn orig f hb.pins)
    (narrowing_complete_canonical hb.shape hb.full_len) hfits (canonical_agree hb.shape hfits)

/-- The non-semantic parts after (possibly) appending one filtered literal:
`tr'` extends `tr`, contains an entry `e` for the filtering literal, and holds
nothing else. -/
theorem narrow_pre' {orig : List Domain} {tr : List TrailEntry} {F g : BranchFrame} {l : Literal}
    {e : TrailEntry} (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g)
    (hel : e.literal = l.norm) {tr' : List TrailEntry}
    (hsub0 : ∀ x ∈ tr, x ∈ tr') (heN : e ∈ tr') (hnew : ∀ x ∈ tr', x ∈ tr ∨ x = e) :
    PinsOn tr' g ∧ NarrowingComplete tr' orig g ∧
    (∀ s v, v ∈ (Frame.domains g).getD s Dom.empty → v ∈ orig.getD s Dom.empty) ∧
    (∀ s, SlotAgree tr' (Frame.domains g) s) := by
  have hp : g.order = F.order := Frame.filterFrame_order hf
  refine ⟨?_, nc_narrow hJ.nc hf hsub0 heN hel, ?_, ?_⟩
  · intro s hs
    rw [hp] at hs
    obtain ⟨v, l', hv, hl', x, hx, hxl⟩ := hJ.pins s hs
    exact ⟨v, l', filterFrame_singleton hf hv, hl', x, hsub0 x hx, hxl⟩
  · exact fun s v hv => hJ.fits s v (Frame.domains_subsets hf s v hv)
  · intro s' x hx hxs v hv
    rcases hnew x hx with hx | hx
    · exact hJ.agree s' x hx hxs v (Frame.domains_subsets hf s' v hv)
    · subst hx
      rw [hel, norm_atom_slot] at hxs
      rw [hel, norm_valueHolds]
      rw [← hxs] at hv
      exact filterFrame_holds hf v hv

/-- The non-semantic parts after appending one filtered literal. -/
theorem narrow_pre {orig : List Domain} {tr : List TrailEntry} {F g : BranchFrame} {l : Literal}
    {e : TrailEntry} (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g)
    (hel : e.literal = l.norm) {tr' : List TrailEntry} (htr : tr' = tr ++ [e]) :
    PinsOn tr' g ∧ NarrowingComplete tr' orig g ∧
    (∀ s v, v ∈ (Frame.domains g).getD s Dom.empty → v ∈ orig.getD s Dom.empty) ∧
    (∀ s, SlotAgree tr' (Frame.domains g) s) := by
  subst htr
  refine narrow_pre' hJ hf hel (fun x hx => List.mem_append_left _ hx)
    (List.mem_append_right _ (List.mem_singleton_self _)) (fun x hx => ?_)
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_singleton.mp hx)

theorem frameJ_narrow_syncAll' {orig : List Domain} (hint : AllIntBox orig)
    {tr : List TrailEntry} {F g : BranchFrame} {l : Literal} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g) (hel : e.literal = l.norm)
    (bs : BranchState leaf) (hbs : bs.frame = g)
    (hsub0 : ∀ x ∈ tr, x ∈ bs.trail) (heN : e ∈ bs.trail)
    (hnew : ∀ x ∈ bs.trail, x ∈ tr ∨ x = e) :
    FrameJ orig (syncAll orig bs).trail g := by
  obtain ⟨h1, h2, h3, h4⟩ := narrow_pre' hJ hf hel hsub0 heN hnew
  have := frameJ_syncAll hint bs (by rw [hbs]; exact h1)
    (by rw [hbs]; exact h2) (by rw [hbs]; exact h3) (by rw [hbs]; exact h4)
  rw [hbs] at this
  exact this

theorem frameJ_narrow_syncAll {orig : List Domain} (hint : AllIntBox orig)
    {tr : List TrailEntry} {F g : BranchFrame} {l : Literal} {e : TrailEntry}
    (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g) (hel : e.literal = l.norm)
    (bs : BranchState leaf) (hbs : bs.frame = g) (hbt : bs.trail = tr ++ [e]) :
    FrameJ orig (syncAll orig bs).trail g := by
  refine frameJ_narrow_syncAll' hint hJ hf hel bs hbs
    (fun x hx => by rw [hbt]; exact List.mem_append_left _ hx)
    (by rw [hbt]; exact List.mem_append_right _ (List.mem_singleton_self _))
    (fun x hx => ?_)
  rw [hbt] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_singleton.mp hx)

theorem frameJ_stepNarrowSync {orig : List Domain} (hint : AllIntBox orig)
    (bs : BranchState leaf) (d : ProductiveDeduction leaf bs)
    (hJ : FrameJ orig bs.trail bs.frame) :
    FrameJ orig (stepNarrowSync orig bs d).trail (stepNarrowSync orig bs d).frame := by
  rw [stepNarrowSync_frame]
  exact frameJ_narrow_sync hint hJ d.filtered
    (e := ⟨d.literal.norm, bs.level, some { clause := d.reason }⟩) rfl
    (narrowState bs d.frame d.literal d.reason d.learned) rfl rfl

theorem frameJ_closure {orig : List Domain} (hint : AllIntBox orig) (original : List Clause)
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
      exact ih _ hmass (frameJ_stepNarrowSync hint bs d hJ)

theorem restoreNarrow_shape {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    ∃ g, filterFrame p.asserting p.checkpoint.frame = some g ∧ s.frame = g ∧
      s.trail = p.checkpoint.trail ++ p.assertExtra := by
  unfold BackjumpPlan.restoreNarrow at h
  cases hf : filterFrame p.asserting p.checkpoint.frame with
  | none => rw [hf] at h; cases h
  | some g =>
      rw [hf] at h
      cases h
      exact ⟨g, rfl, rfl, rfl⟩

theorem frameJ_perform_aux {orig : List Domain} (hint : AllIntBox orig)
    {p : BackjumpPlan leaf} {g : BranchFrame}
    (hJcp : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hf : filterFrame p.asserting p.checkpoint.frame = some g)
    (s : BranchState leaf) (hsf : s.frame = g)
    (hst : s.trail = p.checkpoint.trail ++ p.assertExtra) :
    FrameJ orig (syncAll orig s).trail g := by
  rcases p.assertExtra_cases with hx | hx
  · -- guard: the asserting literal is already on the restored trail
    have hx' : p.assertExtra = [] := hx
    obtain ⟨e0, he0, hel0⟩ : ∃ e ∈ p.checkpoint.trail, e.literal = p.asserting.norm := by
      refine Classical.byContradiction fun hno => ?_
      exact BackjumpPlan.assertExtra_ne_nil_of_fresh p
        (fun e he h => hno ⟨e, he, h⟩) hx'
    refine frameJ_narrow_syncAll' hint hJcp hf hel0 s hsf (fun x hx => ?_) ?_
      (fun x hx => Or.inl ?_)
    · rw [hst, hx']; simpa using hx
    · rw [hst, hx']; simpa using he0
    · rw [hst, hx'] at hx; simpa using hx
  · exact frameJ_narrow_syncAll hint hJcp hf (e := ⟨p.asserting.norm, p.target,
      some { clause := p.learned }⟩) rfl s hsf (by rw [hst, hx]; rfl)

theorem frameJ_perform {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hint : AllIntBox orig) {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hJcp : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hperf : p.perform bs orig original props = some restored) :
    FrameJ orig restored.trail restored.frame := by
  unfold BackjumpPlan.perform at hperf
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hperf
  subst hres
  obtain ⟨g, hf, hsf, hst⟩ := restoreNarrow_shape hs
  have h1 := frameJ_perform_aux hint hJcp hf s hsf hst
  have h2 := frameJ_closure hint original props (syncAll orig s)
    (by rw [syncAll_frame, hsf]; exact h1)
  exact h2

/-- Child domains are contained in the parent's. -/
theorem split_domains_sub {F : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) (s : Nat) :
    ∀ x ∈ (Frame.domains (F.pin k v)).getD s Dom.empty, x ∈ (Frame.domains F).getD s Dom.empty := by
  intro x hx
  by_cases hs : s = k
  · subst s
    have hxE : x ∈ Dom.enum ((Frame.domains (F.pin k v)).getD k Dom.empty) :=
      (DomainLike.mem_iff _ x).mp hx
    rw [split_domains_eq hd] at hxE
    have hxv : x = v := List.mem_singleton.mp hxE
    rw [hxv]
    exact (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum, split_domains_parent hd]; exact List.mem_cons_self)
  · rw [split_domains_ne hs] at hx; exact hx

/-- The decide child (fresh pin): agreement of the extended trail. -/
theorem split_agree_push {tr : List TrailEntry} {F : BranchFrame} {k : Nat} {v : Value}
    {vs : Domain} {i : Int} {lvl : Nat}
    (hag : ∀ s, SlotAgree tr (Frame.domains F) s)
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hv : v = Value.int i) :
    ∀ s, SlotAgree (tr ++ [⟨negNe k i, lvl, none⟩])
      (Frame.domains (F.pin k v)) s := by
  subst hv
  intro s x hx hxs w hw
  rcases List.mem_append.mp hx with hx | hx
  · exact hag s x hx hxs w (split_domains_sub hd s w hw)
  · have : x = ⟨negNe k i, lvl, none⟩ := List.mem_singleton.mp hx
    subst this
    have hs : s = k := by simpa [negNe, Atom.slot] using hxs.symm
    subst s
    have hwE : w ∈ Dom.enum ((Frame.domains (F.pin k (Value.int i))).getD k Dom.empty) :=
      (DomainLike.mem_iff _ w).mp hw
    rw [split_domains_eq hd] at hwE
    have hwv : w = Value.int i := List.mem_singleton.mp hwE
    rw [hwv]
    simp [Literal.valueHolds, negNe, Value.intView]

theorem split_agree_skip {tr : List TrailEntry} {F : BranchFrame} {k : Nat} {v : Value}
    {vs : Domain}
    (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hag : ∀ s, SlotAgree tr (Frame.domains F) s) :
    ∀ s, SlotAgree tr (Frame.domains (F.pin k v)) s :=
  fun s x hx hxs w hw => hag s x hx hxs w (split_domains_sub hd s w hw)

/-! ## Frame shape: length and duplicate-freeness -/

/-- The frame spans the box and its remaining domains are duplicate free. -/
def FrameShape (orig : List Domain) (F : BranchFrame) : Prop :=
  (Frame.domains F).length = orig.length ∧ ∀ d ∈ F.1, (Dom.enum d).Nodup

theorem filterSlots_nodup (l : Literal) :
    ∀ (slots : List Domain) (off : Nat), (∀ d ∈ slots, (Dom.enum d).Nodup) →
      ∀ d ∈ filterSlots l off slots, (Dom.enum d).Nodup := by
  intro slots
  induction slots with
  | nil => intro off _ d hd; cases hd
  | cons d0 rest ih =>
      intro off h d hd
      simp only [filterSlots, List.mem_cons] at hd
      rcases hd with rfl | hd
      · split
        · rw [Dom.enum_filterLitKeep]
          exact (h d0 List.mem_cons_self).filter _
        · exact h d0 List.mem_cons_self
      · exact ih (off + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx)) d hd

theorem frameShape_filter {orig : List Domain} {l : Literal} {F g : BranchFrame}
    (hf : filterFrame l F = some g) (h : FrameShape orig F) : FrameShape orig g := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    rw [fullDomains_length] at h1 ⊢
    rw [filterFrame_rem_length hf]
    exact h1
  · unfold filterFrame at hf
    split at hf
    · cases hf; exact h.2
    · rename_i d hd
      split at hf
      · cases hf
      · cases hf
        intro e he
        rcases List.mem_or_eq_of_mem_set he with hmem | heq
        · exact h.2 e hmem
        · subst heq
          rw [Dom.enum_filterLitKeep]
          exact (h.2 d (List.mem_of_getElem? hd)).filter _

theorem frameShape_split {orig : List Domain} {F : BranchFrame} {k : Nat} {v : Value}
    {vs : Domain} (h : FrameShape orig F) (hd : F.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    FrameShape orig (F.pin k v) ∧ (Dom.enum vs).Nodup := by
  obtain ⟨d, hd', hde⟩ := exists_dom_of_enum_cons hd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 := h.1
    rw [fullDomains_length] at h1 ⊢
    rw [BranchFrame.pin_doms, List.length_set]
    exact h1
  · intro d' hd'
    rw [BranchFrame.pin_doms] at hd'
    rcases List.mem_or_eq_of_mem_set hd' with hmem | heq
    · exact h.2 d' hmem
    · subst heq
      rw [Dom.enum_ofList]
      simp
  · have hn := h.2 d (List.mem_of_getElem? hd')
    rw [hde] at hn
    exact (List.nodup_cons.mp hn).2

theorem frameShape_closure (orig : List Domain) (original : List Clause) (props : List Propagator) :
    ∀ (bs : BranchState leaf), FrameShape orig bs.frame →
      FrameShape orig (explainedClosure orig original props bs).frame := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      FrameShape orig bs.frame → FrameShape orig (explainedClosure orig original props bs).frame from
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
      refine ih _ hmass ?_
      rw [stepNarrowSync_frame]
      exact frameShape_filter d.filtered hJ

theorem frameShape_perform {orig : List Domain} {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hcp : FrameShape orig p.checkpoint.frame)
    (hperf : p.perform bs orig original props = some restored) :
    FrameShape orig restored.frame := by
  unfold BackjumpPlan.perform at hperf
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hperf
  subst hres
  obtain ⟨g, hf, hsf, -⟩ := restoreNarrow_shape hs
  have h1 : FrameShape orig g := frameShape_filter hf hcp
  have := frameShape_closure orig original props (syncAll orig s)
    (by rw [syncAll_frame, hsf]; exact h1)
  exact this

end LeanFzn.Solver.UIP.LcgRunInv
