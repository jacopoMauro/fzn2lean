/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantFrame.lean
U1c (2): the frame/trail invariant `FrameJ` of an INTEGER box and its preservation by
every scheduler arm (propagate, decide, decide-skip, consume, backjump, closure).
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantSync
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-! ## Frame-domain reads -/

theorem domains_getD_rem (f : BranchFrame) {s : Nat} (hle : f.2.length ≤ s) :
    (Frame.domains f).getD s [] = f.1.getD (s - f.2.length) [] := by
  obtain ⟨i, rfl⟩ : ∃ i, s = f.2.length + i := ⟨s - f.2.length, by omega⟩
  have h1 : f.2.length + i - f.2.length = i := by omega
  rw [h1]
  have := fullDomains_remaining f i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  show ((fullDomains f)[f.2.length + i]?).getD [] = _
  rw [this]

theorem domains_getD_pre (f : BranchFrame) {s : Nat} (hs : s < f.2.length) :
    (Frame.domains f).getD s [] = [f.2[s]] := by
  rw [List.getD_eq_getElem?_getD]
  show ((fullDomains f)[s]?).getD [] = _
  rw [fullDomains_prefix f s hs]; rfl

/-! ## The filter -/

theorem filterSlots_getD (l : Literal) :
    ∀ (slots : List Domain) (off i : Nat),
      (filterSlots l off slots).getD i [] =
        if off + i = l.atom.slot then (slots.getD i []).filter l.valueHolds
        else slots.getD i [] := by
  intro slots
  induction slots with
  | nil => intro off i; simp [filterSlots]
  | cons d rest ih =>
      intro off i
      cases i with
      | zero => simp [filterSlots]
      | succ i =>
          simp only [filterSlots, List.getD_cons_succ]
          rw [ih (off + 1) i]
          have : off + 1 + i = off + (i + 1) := by omega
          rw [this]

/-- Away from the literal's slot the filter leaves the frame domains unchanged. -/
theorem filterFrame_getD_ne {l : Literal} {f g : BranchFrame} (hg : filterFrame l f = some g)
    {s : Nat} (hs : s ≠ l.atom.slot) : (Frame.domains g).getD s [] = (Frame.domains f).getD s [] := by
  unfold filterFrame at hg
  by_cases hlt : l.atom.slot < f.2.length
  · rw [if_pos hlt] at hg
    split at hg
    · cases hg; rfl
    · cases hg
  · rw [if_neg hlt] at hg
    cases hg
    by_cases hle : f.2.length ≤ s
    · have h1 := domains_getD_rem (filterSlots l f.2.length f.1, f.2) (s := s) hle
      have h2 := domains_getD_rem f hle
      rw [h1, h2]
      show (filterSlots l f.2.length f.1).getD (s - f.2.length) [] = _
      rw [filterSlots_getD, if_neg (by omega)]
    · have hs' : s < f.2.length := by omega
      have h1 := domains_getD_pre (filterSlots l f.2.length f.1, f.2) (s := s) hs'
      have h2 := domains_getD_pre f hs'
      rw [h1, h2]

/-- The filtered slot holds the literal at every remaining value. -/
theorem filterFrame_holds {l : Literal} {f g : BranchFrame} (hg : filterFrame l f = some g) :
    ∀ v ∈ (Frame.domains g).getD l.atom.slot [], l.valueHolds v = true := by
  intro v hv
  unfold filterFrame at hg
  by_cases hlt : l.atom.slot < f.2.length
  · rw [if_pos hlt] at hg
    split at hg
    · rename_i hev
      cases hg
      rw [domains_getD_pre _ hlt] at hv
      have hv' : v = f.2[l.atom.slot] := List.mem_singleton.mp hv
      subst hv'
      have heval : l.eval f.2 = some true := by simpa using hev
      exact (valueHolds_read (l := l) (a := f.2) (v := f.2[l.atom.slot])
        (List.getElem?_eq_getElem hlt)).mpr heval
    · cases hg
  · rw [if_neg hlt] at hg
    cases hg
    have hle : f.2.length ≤ l.atom.slot := by omega
    have h1 := domains_getD_rem (filterSlots l f.2.length f.1, f.2) (s := l.atom.slot) hle
    rw [h1] at hv
    have h3 : (filterSlots l f.2.length f.1).getD (l.atom.slot - f.2.length) [] =
        (f.1.getD (l.atom.slot - f.2.length) []).filter l.valueHolds := by
      rw [filterSlots_getD, if_pos (by omega)]
    have hv2 : v ∈ (f.1.getD (l.atom.slot - f.2.length) []).filter l.valueHolds := by
      rw [← h3]; exact hv
    simpa using (List.mem_filter.mp hv2).2

/-! ## The frame invariant -/

/-- Every integer-valued prefix position carries its pin `s = k` on the trail. -/
def PinsOn (tr : List TrailEntry) (pre : List Value) : Prop :=
  ∀ s k, pre[s]? = some (Value.int k) → ∃ e ∈ tr, e.literal = negNe s k

structure FrameJ (orig : List Domain) (tr : List TrailEntry) (F : BranchFrame) : Prop where
  expl : ExplDoms orig tr (Frame.domains F)
  pins : PinsOn tr F.2
  nc : NarrowingComplete tr orig F
  fits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []
  agree : ∀ s, SlotAgree tr (Frame.domains F) s

theorem frame_ints {orig : List Domain} {F : BranchFrame} (hint : AllIntBox orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []) :
    ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k := by
  intro d hd v hv
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hd
  have hg : (Frame.domains F).getD (F.2.length + i) [] = d := by
    rw [domains_getD_rem F (by omega)]
    have : F.2.length + i - F.2.length = i := by omega
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [hdi]
  exact allInt_getD hint _ v (hfits _ v (by rw [hg]; exact hv))

theorem nc_narrow {orig : List Domain} {tr tr' : List TrailEntry} {l : Literal}
    {F g : BranchFrame} (hnc : NarrowingComplete tr orig F)
    (hf : filterFrame l F = some g) (hsub : ∀ e ∈ tr, e ∈ tr')
    {e : TrailEntry} (he : e ∈ tr') (hel : e.literal = l.norm) :
    NarrowingComplete tr' orig g := by
  intro i w horig hnot
  have hp : g.2 = F.2 := filterFrame_prefix hf
  rw [hp] at horig ⊢
  by_cases hwas : w ∈ F.1.getD i []
  · obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hf hwas hnot
    refine ⟨e, he, ?_, ?_⟩
    · rw [hel, norm_atom_slot, hslot]
    · rw [hel, norm_valueHolds]; exact hfalse
  · obtain ⟨e', he', h1, h2⟩ := hnc i w horig hwas
    exact ⟨e', hsub e' he', h1, h2⟩

theorem filterFrame_pre_eq {l : Literal} {f g : BranchFrame} (hg : filterFrame l f = some g)
    (hlt : l.atom.slot < f.2.length) : g = f := by
  unfold filterFrame at hg
  rw [if_pos hlt] at hg
  split at hg
  · exact (Option.some.inj hg).symm
  · cases hg

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
        have := syncSlot_explains (orig := orig) (bs := bs) (s := l.atom.slot) hint
          (by rw [hbs]; exact frame_ints hint hfits) (by rw [hbs]; exact hle)
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

theorem split_domains_ne (v : Value) (vs : Domain) (doms : List Domain) (pre : List Value)
    {s : Nat} (hs : s ≠ pre.length) :
    (Frame.domains (doms, pre ++ [v])).getD s [] =
      (Frame.domains (((v :: vs) :: doms), pre)).getD s [] := by
  by_cases hlt : s < pre.length
  · have h1 := domains_getD_pre (doms, pre ++ [v]) (s := s) (by simp; omega)
    have h2 := domains_getD_pre (((v :: vs) :: doms), pre) (s := s) hlt
    rw [h1, h2]
    simp [List.getElem_append_left hlt]
  · have hgt : pre.length < s := by omega
    have h1 := domains_getD_rem (doms, pre ++ [v]) (s := s) (by simp; omega)
    have h2 := domains_getD_rem (((v :: vs) :: doms), pre) (s := s) (by simp; omega)
    rw [h1, h2]
    show doms.getD (s - (pre ++ [v]).length) [] = ((v :: vs) :: doms).getD (s - pre.length) []
    have : s - pre.length = (s - (pre ++ [v]).length) + 1 := by simp; omega
    rw [this]; simp

theorem split_domains_eq (v : Value) (vs : Domain) (doms : List Domain) (pre : List Value) :
    (Frame.domains (doms, pre ++ [v])).getD pre.length [] = [v] := by
  have h1 := domains_getD_pre (doms, pre ++ [v]) (s := pre.length) (by simp)
  rw [h1]; simp

theorem split_domains_parent (v : Value) (vs : Domain) (doms : List Domain) (pre : List Value) :
    (Frame.domains (((v :: vs) :: doms), pre)).getD pre.length [] = v :: vs := by
  have h1 := domains_getD_rem (((v :: vs) :: doms), pre) (s := pre.length) (by simp)
  rw [h1]; simp

theorem frameJ_split {orig : List Domain} {tr tr' : List TrailEntry} {v : Value} {vs : Domain}
    {doms : List Domain} {pre : List Value} {k : Int} {e : TrailEntry}
    (hJ : FrameJ orig tr (((v :: vs) :: doms), pre)) (hv : v = Value.int k)
    (hsub : ∀ x ∈ tr, x ∈ tr') (he : e ∈ tr') (hel : e.literal = negNe pre.length k)
    (hag : ∀ s', SlotAgree tr' (Frame.domains (doms, pre ++ [v])) s') :
    FrameJ orig tr' (doms, pre ++ [v]) := by
  subst hv
  refine ⟨?_, ?_, ?_, ?_, hag⟩
  · intro s
    by_cases hs : s = pre.length
    · subst hs
      exact explSlot_pin he hel (split_domains_eq _ vs doms pre)
    · exact ExplSlot.congr (split_domains_ne _ vs doms pre hs).symm ((hJ.expl s).mono hsub)
  · intro s k' hk
    by_cases hlt : s < pre.length
    · have : pre[s]? = some (Value.int k') := by
        rw [List.getElem?_append_left hlt] at hk; exact hk
      obtain ⟨x, hx, hxl⟩ := hJ.pins s k' this
      exact ⟨x, hsub x hx, hxl⟩
    · have hs : s = pre.length := by
        by_cases h2 : s = pre.length
        · exact h2
        · exfalso
          have : (pre ++ [Value.int k])[s]? = none := by
            apply List.getElem?_eq_none; simp; omega
          rw [this] at hk; cases hk
      subst hs
      have : (pre ++ [Value.int k])[pre.length]? = some (Value.int k) := by simp
      rw [this] at hk
      have hkk : k = k' := by simpa using hk
      subst hkk
      exact ⟨e, he, hel⟩
  · intro i w horig hnot
    have h1 : w ∈ orig.getD (pre.length + (i + 1)) [] := by
      have : (pre ++ [Value.int k]).length + i = pre.length + (i + 1) := by simp; omega
      rw [← this]; exact horig
    obtain ⟨x, hx, hxs, hxf⟩ := hJ.nc (i + 1) w h1 (by simpa using hnot)
    refine ⟨x, hsub x hx, ?_, hxf⟩
    show x.literal.atom.slot = (pre ++ [Value.int k]).length + i
    rw [hxs]; simp; omega
  · intro s w hw
    by_cases hs : s = pre.length
    · subst hs
      rw [split_domains_eq _ vs doms pre] at hw
      have : w = Value.int k := List.mem_singleton.mp hw
      subst this
      apply hJ.fits pre.length
      rw [split_domains_parent]; exact List.mem_cons_self
    · apply hJ.fits s
      rw [← split_domains_ne (Value.int k) vs doms pre hs]; exact hw

/-! ## Whole-frame synchronisation -/

theorem explSlot_prefix {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hpins : PinsOn tr F.2)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s [])
    {s : Nat} (hs : s < F.2.length) : ExplSlot orig tr (Frame.domains F) s := by
  have hd := domains_getD_pre F hs
  have hmem : F.2[s] ∈ orig.getD s [] := hfits s _ (by rw [hd]; exact List.mem_cons_self)
  obtain ⟨k, hk⟩ := allInt_getD hint s _ hmem
  obtain ⟨x, hx, hxl⟩ := hpins s k (by rw [List.getElem?_eq_getElem hs, hk])
  exact explSlot_pin hx hxl (by rw [hd, hk])

/-- The whole-frame explanation from the remaining-slot explanations and the pins. -/
theorem explDoms_of_remaining {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hpins : PinsOn tr F.2)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s [])
    (hrem : ∀ i, i < F.1.length → ExplSlot orig tr (Frame.domains F) (F.2.length + i)) :
    ExplDoms orig tr (Frame.domains F) := by
  intro s
  by_cases hs : s < F.2.length
  · exact explSlot_prefix hint hpins hfits hs
  · have hle : F.2.length ≤ s := by omega
    obtain ⟨i, rfl⟩ : ∃ i, s = F.2.length + i := ⟨s - F.2.length, by omega⟩
    by_cases hi : i < F.1.length
    · exact hrem i hi
    · refine explSlot_none hle ?_
      have : F.2.length + i - F.2.length = i := by omega
      rw [this]
      exact List.getElem?_eq_none (by omega)

/-- `syncAll` establishes the whole-frame invariant from its non-semantic parts. -/
theorem frameJ_syncAll {orig : List Domain} (hint : AllIntBox orig) (bs : BranchState leaf)
    (hpins : PinsOn bs.trail bs.frame.2)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfits : ∀ s v, v ∈ (Frame.domains bs.frame).getD s [] → v ∈ orig.getD s [])
    (hag : ∀ s, SlotAgree bs.trail (Frame.domains bs.frame) s) :
    FrameJ orig (syncAll orig bs).trail bs.frame := by
  have hsub := syncAll_trail_sub orig bs
  have hpins' : PinsOn (syncAll orig bs).trail bs.frame.2 := fun s k hk => by
    obtain ⟨x, hx, hxl⟩ := hpins s k hk
    exact ⟨x, hsub x hx, hxl⟩
  refine ⟨?_, hpins', nc_mono hsub hnc, hfits, fun s => syncAll_slotAgree orig bs s (hag s)⟩
  exact explDoms_of_remaining hint hpins' hfits
    (fun i hi => syncAll_explains hint (frame_ints hint hfits) hfits hnc hag i hi)

/-! ## The canonical (consume) base -/

theorem canonical_pinsOn (orig : List Domain) (f : BranchFrame) :
    PinsOn (canonicalTrail orig f) f.2 := by
  intro s k hk
  have hs : s < f.2.length := (List.getElem?_eq_some_iff.mp hk).1
  have hval : f.2[s] = Value.int k := by
    rw [List.getElem?_eq_getElem hs] at hk; exact Option.some.inj hk
  refine ⟨⟨(negNe s k).norm, s + 1, none⟩, ?_, rfl⟩
  apply List.mem_append_left
  rw [mem_canonicalPins]
  exact ⟨(Value.int k, s), mem_zipIdx_iff'.mpr ⟨hs, hval⟩, negNe s k, rfl, rfl⟩

theorem canonical_agree {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ s v, v ∈ (Frame.domains f).getD s [] → v ∈ orig.getD s []) :
    ∀ s, SlotAgree (canonicalTrail orig f) (Frame.domains f) s := by
  intro s e he hes v hv
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
    simp only [norm_atom_slot] at hes
    have hps : p.2 = s := by rw [← valueLiteral_atom_slot hl]; exact hes
    subst hps
    rw [domains_getD_pre f hlt] at hv
    have : v = f.2[p.2] := List.mem_singleton.mp hv
    subst this
    simp only [hpre, norm_valueHolds]
    exact valueLiteral_valueHolds_self hl
  · obtain ⟨p, hp, q, hq, l, hl, hlk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
    obtain ⟨hqlt, hqe⟩ := mem_zipIdx_iff'.mp hq
    obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
    have hw : q.1 ∈ orig.getD (f.2.length + p.2) [] := by
      rw [← hqe]; exact List.getElem_mem hqlt
    have hs : f.2.length + p.2 = s := by
      simp only [literal_negate_norm_atom_slot] at hes
      rw [← valueLiteral_atom_slot hl]; exact hes
    subst hs
    have hgetD : f.1.getD p.2 [] = p.1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact hpre
    have hdom : (Frame.domains f).getD (f.2.length + p.2) [] = p.1 := by
      rw [domains_getD_rem f (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hgetD]
    rw [hdom] at hv
    refine falsifier_holds_of_not_kept (j := f.2.length + p.2) hshape hw hl hlk ?_ hv
    intro v' hv'
    exact hfit _ _ (by rw [hdom]; exact hv')

theorem frameJ_resume {orig : List Domain} (hint : AllIntBox orig) (bs : BranchState leaf)
    {f : BranchFrame} (hb : PendingBacked orig f) :
    FrameJ orig (resumePending orig bs f).trail f := by
  have hfits : ∀ s v, v ∈ (Frame.domains f).getD s [] → v ∈ orig.getD s [] := hb.fit
  exact frameJ_syncAll (bs := resumePendingBase orig bs f) hint (canonical_pinsOn orig f)
    (narrowing_complete_canonical hb.shape hb.full_len) hfits (canonical_agree hb.shape hfits)

/-- The non-semantic parts after (possibly) appending one filtered literal:
`tr'` extends `tr`, contains an entry `e` for the filtering literal, and holds
nothing else. -/
theorem narrow_pre' {orig : List Domain} {tr : List TrailEntry} {F g : BranchFrame} {l : Literal}
    {e : TrailEntry} (hJ : FrameJ orig tr F) (hf : filterFrame l F = some g)
    (hel : e.literal = l.norm) {tr' : List TrailEntry}
    (hsub0 : ∀ x ∈ tr, x ∈ tr') (heN : e ∈ tr') (hnew : ∀ x ∈ tr', x ∈ tr ∨ x = e) :
    PinsOn tr' g.2 ∧ NarrowingComplete tr' orig g ∧
    (∀ s v, v ∈ (Frame.domains g).getD s [] → v ∈ orig.getD s []) ∧
    (∀ s, SlotAgree tr' (Frame.domains g) s) := by
  have hp : g.2 = F.2 := filterFrame_prefix hf
  refine ⟨?_, nc_narrow hJ.nc hf hsub0 heN hel, ?_, ?_⟩
  · intro s k hk
    rw [hp] at hk
    obtain ⟨x, hx, hxl⟩ := hJ.pins s k hk
    exact ⟨x, hsub0 x hx, hxl⟩
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
    PinsOn tr' g.2 ∧ NarrowingComplete tr' orig g ∧
    (∀ s v, v ∈ (Frame.domains g).getD s [] → v ∈ orig.getD s []) ∧
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
theorem split_domains_sub (v : Value) (vs : Domain) (doms : List Domain) (pre : List Value)
    (s : Nat) : ∀ x ∈ (Frame.domains (doms, pre ++ [v])).getD s [],
      x ∈ (Frame.domains (((v :: vs) :: doms), pre)).getD s [] := by
  intro x hx
  by_cases hs : s = pre.length
  · subst hs
    rw [split_domains_eq _ vs doms pre] at hx
    rw [split_domains_parent]
    have : x = v := List.mem_singleton.mp hx
    subst this; exact List.mem_cons_self
  · rw [split_domains_ne _ vs doms pre hs] at hx; exact hx

/-- The decide child (fresh pin): agreement of the extended trail. -/
theorem split_agree_push {tr : List TrailEntry} {v : Value} {vs : Domain} {doms : List Domain}
    {pre : List Value} {k : Int} {lvl : Nat}
    (hag : ∀ s, SlotAgree tr (Frame.domains (((v :: vs) :: doms), pre)) s)
    (hv : v = Value.int k) :
    ∀ s, SlotAgree (tr ++ [⟨negNe pre.length k, lvl, none⟩])
      (Frame.domains (doms, pre ++ [v])) s := by
  subst hv
  intro s x hx hxs w hw
  rcases List.mem_append.mp hx with hx | hx
  · exact hag s x hx hxs w (split_domains_sub _ vs doms pre s w hw)
  · have : x = ⟨negNe pre.length k, lvl, none⟩ := List.mem_singleton.mp hx
    subst this
    have hs : s = pre.length := by simpa [negNe, Atom.slot] using hxs.symm
    subst hs
    rw [split_domains_eq _ vs doms pre] at hw
    have : w = Value.int k := List.mem_singleton.mp hw
    subst this
    simp [Literal.valueHolds, negNe, Value.intView]

theorem split_agree_skip {tr : List TrailEntry} {v : Value} {vs : Domain} {doms : List Domain}
    {pre : List Value}
    (hag : ∀ s, SlotAgree tr (Frame.domains (((v :: vs) :: doms), pre)) s) :
    ∀ s, SlotAgree tr (Frame.domains (doms, pre ++ [v])) s :=
  fun s x hx hxs w hw => hag s x hx hxs w (split_domains_sub v vs doms pre s w hw)

/-! ## Frame shape: length and duplicate-freeness -/

/-- The frame spans the box and its remaining domains are duplicate free. -/
def FrameShape (orig : List Domain) (F : BranchFrame) : Prop :=
  (Frame.domains F).length = orig.length ∧ ∀ d ∈ F.1, d.Nodup

theorem filterSlots_nodup (l : Literal) :
    ∀ (slots : List Domain) (off : Nat), (∀ d ∈ slots, d.Nodup) →
      ∀ d ∈ filterSlots l off slots, d.Nodup := by
  intro slots
  induction slots with
  | nil => intro off _ d hd; cases hd
  | cons d0 rest ih =>
      intro off h d hd
      simp only [filterSlots, List.mem_cons] at hd
      rcases hd with rfl | hd
      · split
        · exact (h d0 List.mem_cons_self).filter _
        · exact h d0 List.mem_cons_self
      · exact ih (off + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx)) d hd

theorem frameShape_filter {orig : List Domain} {l : Literal} {F g : BranchFrame}
    (hf : filterFrame l F = some g) (h : FrameShape orig F) : FrameShape orig g := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    rw [fullDomains_length] at h1 ⊢
    rw [filterFrame_prefix hf, filterFrame_rem_length hf]; exact h1
  · unfold filterFrame at hf
    by_cases hlt : l.atom.slot < F.2.length
    · rw [if_pos hlt] at hf
      split at hf
      · cases hf; exact h.2
      · cases hf
    · rw [if_neg hlt] at hf
      cases hf
      exact filterSlots_nodup l F.1 F.2.length h.2

theorem frameShape_split {orig : List Domain} {v : Value} {vs : Domain} {doms : List Domain}
    {pre : List Value} (h : FrameShape orig (((v :: vs) :: doms), pre)) :
    FrameShape orig (doms, pre ++ [v]) ∧ vs.Nodup := by
  refine ⟨⟨?_, fun d hd => h.2 d (List.mem_cons_of_mem _ hd)⟩, (List.nodup_cons.mp (h.2 _ List.mem_cons_self)).2⟩
  have h1 := h.1
  rw [fullDomains_length] at h1 ⊢
  simp only [List.length_cons, List.length_append, List.length_nil] at h1 ⊢
  omega

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
