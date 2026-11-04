/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantSync.lean
U1c (2), state level: frame/trail explanation (`BoundsExpl`, `FixExpl`, `HolesExpl`,
`AbsentExpl`) of an INTEGER box, established by the R1d synchronisation.

Everything here is a statement about one branch state (frame + trail), with the
inputs `NarrowingComplete`, "frame inside the original box" and "int-shaped box".
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Legacy.Solver.UIP.Proofs.PendingBacked
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-- Every original value is an integer (no Boolean slot). -/
def AllIntBox (orig : List Domain) : Prop := ∀ d ∈ orig, ∀ v ∈ d, ∃ k : Int, v = Value.int k

/-- A member of a slot's enumeration lies in the slot domain. -/
theorem exists_dom_of_enum_getD {orig : List Domain} {s : Nat} {v : Value}
    (h : v ∈ Dom.enum (orig.getD s Dom.empty)) :
    ∃ d, orig[s]? = some d ∧ v ∈ d := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hs : orig[s]? with
  | none =>
      rw [hs] at h
      simp only [Option.getD_none, Dom.enum_empty, List.not_mem_nil] at h
  | some d =>
      rw [hs] at h
      exact ⟨d, rfl, (DomainLike.mem_iff d v).mpr (by simpa using h)⟩

theorem allInt_getD {orig : List Domain} (h : AllIntBox orig) (s : Nat) :
    ∀ v ∈ Dom.enum (orig.getD s Dom.empty), ∃ k : Int, v = Value.int k := by
  intro v hv
  obtain ⟨d, hd, hvd⟩ := exists_dom_of_enum_getD hv
  exact h d (List.mem_of_getElem? hd) v hvd

theorem litFalseAtRoot_boolEq_int {orig : List Domain} (h : AllIntBox orig) (s : Nat)
    (b pos : Bool) : litFalseAtRoot orig ⟨.boolEq s b, pos⟩ = true := by
  unfold litFalseAtRoot
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨k, rfl⟩ := allInt_getD h s v hv
  simp [Atom.evalAtValue]

/-- Per-slot explanation of bounds, integer fixing and holes. -/
def ExplSlot (orig : List Domain) (tr : List TrailEntry) (doms : List Domain) (s : Nat) : Prop :=
  ((∀ mx, domMaxI (doms.getD s Dom.empty) = some mx → SemFalsifiedBefore orig tr (negLe s mx)) ∧
   (∀ mn, domMinI (doms.getD s Dom.empty) = some mn → SemFalsifiedBefore orig tr (posLe s (mn - 1)))) ∧
  (∀ c, Dom.enum (doms.getD s Dom.empty) = [.int c] → SemFalsifiedBefore orig tr (posNe s c)) ∧
  (∀ h, (∃ v ∈ doms.getD s Dom.empty, ∃ a, v.intView = some a ∧ a ≤ h) →
    (∃ v ∈ doms.getD s Dom.empty, ∃ a, v.intView = some a ∧ h ≤ a) →
    (∀ v ∈ doms.getD s Dom.empty, v.intView ≠ some h) →
    SemFalsifiedBefore orig tr (negNe s h))

theorem ExplSlot.mono {orig : List Domain} {pre post : List TrailEntry} {doms : List Domain}
    {s : Nat} (hsub : ∀ e ∈ pre, e ∈ post) (h : ExplSlot orig pre doms s) :
    ExplSlot orig post doms s :=
  ⟨⟨fun mx hm => semFalsifiedBefore_mono hsub (h.1.1 mx hm),
    fun mn hm => semFalsifiedBefore_mono hsub (h.1.2 mn hm)⟩,
   fun c hc => semFalsifiedBefore_mono hsub (h.2.1 c hc),
   fun k h1 h2 h3 => semFalsifiedBefore_mono hsub (h.2.2 k h1 h2 h3)⟩

/-- Membership at a slot is determined by the slot's enumeration. -/
theorem mem_getD_congr_enum {d1 d2 : List Domain} {s : Nat}
    (heq : Dom.enum (d1.getD s Dom.empty) = Dom.enum (d2.getD s Dom.empty)) :
    ∀ v, v ∈ d1.getD s Dom.empty ↔ v ∈ d2.getD s Dom.empty := by
  intro v
  have h1 : v ∈ d1.getD s Dom.empty ↔ v ∈ Dom.enum (d1.getD s Dom.empty) := by
    rw [DomainLike.mem_iff, domElems_eq_enum]
  have h2 : v ∈ d2.getD s Dom.empty ↔ v ∈ Dom.enum (d2.getD s Dom.empty) := by
    rw [DomainLike.mem_iff, domElems_eq_enum]
  rw [h1, h2, heq]

/-- Slot-local transfer along equal enumerations at the slot. -/
theorem ExplSlot.congr {orig : List Domain} {tr : List TrailEntry} {d1 d2 : List Domain}
    {s : Nat} (heq : Dom.enum (d1.getD s Dom.empty) = Dom.enum (d2.getD s Dom.empty))
    (h : ExplSlot orig tr d1 s) : ExplSlot orig tr d2 s := by
  have hm := mem_getD_congr_enum heq
  have hmax : domMaxI (d1.getD s Dom.empty) = domMaxI (d2.getD s Dom.empty) := by
    rw [domMaxI_enum, heq, ← domMaxI_enum]
  have hmin : domMinI (d1.getD s Dom.empty) = domMinI (d2.getD s Dom.empty) := by
    rw [domMinI_enum, heq, ← domMinI_enum]
  unfold ExplSlot at h ⊢
  refine ⟨⟨fun mx hmx => h.1.1 mx ?_, fun mn hmn => h.1.2 mn ?_⟩,
    fun c hc => h.2.1 c ?_, fun k h1 h2 h3 => h.2.2 k ?_ ?_ ?_⟩
  · rw [hmax]; exact hmx
  · rw [hmin]; exact hmn
  · rw [heq]; exact hc
  · obtain ⟨v, hv, a, hva, hle⟩ := h1
    exact ⟨v, (hm v).mpr hv, a, hva, hle⟩
  · obtain ⟨v, hv, a, hva, hle⟩ := h2
    exact ⟨v, (hm v).mpr hv, a, hva, hle⟩
  · intro v hv
    exact h3 v ((hm v).mp hv)

/-- The full-frame explanation = the stated `FrameExplainedFull` of an int box. -/
def ExplDoms (orig : List Domain) (tr : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s, ExplSlot orig tr doms s

theorem explDoms_mono {orig : List Domain} {pre post : List TrailEntry} {doms : List Domain}
    (hsub : ∀ e ∈ pre, e ∈ post) (h : ExplDoms orig pre doms) : ExplDoms orig post doms :=
  fun s => (h s).mono hsub

theorem frameExplainedFull_of_explDoms {orig : List Domain} {bs : BranchState leaf}
    (hint : AllIntBox orig)
    (h : ExplDoms orig bs.trail (Frame.domains bs.frame)) : FrameExplainedFull orig bs where
  base :=
    { bounds := fun s => (h s).1
      absent := fun s b _ => by
        have := litFalseAtRoot_boolEq_int hint s b true
        exact Or.inl this
      fix := fun s c hc => (h s).2.1 c hc }
  holes := fun s k h1 h2 h3 => (h s).2.2 k h1 h2 h3

/-! ## Literal value algebra on integer values -/

theorem valueHolds_boolEq_int (s : Nat) (b pos : Bool) (k : Int) :
    (⟨.boolEq s b, pos⟩ : Literal).valueHolds (.int k) = false := by
  simp [Literal.valueHolds]

theorem valueHolds_negate_int {l : Literal} (hnb : ∀ s b, l.atom ≠ Atom.boolEq s b) (k : Int) :
    l.negate.valueHolds (.int k) = !l.valueHolds (.int k) := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => exact absurd rfl (hnb s b)
  | intLe s u => cases pos <;> simp [Literal.valueHolds, Literal.negate, Value.intView]
  | intNe s u => cases pos <;> simp [Literal.valueHolds, Literal.negate, Value.intView]

theorem not_boolEq_of_holds {l : Literal} {k : Int} (h : l.valueHolds (.int k) = true) :
    ∀ s b, l.atom ≠ Atom.boolEq s b := by
  intro s b hb
  obtain ⟨atom, pos⟩ := l
  simp only at hb
  subst hb
  rw [valueHolds_boolEq_int] at h
  cases h

/-- Root falsity of a literal = it holds at no original value of its slot. -/
theorem litFalseAtRoot_iff (orig : List Domain) (q : Literal) :
    litFalseAtRoot orig q = true ↔
      ∀ v ∈ Dom.enum (orig.getD q.atom.slot Dom.empty), q.valueHolds v = false := by
  unfold litFalseAtRoot
  rw [List.all_eq_true]
  apply forall_congr'; intro v
  apply imp_congr_right; intro _
  obtain ⟨atom, pos⟩ := q
  cases atom <;> cases pos <;> cases v <;>
    simp [Atom.evalAtValue, Literal.valueHolds, Value.intView] <;>
    (try split) <;> simp_all

/-! ## Sync coverage -/

/-- Slot-local agreement: every trail literal on slot `s` holds at every value of the slot's
frame domain. -/
def SlotAgree (tr : List TrailEntry) (doms : List Domain) (s : Nat) : Prop :=
  ∀ e ∈ tr, e.literal.atom.slot = s → ∀ v ∈ doms.getD s Dom.empty, e.literal.valueHolds v = true

theorem SlotAgree.mono {tr tr' : List TrailEntry} {doms : List Domain} {s : Nat}
    (hsub : ∀ e ∈ tr', e ∈ tr) (h : SlotAgree tr doms s) : SlotAgree tr' doms s :=
  fun e he => h e (hsub e he)

/-- `lit` is implied by a trail entry, or already holds on every original value of its slot. -/
def Covers (orig : List Domain) (tr : List TrailEntry) (lit : Literal) : Prop :=
  (∃ e ∈ tr, impliesP orig e.literal lit.norm = true) ∨
  ∀ w ∈ Dom.enum (orig.getD lit.atom.slot Dom.empty), lit.norm.valueHolds w = true

theorem Covers.mono {orig : List Domain} {tr tr' : List TrailEntry} {lit : Literal}
    (hsub : ∀ e ∈ tr, e ∈ tr') (h : Covers orig tr lit) : Covers orig tr' lit := by
  rcases h with ⟨e, he, hi⟩ | h
  · exact Or.inl ⟨e, hsub e he, hi⟩
  · exact Or.inr h

/-- A covered integer-atom literal is semantically true: its negation is falsified. -/
theorem covers_sem {orig : List Domain} {tr : List TrailEntry} {lit : Literal}
    (hint : AllIntBox orig) (hat : ∀ s b, lit.atom ≠ Atom.boolEq s b)
    (hcov : Covers orig tr lit) : SemFalsifiedBefore orig tr lit.negate := by
  have hnorm : lit.norm = lit := by
    obtain ⟨atom, pos⟩ := lit
    cases atom with
    | boolEq s b => exact absurd rfl (hat s b)
    | intLe s u => rfl
    | intNe s u => rfl
  rcases hcov with ⟨e, he, hi⟩ | hall
  · refine Or.inr ⟨e, he, ?_⟩
    rw [Literal.negate_negate, hnorm]
    rwa [hnorm] at hi
  · refine Or.inl ((litFalseAtRoot_iff orig lit.negate).mpr ?_)
    intro v hv
    have hs : lit.negate.atom.slot = lit.atom.slot := by simp [Literal.negate]
    rw [hs] at hv
    obtain ⟨k, rfl⟩ := allInt_getD hint _ v hv
    have h1 := hall _ hv
    rw [hnorm] at h1
    rw [valueHolds_negate_int hat, h1]
    rfl

theorem syncOne_trail_sub (orig : List Domain) (bs : BranchState leaf) (lit : Literal) :
    ∀ e ∈ bs.trail, e ∈ (syncOne orig bs lit).trail := by
  obtain ⟨ex, hex, -⟩ := syncOne_trail orig bs lit
  intro e he; rw [hex]; exact List.mem_append_left _ he

theorem domains_getD_remaining (f : BranchFrame) {s : Nat} {d : Domain}
    (hd : f.doms[s]? = some d) : (Frame.domains f).getD s Dom.empty = d := by
  rw [List.getD_eq_getElem?_getD, Frame.domains, hd]
  rfl

/-- One synchronisation push covers its literal. -/
theorem syncOne_covers {orig : List Domain} {bs : BranchState leaf} {lit : Literal}
    (hint : AllIntBox orig)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD lit.atom.slot Dom.empty,
      v ∈ orig.getD lit.atom.slot Dom.empty)
    (hagree : SlotAgree bs.trail (Frame.domains bs.frame) lit.atom.slot)
    {d : Domain} (hdec : lit.atom.slot ∉ bs.frame.order)
    (hd : bs.frame.doms[lit.atom.slot]? = some d)
    (hne : d.isEmpty = false) (hall : (Dom.enum d).all lit.norm.valueHolds = true) :
    Covers orig (syncOne orig bs lit).trail lit := by
  by_cases hcov : Covers orig bs.trail lit
  · exact hcov.mono (syncOne_trail_sub orig bs lit)
  · have hnot : (∀ e ∈ bs.trail, impliesP orig e.literal lit.norm ≠ true) ∧
        ∃ w ∈ Dom.enum (orig.getD lit.atom.slot Dom.empty), lit.norm.valueHolds w ≠ true := by
      unfold Covers at hcov
      rw [not_or] at hcov
      obtain ⟨h1, h2⟩ := hcov
      refine ⟨fun e he hi => h1 ⟨e, he, hi⟩, ?_⟩
      refine Classical.byContradiction fun hh => h2 ?_
      intro w hw
      exact Classical.byContradiction fun hw' => hh ⟨w, hw, hw'⟩
    obtain ⟨hnimp, w0, hw0, hw0f⟩ := hnot
    have hdget : (Frame.domains bs.frame).getD lit.atom.slot Dom.empty = d :=
      domains_getD_remaining bs.frame hd
    -- the remover of every rejected original value
    have hrem : ∀ w ∈ (Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          (fun w => !lit.norm.valueHolds w),
        (syncRemover bs.trail lit.atom.slot w).isSome = true := by
      intro w hw
      obtain ⟨hwo, hwf⟩ := List.mem_filter.mp hw
      have hwf' : lit.norm.valueHolds w = false := by simpa using hwf
      have hwd : w ∉ d := fun hmem => by
        have := List.all_eq_true.mp hall w ((DomainLike.mem_iff d w).mp hmem)
        rw [hwf'] at this; cases this
      obtain ⟨k, rfl⟩ := allInt_getD hint _ w hwo
      -- NC witness at the absolute slot
      have hgd : bs.frame.doms.getD lit.atom.slot Dom.empty = d := by
        rw [List.getD_eq_getElem?_getD, hd]; rfl
      obtain ⟨e, he, hes, hef⟩ := hnc lit.atom.slot hdec (Value.int k)
        ((DomainLike.mem_iff _ _).mpr hwo) (by rw [hgd]; exact hwd)
      -- e's literal is not a Boolean atom: it holds at a value of the (nonempty) domain
      obtain ⟨v0, hv0⟩ : ∃ v0, v0 ∈ d := by
        cases hd0 : Dom.enum d with
        | nil =>
            have htrue : d.isEmpty = true := (Dom.isEmpty_eq_true_iff d).mpr hd0
            rw [htrue] at hne; cases hne
        | cons v vs =>
            exact ⟨v, (DomainLike.mem_iff d v).mpr
              (by rw [domElems_eq_enum, hd0]; exact List.mem_cons_self ..)⟩
      have hv0o : v0 ∈ orig.getD lit.atom.slot Dom.empty := hfit v0 (by rw [hdget]; exact hv0)
      obtain ⟨k0, rfl⟩ := allInt_getD hint _ v0 ((DomainLike.mem_iff _ v0).mp hv0o)
      have hag := hagree e he hes (Value.int k0) (by rw [hdget]; exact hv0)
      have hnb := not_boolEq_of_holds hag
      have hq : e.literal.negate.valueHolds (.int k) = true := by
        rw [valueHolds_negate_int hnb, hef]; rfl
      unfold syncRemover
      simp only [Option.isSome_map]
      rw [List.findRev?_eq_find?_reverse, List.find?_isSome]
      refine ⟨e, List.mem_reverse.mpr he, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨by simpa [Literal.negate] using hes, hq⟩
    -- assemble the justified push
    have hexp : ∃ ex, syncExplain bs.trail lit.atom.slot
        ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          fun w => !lit.norm.valueHolds w) = some ex := by
      unfold syncExplain
      simp only []
      have hany : (((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          (fun w => !lit.norm.valueHolds w)).map
          (syncRemover bs.trail lit.atom.slot)).any Option.isNone = false := by
        cases hb : (((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          (fun w => !lit.norm.valueHolds w)).map
          (syncRemover bs.trail lit.atom.slot)).any Option.isNone with
        | false => rfl
        | true =>
            obtain ⟨x, hx, hxn⟩ := List.any_eq_true.mp hb
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
            have := hrem w hw
            simp only [Option.isNone_iff_eq_none] at hxn
            rw [hxn] at this
            cases this
      rw [hany]
      exact ⟨_, rfl⟩
    obtain ⟨ex, hex⟩ := hexp
    have hWne : ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
        (fun w => !lit.norm.valueHolds w)).isEmpty = false := by
      cases hh : ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
          (fun w => !lit.norm.valueHolds w)) with
      | nil =>
          exfalso
          have : w0 ∈ (Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter
              (fun w => !lit.norm.valueHolds w) :=
            List.mem_filter.mpr ⟨hw0, by simpa using hw0f⟩
          rw [hh] at this; cases this
      | cons x xs => rfl
    have hany : (bs.trail.any fun e => impliesP orig e.literal lit.norm) = false := by
      cases hb : bs.trail.any fun e => impliesP orig e.literal lit.norm with
      | false => rfl
      | true =>
          obtain ⟨e, he, hi⟩ := List.any_eq_true.mp hb
          exact absurd hi (hnimp e he)
    have hany' : ((trailOnSlot bs.trail lit.atom.slot).any
        fun e => impliesP orig e.literal lit.norm) = false := by
      rw [trailOnSlot_any_impliesP (norm_atom_slot lit)]
      exact hany
    have hsc : syncClause orig bs lit = some (lit.norm :: ex) := by
      unfold syncClause
      simp only []
      rw [hd]
      simp only []
      rw [if_pos (by simp only [hne, hall, hWne, hany']; rfl),
        syncExplain_trailOnSlot, hex]
      rfl
    have hso : syncOne orig bs lit = narrowState bs bs.frame lit (lit.norm :: ex) [] := by
      unfold syncOne; rw [hsc]
    rw [hso]
    refine Or.inl ⟨⟨lit.norm, bs.level, some { clause := lit.norm :: ex }⟩, ?_, ?_⟩
    · simp only [narrowState]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
    · exact impliesP_refl _ _

theorem intView_int (k : Int) : (Value.int k).intView = some k := rfl

theorem all_holds_of_ints {d : Domain} (hdi : ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    {l : Literal}
    (H : ∀ k ∈ (Dom.enum d).filterMap Value.intView, l.valueHolds (.int k) = true) :
    (Dom.enum d).all l.valueHolds = true := by
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨k, rfl⟩ := hdi v ((DomainLike.mem_iff d v).mpr hv)
  exact H k (List.mem_filterMap.mpr ⟨.int k, hv, rfl⟩)

theorem isEmpty_false_of_mem {d : Domain} {k : Int}
    (h : k ∈ (Dom.enum d).filterMap Value.intView) :
    d.isEmpty = false := by
  cases hb : d.isEmpty with
  | false => rfl
  | true =>
      rw [Dom.isEmpty_eq_true_iff d] at hb
      rw [hb] at h
      simp at h

/-- Every sync candidate of an integer frame is an integer atom of its slot holding on the
whole (nonempty) frame domain of that slot. -/
theorem syncCands_ok {orig : List Domain} {f : BranchFrame} {s : Nat} {lit : Literal}
    (hdint : ∀ d ∈ f.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (h : lit ∈ syncCands orig f s) :
    lit.atom.slot = s ∧
    (∃ d, f.doms[s]? = some d ∧ d.isEmpty = false ∧
        (Dom.enum d).all lit.norm.valueHolds = true) ∧
    (∀ s' b, lit.atom ≠ Atom.boolEq s' b) := by
  unfold syncCands at h
  by_cases hc : s < orig.length
  · rw [if_pos hc] at h
    cases hdm : f.doms[s]? with
    | none => rw [hdm] at h; simp at h
    | some d =>
      rw [hdm] at h
      simp only [] at h
      have hdi : ∀ v ∈ d, ∃ k : Int, v = Value.int k :=
        hdint d (List.mem_of_getElem? hdm)
      suffices H : lit.atom.slot = s ∧ d.isEmpty = false ∧
          (Dom.enum d).all lit.norm.valueHolds = true ∧
          (∀ s' b, lit.atom ≠ Atom.boolEq s' b) from
        ⟨H.1, ⟨d, rfl, H.2.1, H.2.2.1⟩, H.2.2.2⟩
      simp only [List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · -- lower bound
        cases hmin : ((Dom.enum d).filterMap Value.intView).min? with
        | none => rw [hmin] at h; simp at h
        | some lo =>
          rw [hmin] at h
          dsimp only at h
          by_cases hlo : lo ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView
          · rw [if_pos hlo] at h
            have hl : lit = negLe s (lo - 1) := by simpa using h
            subst hl
            have hmem := List.min?_mem hmin
            refine ⟨rfl, isEmpty_false_of_mem hmem, ?_, fun _ _ => by simp [negLe]⟩
            apply all_holds_of_ints hdi
            intro k hk
            have := ((List.min?_eq_some_iff.mp hmin).2 k hk)
            simp [Literal.norm, Literal.valueHolds, negLe, Value.intView]
            omega
          · rw [if_neg hlo] at h; simp at h
      · -- upper bound
        cases hmax : ((Dom.enum d).filterMap Value.intView).max? with
        | none => rw [hmax] at h; simp at h
        | some hi =>
          rw [hmax] at h
          dsimp only at h
          by_cases hhi : hi ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView
          · rw [if_pos hhi] at h
            have hl : lit = posLe s hi := by simpa using h
            subst hl
            have hmem := List.max?_mem hmax
            refine ⟨rfl, isEmpty_false_of_mem hmem, ?_, fun _ _ => by simp [posLe]⟩
            apply all_holds_of_ints hdi
            intro k hk
            have := ((List.max?_eq_some_iff.mp hmax).2 k hk)
            simp [Literal.norm, Literal.valueHolds, posLe, Value.intView]
            omega
          · rw [if_neg hhi] at h; simp at h
      · -- fixing
        split at h
        · rename_i i hbe
          by_cases hi : i ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView
          · rw [if_pos hi] at h
            have hl : lit = negNe s i := by simpa [valueLiteral] using h
            subst hl
            have his : d.isEmpty = false := by
              cases hb : d.isEmpty with
              | false => rfl
              | true =>
                  rw [Dom.isEmpty_eq_true_iff d] at hb
                  rw [hb] at hbe
                  simp at hbe
            refine ⟨rfl, his, ?_, fun _ _ => by simp [negNe]⟩
            simp [hbe, Literal.norm, Literal.valueHolds, negNe, Value.intView]
          · rw [if_neg hi] at h; simp at h
        · rename_i b hbe
          exfalso
          have hmem : (Value.bool b) ∈ d :=
            (DomainLike.mem_iff d _).mpr
              (by rw [domElems_eq_enum, hbe]; exact List.mem_cons_self ..)
          obtain ⟨k, hk⟩ := hdi (Value.bool b) hmem
          cases hk
        · simp at h
      · -- interior holes
        cases hmin : ((Dom.enum d).filterMap Value.intView).min? with
        | none => rw [hmin] at h; simp at h
        | some lo =>
          cases hmax : ((Dom.enum d).filterMap Value.intView).max? with
          | none => rw [hmin, hmax] at h; simp at h
          | some hi =>
            rw [hmin, hmax] at h
            dsimp only at h
            obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp h
            have hh1 := (List.mem_filter.mp (List.mem_eraseDups.mp hh0)).2
            have hnc : ((Dom.enum d).filterMap Value.intView).contains h0 = false := by
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh1
              exact hh1.2
            refine ⟨rfl, isEmpty_false_of_mem (List.min?_mem hmin), ?_, fun _ _ => by simp [posNe]⟩
            apply all_holds_of_ints hdi
            intro k hk
            have hne : k ≠ h0 := fun heq => by
              subst heq; simp [hk] at hnc
            simp [Literal.norm, Literal.valueHolds, posNe, Value.intView, hne]
  · rw [if_neg hc] at h; simp at h

/-! ## The sync fold -/

theorem nc_mono {tr tr' : List TrailEntry} {orig : List Domain} {f : BranchFrame}
    (hsub : ∀ e ∈ tr, e ∈ tr') (h : NarrowingComplete tr orig f) :
    NarrowingComplete tr' orig f := by
  intro i hi w hw hn
  obtain ⟨e, he, h1, h2⟩ := h i hi w hw hn
  exact ⟨e, hsub e he, h1, h2⟩

theorem syncOne_slotAgree {orig : List Domain} {bs : BranchState leaf} {lit : Literal}
    {s' : Nat} (h : SlotAgree bs.trail (Frame.domains bs.frame) s') :
    SlotAgree (syncOne orig bs lit).trail (Frame.domains bs.frame) s' := by
  unfold syncOne
  cases hc : syncClause orig bs lit with
  | none => exact h
  | some c =>
      obtain ⟨d, ex, hd, hne, hall, -, -, -⟩ := syncClause_spec hc
      intro e he hes v hv
      simp only [narrowState] at he
      rcases List.mem_append.mp he with he | he
      · exact h e he hes v hv
      · have he' : e = ⟨lit.norm, bs.level, some { clause := c }⟩ := List.mem_singleton.mp he
        subst he'
        simp only [norm_atom_slot] at hes
        have hdg : (Frame.domains bs.frame).getD lit.atom.slot Dom.empty = d :=
          domains_getD_remaining bs.frame hd
        rw [hes] at hdg
        rw [hdg] at hv
        exact List.all_eq_true.mp hall v ((DomainLike.mem_iff d v).mp hv)

theorem foldl_syncOne_trail_sub (orig : List Domain) (cs : List Literal) :
    ∀ (b : BranchState leaf), ∀ e ∈ b.trail, e ∈ (cs.foldl (syncOne orig) b).trail := by
  induction cs with
  | nil => intro b e he; exact he
  | cons c rest ih =>
      intro b e he
      exact ih _ e (syncOne_trail_sub orig b c e he)

theorem foldl_syncOne_covers {orig : List Domain} (hint : AllIntBox orig) (F : BranchFrame)
    (s : Nat) (cs : List Literal)
    (hcs : ∀ lit ∈ cs, lit.atom.slot = s ∧
      (∃ d, F.doms[s]? = some d ∧ d.isEmpty = false ∧
        (Dom.enum d).all lit.norm.valueHolds = true))
    (hfit : ∀ v ∈ (Frame.domains F).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hdec : s ∉ F.order) :
    ∀ (b : BranchState leaf), b.frame = F → NarrowingComplete b.trail orig F →
      SlotAgree b.trail (Frame.domains F) s →
      ∀ lit ∈ cs, Covers orig (cs.foldl (syncOne orig) b).trail lit := by
  induction cs with
  | nil => intro b _ _ _ lit hl; cases hl
  | cons c rest ih =>
      intro b hb hnc hag lit hl
      have hcs' : ∀ lit ∈ rest, lit.atom.slot = s ∧
          (∃ d, F.doms[s]? = some d ∧ d.isEmpty = false ∧
            (Dom.enum d).all lit.norm.valueHolds = true) :=
        fun l hl => hcs l (List.mem_cons_of_mem _ hl)
      have hb1 : (syncOne orig b c).frame = F := by rw [syncOne_frame, hb]
      have hsub : ∀ e ∈ b.trail, e ∈ (syncOne orig b c).trail := syncOne_trail_sub orig b c
      have hnc1 : NarrowingComplete (syncOne orig b c).trail orig F := nc_mono hsub hnc
      have hag1 : SlotAgree (syncOne orig b c).trail (Frame.domains F) s := by
        have := syncOne_slotAgree (orig := orig) (bs := b) (lit := c) (s' := s)
          (by rw [hb]; exact hag)
        rw [hb] at this; exact this
      rcases List.mem_cons.mp hl with rfl | hl
      · obtain ⟨hs, d, hd, hne, hall⟩ := hcs lit List.mem_cons_self
        have hcov := syncOne_covers (orig := orig) (bs := b) (lit := lit) hint
          (by rw [hb]; exact hnc)
          (by rw [hb, hs]; exact hfit)
          (by rw [hb, hs]; exact hag)
          (d := d) (by rw [hb, hs]; exact hdec) (by rw [hb, hs]; exact hd) hne hall
        exact hcov.mono (foldl_syncOne_trail_sub orig rest _)
      · exact ih hcs' _ hb1 hnc1 hag1 lit hl

/-- After `syncSlot`, every candidate of the slot is covered. -/
theorem syncSlot_covers {orig : List Domain} {bs : BranchState leaf} {s : Nat}
    (hint : AllIntBox orig)
    (hdint : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hag : SlotAgree bs.trail (Frame.domains bs.frame) s)
    (hdec : s ∉ bs.frame.order) :
    ∀ lit ∈ syncCands orig bs.frame s, Covers orig (syncSlot orig bs s).trail lit := by
  intro lit hl
  unfold syncSlot
  exact foldl_syncOne_covers hint bs.frame s _
    (fun l hl => by
      obtain ⟨h1, h2, -⟩ := syncCands_ok hdint hl
      exact ⟨h1, h2⟩) hfit hdec bs rfl hnc hag lit hl

/-! ## Candidates are offered -/

section CandMem
variable {orig : List Domain} {f : BranchFrame} {s : Nat} {d : Domain}

theorem cand_lo (hc : s < orig.length) (hd : f.doms[s]? = some d)
    {lo : Int} (hmin : ((Dom.enum d).filterMap Value.intView).min? = some lo)
    (hlo : lo ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) :
    negLe s (lo - 1) ∈ syncCands orig f s := by
  unfold syncCands
  rw [if_pos hc, hd]
  dsimp only
  simp only [List.mem_append]
  left; left; left
  rw [hmin]; dsimp only
  rw [if_pos hlo]; exact List.mem_singleton_self _

theorem cand_hi (hc : s < orig.length) (hd : f.doms[s]? = some d)
    {hi : Int} (hmax : ((Dom.enum d).filterMap Value.intView).max? = some hi)
    (hhi : hi ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) :
    posLe s hi ∈ syncCands orig f s := by
  unfold syncCands
  rw [if_pos hc, hd]
  dsimp only
  simp only [List.mem_append]
  left; left; right
  rw [hmax]; dsimp only
  rw [if_pos hhi]; exact List.mem_singleton_self _

theorem cand_fix (hc : s < orig.length) (hd : f.doms[s]? = some d)
    {i : Int} (hde : Dom.enum d = [Value.int i])
    (hi : i ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView) :
    negNe s i ∈ syncCands orig f s := by
  unfold syncCands
  rw [if_pos hc, hd]
  dsimp only
  simp only [hde, List.mem_append]
  left; right
  rw [if_pos hi]
  simp [valueLiteral]

theorem cand_hole (hc : s < orig.length) (hd : f.doms[s]? = some d)
    {lo hi : Int} (hmin : ((Dom.enum d).filterMap Value.intView).min? = some lo)
    (hmax : ((Dom.enum d).filterMap Value.intView).max? = some hi) {h0 : Int}
    (hh : h0 ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView)
    (hl : lo < h0) (hh2 : h0 < hi)
    (hnin : h0 ∉ (Dom.enum d).filterMap Value.intView) :
    posNe s h0 ∈ syncCands orig f s := by
  unfold syncCands
  rw [if_pos hc, hd]
  dsimp only
  simp only [List.mem_append]
  right
  rw [hmin, hmax]; dsimp only
  apply List.mem_map.mpr
  refine ⟨h0, List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hh, ?_⟩), rfl⟩
  simp [hl, hh2]
  exact fun x hx hxv => hnin (List.mem_filterMap.mpr ⟨x, hx, hxv⟩)

end CandMem

/-! ## Candidate coverage explains the slot -/

theorem lt_of_mem_getD {orig : List Domain} {s : Nat} {v : Value}
    (h : v ∈ orig.getD s Dom.empty) : s < orig.length := by
  by_cases hs : s < orig.length
  · exact hs
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    simp at h

theorem domains_getD_remaining_none (f : BranchFrame) {s : Nat}
    (hd : f.doms[s]? = none) : (Frame.domains f).getD s Dom.empty = Dom.empty := by
  rw [List.getD_eq_getElem?_getD, Frame.domains, hd]
  rfl

theorem max?_of_domMaxI {d : Domain} {mx : Int} (h : domMaxI d = some mx) :
    ((Dom.enum d).filterMap Value.intView).max? = some mx := by
  obtain ⟨⟨x, hx, hxv⟩, hall⟩ := domMaxI_spec h
  rw [List.max?_eq_some_iff]
  exact ⟨List.mem_filterMap.mpr ⟨x, (DomainLike.mem_iff d x).mp hx, hxv⟩, fun b hb => by
    obtain ⟨y, hy, hyb⟩ := List.mem_filterMap.mp hb
    exact hall y ((DomainLike.mem_iff d y).mpr hy) b hyb⟩

theorem min?_of_domMinI {d : Domain} {mn : Int} (h : domMinI d = some mn) :
    ((Dom.enum d).filterMap Value.intView).min? = some mn := by
  obtain ⟨⟨x, hx, hxv⟩, hall⟩ := domMinI_spec h
  rw [List.min?_eq_some_iff]
  exact ⟨List.mem_filterMap.mpr ⟨x, (DomainLike.mem_iff d x).mp hx, hxv⟩, fun b hb => by
    obtain ⟨y, hy, hyb⟩ := List.mem_filterMap.mp hb
    exact hall y ((DomainLike.mem_iff d y).mpr hy) b hyb⟩

theorem mem_oints_of {orig : List Domain} {s : Nat} {x : Value} {m : Int}
    (hx : x ∈ orig.getD s Dom.empty) (hxv : x.intView = some m) :
    m ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView :=
  List.mem_filterMap.mpr
    ⟨x, (DomainLike.mem_iff (orig.getD s Dom.empty) x).mp hx, hxv⟩

theorem explSlot_none {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame} {s : Nat}
    (hdm : F.doms[s]? = none) :
    ExplSlot orig tr (Frame.domains F) s := by
  have hg := domains_getD_remaining_none F hdm
  unfold ExplSlot
  rw [hg, Dom.enum_empty]
  refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 => ?_⟩
  · simp [domMaxI, domInts, Dom.enum_empty] at h
  · simp [domMinI, domInts, Dom.enum_empty] at h
  · simp [Dom.enum_empty] at h
  · intro h2 h3; obtain ⟨v, hv, -⟩ := h1; simp at hv

theorem explSlot_of_covers {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    {s : Nat} (hint : AllIntBox orig)
    (hdint : ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (hfit : ∀ v ∈ (Frame.domains F).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hcov : ∀ lit ∈ syncCands orig F s, Covers orig tr lit) :
    ExplSlot orig tr (Frame.domains F) s := by
  cases hdm : F.doms[s]? with
  | none =>
      have hg := domains_getD_remaining_none F hdm
      unfold ExplSlot
      rw [hg, Dom.enum_empty]
      refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 => ?_⟩
      · simp [domMaxI, domInts, Dom.enum_empty] at h
      · simp [domMinI, domInts, Dom.enum_empty] at h
      · simp [Dom.enum_empty] at h
      · intro h2 h3; obtain ⟨v, hv, -⟩ := h1; simp at hv
  | some d =>
      have hg := domains_getD_remaining F hdm
      have hdi := hdint d (List.mem_of_getElem? hdm)
      have hfit' : ∀ v ∈ d, v ∈ orig.getD s Dom.empty := fun v hv => hfit v (by rw [hg]; exact hv)
      unfold ExplSlot
      rw [hg]
      have hcov' : ∀ lit ∈ syncCands orig F s, SemFalsifiedBefore orig tr lit.negate :=
        fun lit hl => covers_sem hint (syncCands_ok hdint hl).2.2 (hcov lit hl)
      refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 h2 h3 => ?_⟩
      · obtain ⟨⟨x, hx, hxv⟩, -⟩ := domMaxI_spec h
        have hxo := hfit' x hx
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_hi hlt hdm (max?_of_domMaxI h) (mem_oints_of hxo hxv))
      · obtain ⟨⟨x, hx, hxv⟩, -⟩ := domMinI_spec h
        have hxo := hfit' x hx
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_lo hlt hdm (min?_of_domMinI h) (mem_oints_of hxo hxv))
      · have hxo : (Value.int c) ∈ orig.getD s Dom.empty :=
          hfit' (Value.int c) ((DomainLike.mem_iff d _).mpr
            (by rw [domElems_eq_enum, h]; exact List.mem_cons_self ..))
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_fix hlt hdm h (mem_oints_of hxo rfl))
      · obtain ⟨v1, hv1, a1, hv1a, ha1⟩ := h1
        obtain ⟨v2, hv2, a2, hv2a, ha2⟩ := h2
        obtain ⟨mn, hmn⟩ := domMinI_exists hv1 hv1a
        obtain ⟨mx, hmx⟩ := domMaxI_exists hv1 hv1a
        obtain ⟨⟨x1, hx1, hx1v⟩, hallmn⟩ := domMinI_spec hmn
        obtain ⟨⟨x2, hx2, hx2v⟩, hallmx⟩ := domMaxI_spec hmx
        have hmnk : mn < k := by
          have h1' := hallmn v1 hv1 a1 hv1a
          have h2' : mn ≠ k := fun he => h3 x1 hx1 (by rw [hx1v, he])
          omega
        have hkmx : k < mx := by
          have h1' := hallmx v2 hv2 a2 hv2a
          have h2' : mx ≠ k := fun he => h3 x2 hx2 (by rw [hx2v, he])
          omega
        have hlt := lt_of_mem_getD (hfit' v1 hv1)
        by_cases hko : k ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView
        · have hnin : k ∉ (Dom.enum d).filterMap Value.intView := fun hm => by
            obtain ⟨y, hy, hyk⟩ := List.mem_filterMap.mp hm
            exact h3 y ((DomainLike.mem_iff d y).mpr hy) hyk
          exact hcov' _ (cand_hole hlt hdm (min?_of_domMinI hmn) (max?_of_domMaxI hmx)
            hko hmnk hkmx hnin)
        · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
          intro v hv
          obtain ⟨k', rfl⟩ := allInt_getD hint _ v hv
          have hk' : k' ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView :=
            mem_oints_of ((DomainLike.mem_iff _ _).mpr hv) rfl
          have hne : k' ≠ k := fun he => hko (he ▸ hk')
          simp [Literal.valueHolds, negNe, Value.intView, hne]

/-! ## syncSlot / syncAll explain -/

theorem syncSlot_trail_sub (orig : List Domain) (bs : BranchState leaf) (s : Nat) :
    ∀ e ∈ bs.trail, e ∈ (syncSlot orig bs s).trail := by
  obtain ⟨-, -, -, ex, hex, -⟩ := syncSlot_shape orig bs s
  intro e he; rw [hex]; exact List.mem_append_left _ he

theorem foldl_syncOne_slotAgree (orig : List Domain) (F : BranchFrame) (cs : List Literal) :
    ∀ (b : BranchState leaf), b.frame = F → ∀ s',
      SlotAgree b.trail (Frame.domains F) s' →
      SlotAgree (cs.foldl (syncOne orig) b).trail (Frame.domains F) s' := by
  induction cs with
  | nil => intro b _ s' h; exact h
  | cons c rest ih =>
      intro b hb s' h
      refine ih _ (by rw [syncOne_frame, hb]) s' ?_
      have := syncOne_slotAgree (orig := orig) (bs := b) (lit := c) (s' := s')
        (by rw [hb]; exact h)
      rw [hb] at this; exact this

theorem syncSlot_slotAgree (orig : List Domain) (bs : BranchState leaf) (s s' : Nat)
    (h : SlotAgree bs.trail (Frame.domains bs.frame) s') :
    SlotAgree (syncSlot orig bs s).trail (Frame.domains bs.frame) s' := by
  unfold syncSlot
  exact foldl_syncOne_slotAgree orig bs.frame _ bs rfl s' h

/-- After `syncSlot`, the (remaining) slot is explained. -/
theorem syncSlot_explains {orig : List Domain} {bs : BranchState leaf} {s : Nat}
    (hint : AllIntBox orig)
    (hdint : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hag : SlotAgree bs.trail (Frame.domains bs.frame) s)
    (hdec : s ∉ bs.frame.order) :
    ExplSlot orig (syncSlot orig bs s).trail (Frame.domains bs.frame) s :=
  explSlot_of_covers hint hdint hfit (syncSlot_covers hint hdint hnc hfit hag hdec)

theorem foldl_syncSlot_trail_sub (orig : List Domain) (g : Nat → Nat) (L : List Nat) :
    ∀ (b : BranchState leaf), ∀ e ∈ b.trail,
      e ∈ (L.foldl (fun b i => syncSlot orig b (g i)) b).trail := by
  induction L with
  | nil => intro b e he; exact he
  | cons i rest ih =>
      intro b e he
      exact ih _ e (syncSlot_trail_sub orig b (g i) e he)

theorem foldl_syncSlot_explains {orig : List Domain} (hint : AllIntBox orig) (F : BranchFrame)
    (hdint : ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (hfit : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty) :
    ∀ (L : List Nat) (b : BranchState leaf), b.frame = F →
      NarrowingComplete b.trail orig F →
      (∀ s', SlotAgree b.trail (Frame.domains F) s') →
      ∀ i ∈ L, i ∉ F.order → ExplSlot orig
        (L.foldl (fun b i => syncSlot orig b i) b).trail
        (Frame.domains F) i := by
  intro L
  induction L with
  | nil => intro b _ _ _ i hi; cases hi
  | cons i0 rest ih =>
      intro b hb hnc hag i hi hdec
      have hb1 : (syncSlot orig b i0).frame = F := by rw [syncSlot_frame, hb]
      have hsub := syncSlot_trail_sub orig b i0
      have hnc1 := nc_mono hsub hnc
      have hag1 : ∀ s', SlotAgree (syncSlot orig b i0).trail (Frame.domains F) s' := by
        intro s'
        have := syncSlot_slotAgree orig b i0 s' (by rw [hb]; exact hag s')
        rw [hb] at this; exact this
      have hmono : ∀ e ∈ (syncSlot orig b i0).trail,
          e ∈ (rest.foldl (fun b i => syncSlot orig b i)
            (syncSlot orig b i0)).trail :=
        fun e he => foldl_syncSlot_trail_sub orig id rest _ e he
      rcases List.mem_cons.mp hi with rfl | hi
      · have hex := syncSlot_explains (orig := orig) (bs := b) (s := i) hint
          (by rw [hb]; exact hdint) (by rw [hb]; exact hnc)
          (by rw [hb]; exact hfit _) (by rw [hb]; exact hag _)
          (by rw [hb]; exact hdec)
        rw [hb] at hex
        exact ExplSlot.mono hmono hex
      · exact ih _ hb1 hnc1 hag1 i hi hdec

theorem syncAll_explains {orig : List Domain} {bs : BranchState leaf} (hint : AllIntBox orig)
    (hdint : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k)
    (hfit : ∀ s v, v ∈ (Frame.domains bs.frame).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hag : ∀ s', SlotAgree bs.trail (Frame.domains bs.frame) s') :
    ∀ i, i < bs.frame.doms.length → i ∉ bs.frame.order →
      ExplSlot orig (syncAll orig bs).trail (Frame.domains bs.frame) i := by
  intro i hi hdec
  unfold syncAll
  exact foldl_syncSlot_explains hint bs.frame hdint hfit (List.range bs.frame.doms.length) bs rfl
    hnc hag i (List.mem_range.mpr hi) hdec

/-! ## Pins explain prefix slots; slots out of range -/

theorem impliesP_negNe_posLe (orig : List Domain) (s : Nat) (k : Int) :
    impliesP orig (negNe s k) (posLe s k) = true := by
  simp [impliesP, impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, negNe, posLe, Atom.slot]

theorem impliesP_negNe_negLe (orig : List Domain) (s : Nat) (k : Int) :
    impliesP orig (negNe s k) (negLe s (k - 1)) = true := by
  simp [impliesP, impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, negNe, negLe, Atom.slot]
  omega

theorem explSlot_pin {orig : List Domain} {tr : List TrailEntry} {doms : List Domain}
    {s : Nat} {k : Int} {e : TrailEntry} (he : e ∈ tr) (hl : e.literal = negNe s k)
    (hd : Dom.enum (doms.getD s Dom.empty) = [Value.int k]) : ExplSlot orig tr doms s := by
  unfold ExplSlot
  rw [hd]
  refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun h0 h1 h2 h3 => ?_⟩
  · have : mx = k := by
      have : domMaxI [Value.int k] = some k := by simp [domMaxI, domInts, maxI]
      rw [domMaxI_enum (doms.getD s Dom.empty), hd] at h
      rw [this] at h; exact (Option.some.inj h).symm
    subst this
    exact Or.inr ⟨e, he, by rw [hl]; exact impliesP_negNe_posLe _ s mx⟩
  · have : mn = k := by
      have : domMinI [Value.int k] = some k := by simp [domMinI, domInts, minI]
      rw [domMinI_enum (doms.getD s Dom.empty), hd] at h
      rw [this] at h; exact (Option.some.inj h).symm
    subst this
    exact Or.inr ⟨e, he, by rw [hl]; exact impliesP_negNe_negLe _ s mn⟩
  · have : c = k := by simpa using h.symm
    subst this
    exact Or.inr ⟨e, he, by rw [hl]; exact impliesP_refl _ _⟩
  · exfalso
    obtain ⟨v1, hv1, a1, ha1v, ha1⟩ := h1
    obtain ⟨v2, hv2, a2, ha2v, ha2⟩ := h2
    have hv1' : v1 ∈ Dom.enum (doms.getD s Dom.empty) :=
      (DomainLike.mem_iff _ v1).mp hv1
    have hv2' : v2 ∈ Dom.enum (doms.getD s Dom.empty) :=
      (DomainLike.mem_iff _ v2).mp hv2
    rw [hd] at hv1' hv2'
    have e1 : v1 = Value.int k := List.mem_singleton.mp hv1'
    have e2 : v2 = Value.int k := List.mem_singleton.mp hv2'
    subst e1; subst e2
    have h1k : a1 = k := by simpa [Value.intView] using ha1v.symm
    have h2k : a2 = k := by simpa [Value.intView] using ha2v.symm
    exact h3 (Value.int k)
      ((DomainLike.mem_iff _ _).mpr (by rw [domElems_eq_enum, hd]; exact List.mem_cons_self ..))
      (by simp only [Value.intView, Option.some.injEq]; omega)

theorem foldl_syncSlot_slotAgree (orig : List Domain) (F : BranchFrame) (g : Nat → Nat)
    (L : List Nat) : ∀ (b : BranchState leaf), b.frame = F → ∀ s',
      SlotAgree b.trail (Frame.domains F) s' →
      SlotAgree (L.foldl (fun b i => syncSlot orig b (g i)) b).trail (Frame.domains F) s' := by
  induction L with
  | nil => intro b _ s' h; exact h
  | cons i rest ih =>
      intro b hb s' h
      refine ih _ (by rw [syncSlot_frame, hb]) s' ?_
      have := syncSlot_slotAgree orig b (g i) s' (by rw [hb]; exact h)
      rw [hb] at this; exact this

theorem syncAll_slotAgree (orig : List Domain) (bs : BranchState leaf) (s' : Nat)
    (h : SlotAgree bs.trail (Frame.domains bs.frame) s') :
    SlotAgree (syncAll orig bs).trail (Frame.domains bs.frame) s' := by
  unfold syncAll
  exact foldl_syncSlot_slotAgree orig bs.frame id _ bs rfl s' h

theorem syncAll_trail_sub (orig : List Domain) (bs : BranchState leaf) :
    ∀ e ∈ bs.trail, e ∈ (syncAll orig bs).trail := by
  obtain ⟨ex, hex, -⟩ := syncAll_trail_shape orig bs
  intro e he; rw [hex]; exact List.mem_append_left _ he

end LeanFzn.Solver.UIP.LcgRunInv
