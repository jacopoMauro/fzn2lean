/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantShape.lean
Validation: build this module through Lake to preserve package initialization metadata.
Purpose: R3b slot shapes and synchronization coverage for boxes with integer and Boolean slots.
Dependencies: LcgRunInvariantSync supplies the existing sync definitions and integer lemmas;
SchedulerDecision supplies ShapeTypedDomains. Same-sort definedness replaces integer-only
value decomposition in syncOne_covers_shape. This leaf helper prepares the generalized frame
proofs without changing the scheduler or existing integer-box theorem statements.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantSync
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

/-- Every original value of slot `s` is an integer. -/
def IntSlot (orig : List Domain) (s : Nat) : Prop :=
  ∀ v ∈ orig.getD s Dom.empty, ∃ k : Int, v = Value.int k

/-- Every original value of slot `s` is a Boolean. -/
def BoolSlot (orig : List Domain) (s : Nat) : Prop :=
  ∀ v ∈ orig.getD s Dom.empty, ∃ b : Bool, v = Value.bool b

theorem getD_mem_orig {orig : List Domain} {s : Nat} {v : Value} (h : v ∈ orig.getD s Dom.empty) :
    ∃ d ∈ orig, v ∈ d := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hs : orig[s]? with
  | none => rw [hs] at h; simp at h
  | some d => rw [hs] at h; exact ⟨d, List.mem_of_getElem? hs, h⟩

/-- Each slot of a shape-typed box is integer or Boolean. -/
theorem slot_cases {orig : List Domain} (h : ShapeTypedDomains orig) (s : Nat) :
    IntSlot orig s ∨ BoolSlot orig s := by
  unfold IntSlot BoolSlot
  rw [List.getD_eq_getElem?_getD]
  cases hs : orig[s]? with
  | none => left; intro v hv; simp at hv
  | some d => exact h d (List.mem_of_getElem? hs)

theorem boolSlot_slotBoolB {orig : List Domain} {s : Nat} (h : BoolSlot orig s) :
    slotBoolB orig s = true := by
  unfold LeanFzn.Solver.Propagation.slotBoolB
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨b, rfl⟩ := h v ((DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv))
  rfl

theorem boolSlot_of_slotBoolB {orig : List Domain} {s : Nat} (h : slotBoolB orig s = true) :
    BoolSlot orig s := by
  unfold LeanFzn.Solver.Propagation.slotBoolB at h
  intro v hv
  have hvE : v ∈ Dom.enum (orig.getD s Dom.empty) := by
    rw [← domElems_eq_enum]
    exact (DomainLike.mem_iff _ v).mp hv
  have := List.all_eq_true.mp h v hvE
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | _ => simp at this

theorem intSlot_not_boolSlot_of_mem {orig : List Domain} {s : Nat} {v : Value}
    (hv : v ∈ orig.getD s Dom.empty) (hi : IntSlot orig s) (hb : BoolSlot orig s) : False := by
  obtain ⟨k, rfl⟩ := hi v hv
  obtain ⟨b, hb'⟩ := hb _ hv
  cases hb'

/-- A value of an integer slot is not Boolean-only: `slotBoolB` is false. -/
theorem intSlot_slotBoolB_false {orig : List Domain} {s : Nat} {v : Value}
    (hv : v ∈ orig.getD s Dom.empty) (hi : IntSlot orig s) : slotBoolB orig s = false := by
  cases hb : slotBoolB orig s with
  | false => rfl
  | true => exact (intSlot_not_boolSlot_of_mem hv hi (boolSlot_of_slotBoolB hb)).elim

/-- Every original value of a shape-typed box has an integer view. -/
theorem slot_viewed {orig : List Domain} (h : ShapeTypedDomains orig) {s : Nat} {v : Value}
    (hv : v ∈ orig.getD s Dom.empty) : ∃ k : Int, v.intView = some k := by
  rcases slot_cases h s with hi | hb
  · obtain ⟨k, rfl⟩ := hi v hv; exact ⟨k, rfl⟩
  · obtain ⟨b, rfl⟩ := hb v hv; exact ⟨if b then 1 else 0, rfl⟩

/-- Negation is exact wherever the atom is defined at the value. -/
theorem valueHolds_negate_of_defined {l : Literal} {v : Value}
    (h : (l.atom.evalAtValue v).isSome = true) : l.negate.valueHolds v = !l.valueHolds v := by
  obtain ⟨atom, pos⟩ := l
  cases atom <;> cases pos <;> cases v <;>
    simp_all [Atom.evalAtValue, Literal.valueHolds, Literal.negate, Value.intView]

/-- An atom defined at one value of a slot is defined at every value of the same sort. -/
theorem defined_of_sameSort {a : Atom} {v w : Value}
    (h : (a.evalAtValue v).isSome = true)
    (hs : (∃ k : Int, v = .int k) ∧ (∃ k : Int, w = .int k) ∨
          (∃ b : Bool, v = .bool b) ∧ (∃ b : Bool, w = .bool b)) :
    (a.evalAtValue w).isSome = true := by
  rcases hs with ⟨⟨k, rfl⟩, ⟨k', rfl⟩⟩ | ⟨⟨b, rfl⟩, ⟨b', rfl⟩⟩ <;>
    cases a <;> simp_all [Atom.evalAtValue, Value.intView]

/-- Two values of one slot of a shape-typed box have the same sort. -/
theorem sameSort_of_slot {orig : List Domain} {s : Nat} {v w : Value}
    (h : ShapeTypedDomains orig) (hv : v ∈ orig.getD s Dom.empty) (hw : w ∈ orig.getD s Dom.empty) :
    (∃ k : Int, v = .int k) ∧ (∃ k : Int, w = .int k) ∨
    (∃ b : Bool, v = .bool b) ∧ (∃ b : Bool, w = .bool b) := by
  rcases slot_cases h s with hi | hb
  · exact Or.inl ⟨hi v hv, hi w hw⟩
  · exact Or.inr ⟨hb v hv, hb w hw⟩

/-- Every atom is defined at a Boolean or integer value (the integer view). -/
theorem intLe_defined (s : Nat) (u : Int) {v : Value} (h : ∃ k, v.intView = some k) :
    ((Atom.intLe s u).evalAtValue v).isSome = true := by
  obtain ⟨k, hk⟩ := h
  simp [Atom.evalAtValue, hk]

/-- A literal true at a value has a defined atom there. -/
theorem defined_of_valueHolds {l : Literal} {v : Value}
    (h : l.valueHolds v = true) : (l.atom.evalAtValue v).isSome = true := by
  obtain ⟨atom, pos⟩ := l
  cases atom <;> cases pos <;> cases v <;>
    simp_all [Literal.valueHolds, Atom.evalAtValue, Value.intView]

/-- Covered integer-atom literals are semantically true in any shape-typed box. -/
theorem covers_sem_shape {orig : List Domain} {tr : List TrailEntry} {lit : Literal}
    (hat : ∀ s b, lit.atom ≠ Atom.boolEq s b)
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
    have h1 := hall _ hv
    rw [hnorm] at h1
    rw [valueHolds_negate_of_defined (defined_of_valueHolds h1), h1]
    rfl

theorem syncOne_covers_shape {orig : List Domain} {bs : BranchState leaf} {lit : Literal}
    (hint : ShapeTypedDomains orig)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD lit.atom.slot Dom.empty, v ∈ orig.getD lit.atom.slot Dom.empty)
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
    have hrem : ∀ w ∈ (Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w),
        (syncRemover bs.trail lit.atom.slot w).isSome = true := by
      intro w hw
      obtain ⟨hwo, hwf⟩ := List.mem_filter.mp hw
      have hwf' : lit.norm.valueHolds w = false := by simpa using hwf
      have hwd : w ∉ d := fun hmem => by
        have hmemE : w ∈ Dom.enum d := by
          rw [← domElems_eq_enum]
          exact (DomainLike.mem_iff _ w).mp hmem
        have := List.all_eq_true.mp hall w hmemE
        rw [hwf'] at this; cases this
      -- NC witness at the absolute slot
      have hgd : bs.frame.doms.getD lit.atom.slot Dom.empty = d := by
        rw [List.getD_eq_getElem?_getD, hd]; rfl
      have hwoD : w ∈ orig.getD lit.atom.slot Dom.empty :=
        (DomainLike.mem_iff _ w).mpr (by rw [domElems_eq_enum]; exact hwo)
      obtain ⟨e, he, hes, hef⟩ := hnc lit.atom.slot hdec w hwoD
        (by rw [hgd]; exact hwd)
      -- Agreement at one value makes the atom defined at every original value of this slot.
      obtain ⟨v0, hv0⟩ : ∃ v0, v0 ∈ d := by
        have hne' : Dom.enum d ≠ [] := by
          intro hnil
          have hemp : d.isEmpty = true := (Dom.isEmpty_eq_true_iff d).mpr hnil
          rw [hemp] at hne; cases hne
        cases hE : Dom.enum d with
        | nil => exact absurd hE hne'
        | cons v vs =>
            exact ⟨v, (DomainLike.mem_iff _ v).mpr (by
              rw [domElems_eq_enum, hE]; exact List.mem_cons_self)⟩
      have hv0o : v0 ∈ orig.getD lit.atom.slot Dom.empty := hfit v0 (by rw [hdget]; exact hv0)
      have hag := hagree e he hes v0 (by rw [hdget]; exact hv0)
      have hdefined := defined_of_sameSort (defined_of_valueHolds hag)
        (sameSort_of_slot hint hv0o hwoD)
      have hq : e.literal.negate.valueHolds w = true := by
        rw [valueHolds_negate_of_defined hdefined, hef]; rfl
      unfold syncRemover
      simp only [Option.isSome_map]
      rw [List.findRev?_eq_find?_reverse, List.find?_isSome]
      refine ⟨e, List.mem_reverse.mpr he, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨by simpa [Literal.negate] using hes, hq⟩
    -- assemble the justified push
    have hexp : ∃ ex, syncExplain bs.trail lit.atom.slot
        ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter fun w => !lit.norm.valueHolds w) = some ex := by
      unfold syncExplain
      simp only []
      have hany : (((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w)).map
          (syncRemover bs.trail lit.atom.slot)).any Option.isNone = false := by
        cases hb : (((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w)).map
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
    have hWne : ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w)).isEmpty
        = false := by
      cases hh : ((Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w)) with
      | nil =>
          exfalso
          have : w0 ∈ (Dom.enum (orig.getD lit.atom.slot Dom.empty)).filter (fun w => !lit.norm.valueHolds w) :=
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

/-- A covered literal has a semantically falsified negation, for every original box. -/
theorem covers_sem_general {orig : List Domain} {tr : List TrailEntry} {lit : Literal}
    (hcov : Covers orig tr lit) : SemFalsifiedBefore orig tr lit.negate := by
  rcases hcov with ⟨e, he, hi⟩ | hall
  · exact Or.inr ⟨e, he, by simpa only [Literal.negate_negate] using hi⟩
  · refine Or.inl ((litFalseAtRoot_iff orig lit.negate).mpr ?_)
    intro v hv
    have hs : lit.negate.atom.slot = lit.atom.slot := by simp [Literal.negate]
    rw [hs] at hv
    have h1 := hall _ hv
    rw [norm_valueHolds] at h1
    rw [valueHolds_negate_of_defined (defined_of_valueHolds h1), h1]
    rfl

/-- Integer-atom evaluation depends only on the integer view, also for Boolean values. -/
theorem valueHolds_of_intView {l : Literal} (hat : ∀ s b, l.atom ≠ Atom.boolEq s b)
    {v : Value} {k : Int} (hk : v.intView = some k) :
    l.valueHolds v = l.valueHolds (.int k) := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => exact absurd rfl (hat s b)
  | intLe s u => cases pos <;> simp only [Literal.valueHolds, hk] <;> simp [Value.intView]
  | intNe s u => cases pos <;> simp only [Literal.valueHolds, hk] <;> simp [Value.intView]

/-- Integer-atom candidate truth follows from all integer views of a domain. -/
theorem all_holds_of_views {d : Domain} (hdv : ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    {l : Literal} (hat : ∀ s b, l.atom ≠ Atom.boolEq s b)
    (H : ∀ k ∈ (Dom.enum d).filterMap Value.intView, l.valueHolds (.int k) = true) :
    (Dom.enum d).all l.valueHolds = true := by
  rw [List.all_eq_true]
  intro v hv
  have hvD : v ∈ d := (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
  obtain ⟨k, hk⟩ := hdv v hvD
  rw [valueHolds_of_intView hat hk]
  exact H k (List.mem_filterMap.mpr ⟨v, hv, hk⟩)

theorem syncCands_ok_shape {orig : List Domain} {f : BranchFrame} {s : Nat} {lit : Literal}
    (hdview : ∀ d ∈ f.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    (h : lit ∈ syncCands orig f s) :
    lit.atom.slot = s ∧
    (∃ d, f.doms[s]? = some d ∧ d.isEmpty = false ∧
        (Dom.enum d).all lit.norm.valueHolds = true) := by
  unfold syncCands at h
  by_cases hc : s < orig.length
  · rw [if_pos hc] at h
    cases hdm : f.doms[s]? with
    | none => rw [hdm] at h; simp at h
    | some d =>
      rw [hdm] at h
      simp only [] at h
      have hdi : ∀ v ∈ d, ∃ k : Int, v.intView = some k :=
        hdview d (List.mem_of_getElem? hdm)
      suffices H : lit.atom.slot = s ∧ d.isEmpty = false ∧ (Dom.enum d).all lit.norm.valueHolds = true from
        ⟨H.1, ⟨d, rfl, H.2.1, H.2.2⟩⟩
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
            refine ⟨rfl, isEmpty_false_of_mem hmem, ?_⟩
            apply all_holds_of_views hdi (fun _ _ => by simp [Literal.norm, negLe])
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
            refine ⟨rfl, isEmpty_false_of_mem hmem, ?_⟩
            apply all_holds_of_views hdi (fun _ _ => by simp [Literal.norm, posLe])
            intro k hk
            have := ((List.max?_eq_some_iff.mp hmax).2 k hk)
            simp [Literal.norm, Literal.valueHolds, posLe, Value.intView]
            omega
          · rw [if_neg hhi] at h; simp at h
      · -- fixing
        split at h
        · rename_i i hde
          by_cases hi : i ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView
          · rw [if_pos hi] at h
            have hl : lit = negNe s i := by simpa [valueLiteral] using h
            subst hl
            have hmem : i ∈ (Dom.enum d).filterMap Value.intView := by
              rw [hde]
              exact List.mem_filterMap.mpr ⟨Value.int i, List.mem_cons_self, rfl⟩
            exact ⟨rfl, isEmpty_false_of_mem hmem,
              by rw [hde]; simp [Literal.norm, Literal.valueHolds, negNe, Value.intView]⟩
          · rw [if_neg hi] at h; simp at h
        · rename_i b hde
          have hl : lit = posBool s b := by simpa [valueLiteral] using h
          subst hl
          have hmem : (if b = true then 1 else 0) ∈
              (Dom.enum d).filterMap Value.intView := by
            rw [hde]
            exact List.mem_filterMap.mpr ⟨Value.bool b, List.mem_cons_self, rfl⟩
          exact ⟨rfl, isEmpty_false_of_mem hmem,
            by rw [hde]; cases b <;> simp [Literal.norm, Literal.valueHolds, posBool]⟩
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
            refine ⟨rfl, isEmpty_false_of_mem (List.min?_mem hmin), ?_⟩
            apply all_holds_of_views hdi (fun _ _ => by simp [Literal.norm, posNe])
            intro k hk
            have hne : k ≠ h0 := fun heq => by
              subst heq; simp [hk] at hnc
            simp [Literal.norm, Literal.valueHolds, posNe, Value.intView, hne]
  · rw [if_neg hc] at h; simp at h

theorem foldl_syncOne_covers_shape {orig : List Domain} (hint : ShapeTypedDomains orig) (F : BranchFrame)
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
        have hcov := syncOne_covers_shape (orig := orig) (bs := b) (lit := lit) hint
          (by rw [hb]; exact hnc)
          (by rw [hb, hs]; exact hfit)
          (by rw [hb, hs]; exact hag)
          (d := d) (by rw [hb, hs]; exact hdec) (by rw [hb, hs]; exact hd) hne hall
        exact hcov.mono (foldl_syncOne_trail_sub orig rest _)
      · exact ih hcs' _ hb1 hnc1 hag1 lit hl

/-- After `syncSlot`, every candidate of the slot is covered. -/
theorem syncSlot_covers_shape {orig : List Domain} {bs : BranchState leaf} {s : Nat}
    (hint : ShapeTypedDomains orig)
    (hdview : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hag : SlotAgree bs.trail (Frame.domains bs.frame) s)
    (hdec : s ∉ bs.frame.order) :
    ∀ lit ∈ syncCands orig bs.frame s, Covers orig (syncSlot orig bs s).trail lit := by
  intro lit hl
  unfold syncSlot
  exact foldl_syncOne_covers_shape hint bs.frame s _
    (fun l hl => by
      obtain ⟨h1, h2⟩ := syncCands_ok_shape hdview hl
      exact ⟨h1, h2⟩) hfit hdec bs rfl hnc hag lit hl

theorem explSlot_of_covers_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    {s : Nat} (hint : ShapeTypedDomains orig)
    (_hdview : ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    (hfit : ∀ v ∈ (Frame.domains F).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hcov : ∀ lit ∈ syncCands orig F s, Covers orig tr lit) :
    ExplSlot orig tr (Frame.domains F) s := by
  cases hdm : F.doms[s]? with
  | none =>
      have hg := domains_getD_remaining_none F hdm
      unfold ExplSlot
      rw [hg]
      refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 => ?_⟩
      · simp [domMaxI, domInts, Dom.enum_empty] at h
      · simp [domMinI, domInts, Dom.enum_empty] at h
      · cases h
      · intro h2 h3; obtain ⟨v, hv, -⟩ := h1; cases hv
  | some d =>
      have hg := domains_getD_remaining F hdm
      have hfit' : ∀ v ∈ d, v ∈ orig.getD s Dom.empty := fun v hv => hfit v (by rw [hg]; exact hv)
      unfold ExplSlot
      rw [hg]
      have hcov' : ∀ lit ∈ syncCands orig F s, SemFalsifiedBefore orig tr lit.negate :=
        fun lit hl => covers_sem_general (hcov lit hl)
      refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 h2 h3 => ?_⟩
      · obtain ⟨⟨x, hx, hxv⟩, -⟩ := domMaxI_spec h
        have hxo := hfit' x hx
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_hi hlt hdm (max?_of_domMaxI h) (mem_oints_of hxo hxv))
      · obtain ⟨⟨x, hx, hxv⟩, -⟩ := domMinI_spec h
        have hxo := hfit' x hx
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_lo hlt hdm (min?_of_domMinI h) (mem_oints_of hxo hxv))
      · have hdc : Dom.enum d = [Value.int c] := h
        have hmemD : Value.int c ∈ d := (DomainLike.mem_iff _ _).mpr (by
          rw [domElems_eq_enum, hdc]; exact List.mem_cons_self)
        have hxo := hfit' (Value.int c) hmemD
        have hlt := lt_of_mem_getD hxo
        exact hcov' _ (cand_fix hlt hdm hdc (mem_oints_of hxo rfl))
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
            exact h3 y ((DomainLike.mem_iff _ y).mpr (by rw [domElems_eq_enum]; exact hy)) hyk
          exact hcov' _ (cand_hole hlt hdm (min?_of_domMinI hmn) (max?_of_domMaxI hmx)
            hko hmnk hkmx hnin)
        · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
          intro v hv
          have hslot : (negNe s k).atom.slot = s := rfl
          have hvD : v ∈ orig.getD s Dom.empty := by
            rw [hslot] at hv
            exact (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
          obtain ⟨k', hkv⟩ := slot_viewed hint hvD
          have hk' : k' ∈ (Dom.enum (orig.getD s Dom.empty)).filterMap Value.intView :=
            mem_oints_of hvD hkv
          have hne : k' ≠ k := fun he => hko (he ▸ hk')
          rw [valueHolds_of_intView (fun _ _ => by simp [negNe]) hkv]
          simp [Literal.valueHolds, negNe, Value.intView, hne]

theorem syncSlot_explains_shape {orig : List Domain} {bs : BranchState leaf} {s : Nat}
    (hint : ShapeTypedDomains orig)
    (hdview : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfit : ∀ v ∈ (Frame.domains bs.frame).getD s Dom.empty, v ∈ orig.getD s Dom.empty)
    (hag : SlotAgree bs.trail (Frame.domains bs.frame) s)
    (hdec : s ∉ bs.frame.order) :
    ExplSlot orig (syncSlot orig bs s).trail (Frame.domains bs.frame) s :=
  explSlot_of_covers_shape hint hdview hfit (syncSlot_covers_shape hint hdview hnc hfit hag hdec)

theorem foldl_syncSlot_explains_shape_shape {orig : List Domain} (hint : ShapeTypedDomains orig) (F : BranchFrame)
    (hdview : ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
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
      · have hex := syncSlot_explains_shape (orig := orig) (bs := b) (s := i) hint
          (by rw [hb]; exact hdview) (by rw [hb]; exact hnc)
          (by rw [hb]; exact hfit _) (by rw [hb]; exact hag _)
          (by rw [hb]; exact hdec)
        rw [hb] at hex
        exact ExplSlot.mono hmono hex
      · exact ih _ hb1 hnc1 hag1 i hi hdec

theorem syncAll_explains_shape {orig : List Domain} {bs : BranchState leaf} (hint : ShapeTypedDomains orig)
    (hdview : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k)
    (hfit : ∀ s v, v ∈ (Frame.domains bs.frame).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hag : ∀ s', SlotAgree bs.trail (Frame.domains bs.frame) s') :
    ∀ i, i < bs.frame.doms.length → i ∉ bs.frame.order →
      ExplSlot orig (syncAll orig bs).trail (Frame.domains bs.frame) i := by
  intro i hi hdec
  unfold syncAll
  exact foldl_syncSlot_explains_shape_shape hint bs.frame hdview hfit (List.range bs.frame.doms.length) bs rfl
    hnc hag i (List.mem_range.mpr hi) hdec

end LeanFzn.Solver.UIP.LcgRunInv
