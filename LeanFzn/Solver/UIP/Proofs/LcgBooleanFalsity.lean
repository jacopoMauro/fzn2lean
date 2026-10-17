/-
Purpose: derive semantic falsity from impossible live-frame literals on mixed domain boxes.
Dependencies: Boolean pin/frame helpers handle prefix slots; frame narrowing witnesses
handle remaining slots; LcgRunInvariantReasons supplies integer extrema and hole lemmas.
DAG: mixed frame operations -> this semantic bridge -> mixed propagation event contract.
No runtime or reason-pivot contract changes.
-/
import LeanFzn.Solver.UIP.Proofs.LcgBooleanPins
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantAbsentShape
namespace LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgContract

theorem mem_of_slotHasBool {orig : List Domain} {s : Nat} {c : Bool}
    (h : slotHasBool orig s c = true) : Value.bool c ∈ orig.getD s [] := by
  unfold slotHasBool at h
  obtain ⟨v, hv, hvb⟩ := List.any_eq_true.mp h
  cases v with
  | bool x => simp only [beq_iff_eq] at hvb; subst hvb; exact hv
  | _ => simp at hvb

theorem slotHasBool_of_mem {orig : List Domain} {s : Nat} {c : Bool}
    (h : Value.bool c ∈ orig.getD s []) : slotHasBool orig s c = true := by
  unfold slotHasBool
  exact List.any_eq_true.mpr ⟨_, h, by simp⟩

/-- On a Boolean slot, a literal that is false at `w` implies every literal on the slot that is
true at all other original Boolean values. -/
theorem impliesP_of_boolOne {orig : List Domain} {s : Nat} {e g : Literal} {w : Bool}
    (hB : BoolSlot orig s) (he : e.atom.slot = s) (hg : g.atom.slot = s)
    (hew : e.truthAtBool w = false)
    (hgc : ∀ c : Bool, Value.bool c ∈ orig.getD s [] → c ≠ w → g.truthAtBool c = true) :
    impliesP orig e g = true := by
  refine impliesP_of_table (boolSlotImp_intro (by rw [he, hg]) (by rw [he, booleanSlotB_eq_slotBoolB]; exact boolSlot_slotBoolB hB) ?_)
  intro c hh hc
  rw [he] at hh
  have hmem := mem_of_slotHasBool hh
  by_cases hcw : c = w
  · subst hcw; rw [hew] at hc; cases hc
  · exact hgc c hmem hcw

/-- **Frame falsity on a Boolean slot.** A literal false at every value of a nonempty
(narrowing-complete) frame domain of a Boolean slot is semantically falsified. -/
theorem semFalsified_of_boolDom {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    {d : Domain} {q : Literal} (hB : BoolSlot orig s) (hq : q.atom.slot = s) (hne : d ≠ [])
    (hsub : ∀ v ∈ d, v ∈ orig.getD s [])
    (hnc : ∀ w ∈ orig.getD s [], w ∉ d →
      ∃ e ∈ tr, e.literal.atom.slot = s ∧ e.literal.valueHolds w = false)
    (hfalse : ∀ v ∈ d, q.valueHolds v = false) : SemFalsifiedBefore orig tr q := by
  by_cases hall : ∀ w ∈ orig.getD s [], w ∈ d
  · left
    rw [litFalseAtRoot_iff, hq]
    intro v hv
    exact hfalse v (hall v hv)
  · have hex : ∃ w ∈ orig.getD s [], w ∉ d := by
      refine Classical.byContradiction fun hno => hall fun w hw => ?_
      refine Classical.byContradiction fun hwd => hno ⟨w, hw, hwd⟩
    obtain ⟨w, hwo, hwd⟩ := hex
    right
    obtain ⟨e, he, hes, hef⟩ := hnc w hwo hwd
    obtain ⟨wb, rfl⟩ := hB w hwo
    refine ⟨e, he, impliesP_of_boolOne (w := wb) hB hes
      (by simp [norm_atom_slot, Literal.negate, hq]) ?_ ?_⟩
    · rw [← valueHolds_bool]; exact hef
    · intro c _ hcw
      have hcd : Value.bool c ∈ d := by
        obtain ⟨x, hx⟩ : ∃ x, x ∈ d := by
          cases d with
          | nil => exact absurd rfl hne
          | cons a rest => exact ⟨a, List.mem_cons_self⟩
        obtain ⟨xb, rfl⟩ := hB x (hsub x hx)
        have hxw : xb ≠ wb := fun h => hwd (h ▸ hx)
        have : c = xb := by cases c <;> cases xb <;> cases wb <;> simp_all
        subst this; exact hx
      rw [truthAtBool_negate_norm, ← valueHolds_bool, hfalse _ hcd]
      rfl

theorem ncSlot_of_nc {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame} {s : Nat}
    (hle : F.2.length ≤ s) (hnc : NarrowingComplete tr orig F) :
    ∀ w ∈ orig.getD s [], w ∉ (Frame.domains F).getD s [] →
      ∃ e ∈ tr, e.literal.atom.slot = s ∧ e.literal.valueHolds w = false := by
  intro w hw hwn
  obtain ⟨i, hi⟩ : ∃ i, s = F.2.length + i := ⟨s - F.2.length, by omega⟩
  rw [domains_getD_rem F hle] at hwn
  have h1 : s - F.2.length = i := by omega
  rw [h1] at hwn
  have := hnc i w (by rw [← hi]; exact hw) hwn
  rw [← hi] at this
  exact this

theorem semFalsified_of_pinBool {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    {b : Bool} {e : TrailEntry} {q : Literal} (hB : BoolSlot orig s) (he : e ∈ tr)
    (hl : e.literal = posBool s b) (hq : q.atom.slot = s)
    (hfb : q.valueHolds (.bool b) = false) : SemFalsifiedBefore orig tr q := by
  have hes : e.literal.atom.slot = s := by rw [hl]; rfl
  right
  refine ⟨e, he, impliesP_of_boolOne (w := !b) hB hes
    (by rw [norm_atom_slot]; simpa [Literal.negate] using hq) ?_ ?_⟩
  · rw [hl]; cases b <;> simp [Literal.truthAtBool, posBool]
  · intro c _ hcw
    have : c = b := by cases c <;> cases b <;> simp_all
    subst this
    rw [truthAtBool_negate_norm, ← valueHolds_bool, hfb]; rfl


/-- Boolean atoms are false or undefined throughout an integer-only slot. -/
theorem litFalseAtRoot_boolEq_intSlot {orig : List Domain} {s : Nat}
    (hi : IntSlot orig s) (b pos : Bool) :
    litFalseAtRoot orig ⟨.boolEq s b, pos⟩ = true := by
  rw [litFalseAtRoot_iff]
  intro v hv
  obtain ⟨k, rfl⟩ := hi v hv
  simp [Literal.valueHolds]

theorem frameFalse_sem_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : ShapeTypedDomains orig) (hJ : FrameJ orig tr F) (hS : FrameShape orig F)
    (hpins : BoolPinsOn tr F.2)
    (hlive : ∀ d ∈ F.1, d ≠ []) {q : Literal}
    (himp : ((Frame.domains F).getD q.atom.slot []).all (fun v => !q.valueHolds v) = true) :
    SemFalsifiedBefore orig tr q := by
  have hfalse : ∀ v ∈ (Frame.domains F).getD q.atom.slot [], q.valueHolds v = false := by
    intro v hv
    have := List.all_eq_true.mp himp v hv
    simpa using this
  by_cases hD : (Frame.domains F).getD q.atom.slot [] = []
  · -- the slot is outside the box: root-false vacuously
    have hs : ¬ q.atom.slot < (Frame.domains F).length := fun hlt =>
      domains_getD_ne_nil hlive hlt hD
    refine Or.inl ((litFalseAtRoot_iff orig q).mpr fun v hv => ?_)
    exfalso
    have : orig.length ≤ q.atom.slot := by rw [← hS.1]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none this] at hv
    simp at hv
  · rcases slot_cases hint q.atom.slot with hIS | hB
    · obtain ⟨x, hx⟩ : ∃ x, x ∈ (Frame.domains F).getD q.atom.slot [] := by
        cases hh : (Frame.domains F).getD q.atom.slot [] with
        | nil => exact absurd hh hD
        | cons a rest => exact ⟨a, by simp⟩
      have hints : ∀ v ∈ (Frame.domains F).getD q.atom.slot [], ∃ k : Int, v = Value.int k :=
        fun v hv => hIS v (hJ.fits _ v hv)
      obtain ⟨k0, rfl⟩ := hints x hx
      obtain ⟨atom, pos⟩ := q
      simp only [Atom.slot] at hfalse hx hints hD ⊢
      have hE := hJ.expl
      cases atom with
      | boolEq s b => exact Or.inl (litFalseAtRoot_boolEq_intSlot hIS b pos)
      | intLe s k =>
          cases pos with
          | true =>
              obtain ⟨mn, hmn⟩ := domMinI_exists hx rfl
              obtain ⟨⟨x1, hx1, hx1v⟩, -⟩ := domMinI_spec hmn
              obtain ⟨k1, rfl⟩ := hints x1 hx1
              have hk1 : k1 = mn := by simpa [Value.intView] using hx1v
              subst hk1
              have := hfalse _ hx1
              simp [Literal.valueHolds, Value.intView] at this
              exact sf_posLe_mono ((hE s).1.2 k1 hmn) (by omega)
          | false =>
              obtain ⟨mx, hmx⟩ := domMaxI_exists hx rfl
              obtain ⟨⟨x2, hx2, hx2v⟩, -⟩ := domMaxI_spec hmx
              obtain ⟨k2, rfl⟩ := hints x2 hx2
              have hk2 : k2 = mx := by simpa [Value.intView] using hx2v
              subst hk2
              have := hfalse _ hx2
              simp [Literal.valueHolds, Value.intView] at this
              exact sf_negLe_mono ((hE s).1.1 k2 hmx) (by omega)
      | intNe s k =>
          cases pos with
          | true =>
              have hall : ∀ y ∈ (Frame.domains F).getD s [], y = Value.int k := by
                intro y hy
                obtain ⟨k', rfl⟩ := hints y hy
                have := hfalse _ hy
                simp [Literal.valueHolds, Value.intView] at this
                rw [this]
              have hxk : Value.int k0 = Value.int k := hall _ hx
              rw [hxk] at hx
              have hD1 : (Frame.domains F).getD s [] = [Value.int k] :=
                list_eq_singleton_of_nodup hx (domains_getD_nodup hS.2 s) hall
              exact (hE s).2.1 k hD1
          | false =>
              obtain ⟨mn, hmn⟩ := domMinI_exists hx rfl
              obtain ⟨mx, hmx⟩ := domMaxI_exists hx rfl
              obtain ⟨⟨x1, hx1, hx1v⟩, hallmn⟩ := domMinI_spec hmn
              obtain ⟨⟨x2, hx2, hx2v⟩, hallmx⟩ := domMaxI_spec hmx
              have hne : ∀ y ∈ (Frame.domains F).getD s [], ∀ k', y.intView = some k' → k' ≠ k := by
                intro y hy k' hyk hk'
                subst hk'
                obtain ⟨k'', rfl⟩ := hints y hy
                have := hfalse _ hy
                simp [Literal.valueHolds, Value.intView] at this hyk
                exact this hyk
              have hmnk : mn ≠ k := hne x1 hx1 mn hx1v
              have hmxk : mx ≠ k := hne x2 hx2 mx hx2v
              by_cases hlt : k < mn
              · exact sf_posLe_to_negNe ((hE s).1.2 mn hmn) (by omega)
              · by_cases hgt : mx < k
                · exact sf_negLe_to_negNe ((hE s).1.1 mx hmx) hgt
                · refine (hE s).2.2 k ⟨x1, hx1, mn, hx1v, by omega⟩ ⟨x2, hx2, mx, hx2v, by omega⟩ ?_
                  intro v hv hvk
                  exact hne v hv k hvk rfl
    · by_cases hlt : q.atom.slot < F.2.length
      · have hd := domains_getD_pre F hlt
        have hmem : F.2[q.atom.slot] ∈ orig.getD q.atom.slot [] :=
          hJ.fits _ _ (by rw [hd]; exact List.mem_cons_self)
        obtain ⟨b, hb⟩ := hB _ hmem
        obtain ⟨e, he, hel⟩ := hpins q.atom.slot b
          (by rw [List.getElem?_eq_getElem hlt, hb])
        refine semFalsified_of_pinBool hB he hel rfl ?_
        apply hfalse
        rw [hd, hb]; exact List.mem_cons_self
      · exact semFalsified_of_boolDom hB rfl hD (fun v hv => hJ.fits _ v hv)
          (ncSlot_of_nc (by omega) hJ.nc) hfalse


/-- The raw negative Boolean unit does not contain its normalized pivot.
This is an abstract clause witness, not a reachable public-run counterexample. -/
theorem raw_negative_boolean_unit_not_reason :
    ¬ SemReasonOK [[Value.bool false, Value.bool true]] []
      ⟨.boolEq 0 false, false⟩ [⟨.boolEq 0 false, false⟩] := by
  intro h
  have hp := h.1
  simp [Literal.norm] at hp

/-- A normalized database unit has the original exact pivot-membership
contract on mixed-domain frames; no reason-pivot definition is changed. -/
theorem dbUnit_sem_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig tr F) (hS : FrameShape orig F)
    (hpins : BoolPinsOn tr F.2) (hlive : ∀ d ∈ F.1, d ≠ []) {c : Clause} {l : Literal}
    (hcanon : ∀ q ∈ c, q.norm = q) (hrem : clauseRemaining F c = [l]) :
    SemReasonOK orig tr l c := by
  have hlmem : l ∈ c.filter (fun q => !literalImpossible F q) := by
    unfold clauseRemaining at hrem
    rw [hrem]
    exact List.mem_cons_self
  obtain ⟨hlc, _⟩ := List.mem_filter.mp hlmem
  refine ⟨by rw [hcanon l hlc]; exact hlc, fun q hq hne => ?_⟩
  have hqimp : literalImpossible F q = true := by
    cases hh : literalImpossible F q with
    | true => rfl
    | false =>
        exfalso
        have hm : q ∈ clauseRemaining F c := List.mem_filter.mpr ⟨hq, by simp [hh]⟩
        rw [hrem] at hm
        have hql : q = l := List.mem_singleton.mp hm
        subst q
        simp [litEqB] at hne
  exact frameFalse_sem_shape hshape hJ hS hpins hlive hqimp
theorem nextPruningEvent_implied_sem_shape {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    (hint : ShapeTypedDomains orig) (hJ : FrameJ orig bs.trail bs.frame) (hS : FrameShape orig bs.frame)
    (hpins : BoolPinsOn bs.trail bs.frame.2)
    (hcanon : ∀ c ∈ bs.learned, ∀ q ∈ c, q.norm = q)
    (hP : ∀ p ∈ props, PropSemContract orig p bs) {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl) :
    SemReasonOK orig bs.trail l c := by
  unfold nextPruningEvent at h
  cases hd : scanDatabase original bs.frame bs.learned with
  | stable =>
      rw [hd] at h
      by_cases hv : frameViewedB bs.frame = true
      · rw [if_pos hv] at h
        exact scanPropagators_implied hP (fun x hx => hx) h
      · rw [if_neg hv] at h; cases h
  | conflict cs => rw [hd] at h; cases h
  | implied l' c' lr' fl' =>
      rw [hd] at h
      simp only at h
      by_cases hl : frameLiveB bs.frame = true
      · rw [if_pos hl] at h
        simp only [PruningEvent.implied.injEq] at h
        obtain ⟨rfl, rfl, -, -⟩ := h
        obtain ⟨hmem, hrem⟩ := scanDatabase_implied hd
        have hlive : ∀ d ∈ bs.frame.1, d ≠ [] := by
          intro d hd' hnil
          have := List.all_eq_true.mp hl d hd'
          simp [hnil] at this
        exact dbUnit_sem_shape hint hJ hS hpins hlive (hcanon _ hmem) hrem
      · rw [if_neg hl] at h; cases h


end LeanFzn.Solver.UIP.LcgRunInv
