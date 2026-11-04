/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamilies.lean
U1a/U1b: the U0 `PropSemContract` for the registered propagators, family by
family, from the actual `run` equations.

## The frame-explanation invariant (a PREMISE, not proved here)
`BoundsExpl orig trail doms` (`bs.BoundsExplained orig`): every domain
extremum of the box `doms` is semantically explained by the trail or the root:
for the maximum `mx` of slot `s`, the literal `s > mx` is semantically
falsified (`SemFalsifiedBefore`), for the minimum `mn` the literal `s ≤ mn-1`
is. This is the "bound-cause hygiene" of `Propagate.lean`; it is what R1d's
`syncAll` establishes (lower bound, upper bound and fixing literals of every
slot are pushed). It is NOT proved along runs in this module (that is the
`syncAll` coverage fact for U1c); every theorem below is stated relative to it.
`PinsExpl` is the Boolean-pin analogue. Known limit: `impliesP` never lets a
Boolean trail literal imply an integer literal, so the premise can only hold
for integer-sorted slots (or via root facts).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgContract
import LeanFzn.Legacy.Solver.UIP.Proofs.DomExplained
import LeanFzn.Legacy.Solver.UIP.Proofs.ExplainedFamilies
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract

namespace LeanFzn.Solver.UIP.LcgFamilies

variable {leaf : Assignment → Bool}

/-! ## 1. Literal monotonicity -/

theorem impliesP_posLe_mono {orig : List Domain} {t : Literal} {s : Nat} {k k' : Int}
    (h : impliesP orig t (posLe s k) = true) (hk : k ≤ k') : impliesP orig t (posLe s k') = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;> simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at h ⊢ <;> simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (right; exact ⟨h1, by omega⟩))
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (first | (left; exact ⟨h1, by omega⟩) | (right; exact ⟨h1, by omega⟩)))
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, posLe] at this ⊢ <;> omega

theorem impliesP_negLe_mono {orig : List Domain} {t : Literal} {s : Nat} {k k' : Int}
    (h : impliesP orig t (negLe s k) = true) (hk : k' ≤ k) : impliesP orig t (negLe s k') = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;> simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at h ⊢ <;> simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (right; exact ⟨h1, by omega⟩))
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (first | (left; exact ⟨h1, by omega⟩) | (right; exact ⟨h1, by omega⟩)))
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, negLe] at this ⊢ <;> omega

theorem litFalseAtRoot_negLe_mono {orig : List Domain} {s : Nat} {k k' : Int}
    (h : litFalseAtRoot orig (negLe s k) = true) (hk : k ≤ k') :
    litFalseAtRoot orig (negLe s k') = true := by
  simp only [litFalseAtRoot, List.all_eq_true] at h ⊢
  intro v hv
  have := h v hv
  simp [negLe, Atom.evalAtValue] at this ⊢
  cases hi : Value.intView v <;> simp [hi] at this ⊢
  omega

theorem litFalseAtRoot_posLe_mono {orig : List Domain} {s : Nat} {k k' : Int}
    (h : litFalseAtRoot orig (posLe s k) = true) (hk : k' ≤ k) :
    litFalseAtRoot orig (posLe s k') = true := by
  simp only [litFalseAtRoot, List.all_eq_true] at h ⊢
  intro v hv
  have := h v hv
  simp [posLe, Atom.evalAtValue] at this ⊢
  cases hi : Value.intView v <;> simp [hi] at this ⊢
  omega

theorem sf_negLe_mono {orig : List Domain} {pre : List TrailEntry} {s : Nat} {k k' : Int}
    (h : SemFalsifiedBefore orig pre (negLe s k)) (hk : k ≤ k') :
    SemFalsifiedBefore orig pre (negLe s k') := by
  rcases h with h | ⟨e, he, hi⟩
  · exact Or.inl (litFalseAtRoot_negLe_mono h hk)
  · exact Or.inr ⟨e, he, impliesP_posLe_mono (s := s) hi hk⟩

theorem sf_posLe_mono {orig : List Domain} {pre : List TrailEntry} {s : Nat} {k k' : Int}
    (h : SemFalsifiedBefore orig pre (posLe s k)) (hk : k' ≤ k) :
    SemFalsifiedBefore orig pre (posLe s k') := by
  rcases h with h | ⟨e, he, hi⟩
  · exact Or.inl (litFalseAtRoot_posLe_mono h hk)
  · exact Or.inr ⟨e, he, impliesP_negLe_mono (s := s) hi hk⟩

/-! ## 2. The result contract and the frame invariant -/

/-- The semantic contract of one propagation result. -/
def ResSem (orig : List Domain) (pre : List TrailEntry) : PropagationResult → Prop
  | .stable => True
  | .implied l r => SemReasonOK orig pre l r.clause
  | .conflict c => ClauseSemFalsifiedR orig pre c

theorem propSem_iff {orig : List Domain} {p : Propagator} {bs : BranchState leaf} :
    PropSemContract orig p bs ↔ ResSem orig bs.trail (p.run (frameState bs.frame)) := by
  constructor
  · rintro ⟨h1, h2⟩
    generalize hr : p.run (frameState bs.frame) = r
    cases r with
    | stable => trivial
    | implied l r => exact h1 l r hr
    | conflict c => exact h2 c hr
  · intro h
    constructor
    · intro l r hr; rw [hr] at h; exact h
    · intro c hr; rw [hr] at h; exact h

/-- THE FRAME-EXPLANATION INVARIANT (bounds): every extremum of every slot
domain is semantically explained by the trail or the root. -/
def BoundsExpl (orig : List Domain) (pre : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s, (∀ mx, domMaxI (doms.getD s Dom.empty) = some mx → SemFalsifiedBefore orig pre (negLe s mx)) ∧
       (∀ mn, domMinI (doms.getD s Dom.empty) = some mn → SemFalsifiedBefore orig pre (posLe s (mn - 1)))

/-- Boolean absence: a Boolean value missing from a slot domain makes the
corresponding Boolean literal semantically falsified (covers pins: a pin to
`!b` removes `b`). -/
def AbsentExpl (orig : List Domain) (pre : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s b, valueMemB (.bool b) (slotEnum doms s) = false →
    SemFalsifiedBefore orig pre (posBool s b)

/-- Integer fixing: a singleton integer domain falsifies `s ≠ c`. -/
def FixExpl (orig : List Domain) (pre : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s c, Dom.enum (doms.getD s Dom.empty) = [.int c] →
    SemFalsifiedBefore orig pre (posNe s c)

/-- The frame-explanation invariant at a branch state. -/
structure FrameExplained (orig : List Domain) (bs : BranchState leaf) : Prop where
  bounds : BoundsExpl orig bs.trail (Frame.domains bs.frame)
  absent : AbsentExpl orig bs.trail (Frame.domains bs.frame)
  fix : FixExpl orig bs.trail (Frame.domains bs.frame)

/-- Pins are derived from absence. -/
theorem pins_of_absent {orig : List Domain} {pre : List TrailEntry} {doms : List Domain}
    (hA : AbsentExpl orig pre doms) {s : Nat} {b : Bool}
    (h : domBoolPin doms s b = true) : SemFalsifiedBefore orig pre (posBool s (!b)) := by
  have := domBoolPin_eq h
  apply hA
  rw [this]
  cases b <;> rfl

theorem firstEvent_sem {orig : List Domain} {pre : List TrailEntry}
    {rs : List PropagationResult} (h : ∀ r ∈ rs, ResSem orig pre r) :
    ResSem orig pre (firstEvent rs) := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
      cases r with
      | stable => exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
      | implied l c => exact h _ List.mem_cons_self
      | conflict c => exact h _ List.mem_cons_self

/-- Int-atom literal: the only literal with this normal form is itself. -/
theorem eq_of_norm_intLe {q : Literal} {s : Nat} {k : Int} {b : Bool}
    (h : q.norm = ⟨.intLe s k, b⟩) : q = ⟨.intLe s k, b⟩ := by
  obtain ⟨a, p⟩ := q
  cases a <;> cases p <;> simp_all [Literal.norm]

/-- Reason contract for an int-atom pivot: all other literals falsified. -/
theorem reasonOK_of_int {orig : List Domain} {pre : List TrailEntry} {l : Literal}
    {c : Clause} {s : Nat} {k : Int} {b : Bool} (hl : l = ⟨.intLe s k, b⟩) (hmem : l ∈ c)
    (hc : ∀ q ∈ c, q ≠ l → SemFalsifiedBefore orig pre q) :
    SemReasonOK orig pre l c := by
  subst hl
  refine ⟨by simpa [Literal.norm] using hmem, fun q hq hne => hc q hq ?_⟩
  intro hq'
  subst hq'
  simp [litEqB] at hne

theorem narrowHi_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) {s : Nat} {hi : Int} {ng : Clause}
    (hmem : posLe s hi ∈ ng)
    (hc : ∀ q ∈ ng, q ≠ posLe s hi → SemFalsifiedBefore orig pre q) :
    ResSem orig pre (narrowHi st s hi ng) := by
  unfold narrowHi
  cases hmn : domMinI (st.domains.getD s Dom.empty) with
  | none => trivial
  | some mn =>
    cases hmx : domMaxI (st.domains.getD s Dom.empty) with
    | none => trivial
    | some mx =>
      simp only
      split
      · rename_i hgt
        intro q hq
        by_cases hqh : q = posLe s hi
        · subst hqh
          exact sf_posLe_mono ((hB s).2 mn hmn) (by omega)
        · exact hc q hq hqh
      · split
        · exact reasonOK_of_int rfl hmem hc
        · trivial

theorem narrowLo_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) {s : Nat} {lo : Int} {ng : Clause}
    (hmem : negLe s (lo - 1) ∈ ng)
    (hc : ∀ q ∈ ng, q ≠ negLe s (lo - 1) → SemFalsifiedBefore orig pre q) :
    ResSem orig pre (narrowLo st s lo ng) := by
  unfold narrowLo
  cases hmn : domMinI (st.domains.getD s Dom.empty) with
  | none => trivial
  | some mn =>
    cases hmx : domMaxI (st.domains.getD s Dom.empty) with
    | none => trivial
    | some mx =>
      simp only
      split
      · rename_i hlt
        intro q hq
        by_cases hqh : q = negLe s (lo - 1)
        · subst hqh
          exact sf_negLe_mono ((hB s).1 mx hmx) (by omega)
        · exact hc q hq hqh
      · split
        · exact reasonOK_of_int rfl hmem hc
        · trivial


/-- Boolean head. -/
theorem reasonOK_of_bool {orig : List Domain} {pre : List TrailEntry} {s : Nat} {b : Bool}
    {c : Clause} (hmem : posBool s b ∈ c)
    (hc : ∀ q ∈ c, q ≠ posBool s b → SemFalsifiedBefore orig pre q) :
    SemReasonOK orig pre (posBool s b) c := by
  refine ⟨by simpa [posBool_norm] using hmem, fun q hq hne => hc q hq ?_⟩
  intro hq'
  subst hq'
  simp [litEqB] at hne

theorem implyBool_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hA : AbsentExpl orig pre st.domains) {s : Nat} {b : Bool} {ng : Clause}
    (hmem : posBool s b ∈ ng)
    (hc : ∀ q ∈ ng, q ≠ posBool s b → SemFalsifiedBefore orig pre q) :
    ResSem orig pre (implyBool st s b ng) := by
  unfold implyBool
  split
  · split
    · trivial
    · exact reasonOK_of_bool hmem hc
  · rename_i hn
    intro q hq
    by_cases hqh : q = posBool s b
    · subst hqh; exact hA s b (by simpa using hn)
    · exact hc q hq hqh

end LeanFzn.Solver.UIP.LcgFamilies
