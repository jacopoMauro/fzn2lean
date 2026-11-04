/-
File: LeanFzn/Solver/UIP/Proofs/LcgNoBoolEmit.lean

DL (decide-site liveness), part 1: on an integer-valued state no `lcgFamB` raw propagator ever
implies a Boolean-atom literal. Boolean atoms are only emitted behind a `domBoolPin` / `.bool`
membership guard, which an integer-valued state falsifies.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEmissionTyped
import LeanFzn.Solver.Propagation.Proofs.PropCheck
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgFamilies
open LeanFzn.Solver.UIP.LcgEmissionTyped

namespace LeanFzn.Solver.UIP.LcgNoBool

/-- A literal over an order/removal atom (not a Boolean pin). -/
def NoBoolAtom (l : Literal) : Prop := ∀ s b, l.atom ≠ Atom.boolEq s b

/-- Every domain value of the state is an integer. -/
def IntState (st : State) : Prop := ∀ d ∈ st.domains, ∀ v ∈ d, ∃ k : Int, v = Value.int k

/-- The bounds arm's Boolean-domain guard contradicts an integer-only
    state: the guarded slot carries a Boolean, so the state is not
    all-integer (the widened order disjunction's `posBool` case). -/
theorem not_intState_of_domBoolOnly {st : State} {r : Nat}
    (h : domBoolOnlyB (slotEnum st.domains r) = true) : ¬ IntState st := by
  intro hI
  obtain ⟨hlen0, hall⟩ := domBoolOnlyB_eq h
  have hne : st.domains.getD r Dom.empty ≠ Dom.empty := by
    intro h0
    have hlen0' : 0 < (Dom.enum (st.domains.getD r Dom.empty)).length := hlen0
    rw [h0, Dom.enum_empty] at hlen0'
    simp at hlen0'
  have hlt : r < st.domains.length := by
    by_cases hlt' : r < st.domains.length
    · exact hlt'
    · exact absurd (getD_nil_of_length_le hlt') hne
  obtain ⟨b, hb⟩ := hall ((slotEnum st.domains r)[0])
    (List.getElem_mem hlen0)
  have hmemE : (Value.bool b) ∈ Dom.enum (st.domains.getD r Dom.empty) := by
    rw [← hb]
    exact List.getElem_mem hlen0
  obtain ⟨k, hk⟩ := hI (st.domains.getD r Dom.empty) (getD_mem_of_lt hlt)
    (.bool b) ((DomainLike.mem_iff _ _).mpr (by rw [domElems_eq_enum]; exact hmemE))
  exact absurd hk (by simp)

/-- An emission never implies a Boolean-atom literal. -/
def ImpliedNB (res : PropagationResult) : Prop := ∀ l r, res = .implied l r → NoBoolAtom l

theorem noBoolAtom_posLe (s : Nat) (k : Int) : NoBoolAtom (posLe s k) := by
  intro s' b h; simp [posLe] at h

theorem noBoolAtom_negLe (s : Nat) (k : Int) : NoBoolAtom (negLe s k) := by
  intro s' b h; simp [negLe] at h

theorem noBoolAtom_posNe (s : Nat) (k : Int) : NoBoolAtom (posNe s k) := by
  intro s' b h; simp [posNe] at h

theorem impliedNB_stable : ImpliedNB .stable := fun _ _ h => by cases h

theorem impliedNB_conflict (c : Clause) : ImpliedNB (.conflict c) := fun _ _ h => by cases h

theorem intState_getD {st : State} (h : IntState st) (s : Nat) :
    ∀ v ∈ slotEnum st.domains s, ∃ k : Int, v = Value.int k := by
  intro v hv
  have hv' : v ∈ Dom.enum (st.domains.getD s Dom.empty) := hv
  rw [List.getD_eq_getElem?_getD] at hv'
  cases hs : st.domains[s]? with
  | none => rw [hs] at hv'; simp [Dom.enum_empty] at hv'
  | some d =>
      rw [hs] at hv'
      have hvD : v ∈ d := (DomainLike.mem_iff _ v).mpr (by
        rw [domElems_eq_enum]
        simpa using hv')
      exact h d (List.mem_of_getElem? hs) v hvD

theorem not_domBoolPin {st : State} (h : IntState st) {s : Nat} {b : Bool} :
    domBoolPin st.domains s b ≠ true := by
  intro hp
  have := domBoolPin_eq hp
  obtain ⟨k, hk⟩ := intState_getD h s (.bool b) (by rw [this]; simp)
  cases hk

theorem impliedNB_narrowHi (st : State) (s : Nat) (hi : Int) (ng : Clause) :
    ImpliedNB (narrowHi st s hi ng) := fun l r h => by
  obtain ⟨rfl, -⟩ := narrowHi_implied_inv h; exact noBoolAtom_posLe _ _

theorem impliedNB_narrowLo (st : State) (s : Nat) (lo : Int) (ng : Clause) :
    ImpliedNB (narrowLo st s lo ng) := fun l r h => by
  obtain ⟨rfl, -⟩ := narrowLo_implied_inv h; exact noBoolAtom_negLe _ _

theorem impliedNB_firstEvent (rs : List PropagationResult) (h : ∀ r ∈ rs, ImpliedNB r) :
    ImpliedNB (firstEvent rs) := by
  rcases firstEvent_mem rs _ rfl with hs | hm
  · rw [hs]; exact impliedNB_stable
  · exact h _ hm

theorem nb_constEq (st : State) (h : IntState st) (i : Nat) (v : Value) :
    ImpliedNB (LeanFzn.Solver.Propagation.propConstEq st i v) := by
  match v with
  | .int k =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      refine impliedNB_firstEvent _ ?_
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · exact impliedNB_narrowHi _ _ _ _
      · exact impliedNB_narrowLo _ _ _ _
  | .bool b =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      by_cases h1 : valueMemB (Value.bool b) (Dom.enum (st.domains.getD i Dom.empty)) = true
      · exfalso
        obtain ⟨k, hk⟩ := intState_getD h i (.bool b) (valueMemB_iff.mp h1)
        cases hk
      · rw [if_neg h1]; exact impliedNB_conflict _
  | .setOfInt _ => simp only [LeanFzn.Solver.Propagation.propConstEq]; exact impliedNB_stable
  | .array _ => simp only [LeanFzn.Solver.Propagation.propConstEq]; exact impliedNB_stable

theorem nb_boolNot {st : State} (h : IntState st) (i j : Nat) : ImpliedNB (propBoolNot st i j) := by
  rcases propBoolNot_emit (res := propBoolNot st i j) rfl with
    ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | hs
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · rw [hs]; exact impliedNB_stable

theorem nb_boolAnd {st : State} (h : IntState st) (i j k : Nat) :
    ImpliedNB (propBoolAnd st i j k) := by
  rcases propBoolAnd_emit (res := propBoolAnd st i j k) rfl with
    ⟨hp, -, -⟩ | ⟨hp, -, -⟩ | ⟨hp, -, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | hs
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · rw [hs]; exact impliedNB_stable

theorem nb_boolOr {st : State} (h : IntState st) (i j k : Nat) :
    ImpliedNB (propBoolOr st i j k) := by
  rcases propBoolOr_emit (res := propBoolOr st i j k) rfl with
    ⟨hp, -, -⟩ | ⟨hp, -, -⟩ | ⟨hp, -, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | hs
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · exact absurd hp (not_domBoolPin h)
  · rw [hs]; exact impliedNB_stable

theorem nb_le (st : State) (i j : Nat) : ImpliedNB (propLe st i j) := by
  unfold propLe
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
  · exact impliedNB_stable

theorem nb_lt (st : State) (i j : Nat) : ImpliedNB (propLt st i j) := by
  unfold propLt
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
  · exact impliedNB_stable

theorem nb_eq (st : State) (i j : Nat) : ImpliedNB (propEq st i j) := by
  unfold propEq
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
  · exact impliedNB_stable

theorem nb_plus (st : State) (i j k : Nat) : ImpliedNB (propPlus st i j k) := by
  unfold propPlus
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
  · exact impliedNB_stable

theorem nb_ne (st : State) (i j : Nat) : ImpliedNB (propNe st i j) := by
  intro l r h
  rcases propNe_implied_inv h with
    ⟨x, c, -, rfl, -⟩ | ⟨y, c, -, rfl, -⟩
  · exact noBoolAtom_posNe _ _
  · exact noBoolAtom_posNe _ _

theorem nb_allDiff (st : State) (is : List Nat) : ImpliedNB (propAllDiffLCG st is) := by
  intro l r h
  obtain ⟨i, j, c, -, hl, -⟩ := propAllDiffLCG_implied_inv h
  subst hl
  exact noBoolAtom_posNe _ _

/-- PLAN L3: `propMin` never implies a Boolean-atom literal: its four
    narrowings imply order literals only. -/
theorem nb_min (st : State) (i j k : Nat) : ImpliedNB (propMin st i j k) := by
  unfold propMin
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
  · exact impliedNB_stable

/-- PLAN L3: the `maxSlot` twin of `nb_min`. -/
theorem nb_max (st : State) (i j k : Nat) : ImpliedNB (propMax st i j k) := by
  unfold propMax
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
  · exact impliedNB_stable

/-- PLAN C9c: `propMinGen` never implies a Boolean-atom literal: its two
    attained-operand arms imply order literals only. -/
theorem nb_minGen (st : State) (os : List DomIntArg) (r : DomIntArg) :
    ImpliedNB (propMinGen st os r) := by
  unfold propMinGen
  split
  case h_1 => exact impliedNB_stable
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      refine impliedNB_firstEvent _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact impliedNB_narrowLo _ _ _ _
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact impliedNB_narrowHi _ _ _ _
    case h_2 => exact impliedNB_stable

/-- PLAN C9c: the `maxGen` twin of `nb_minGen`. -/
theorem nb_maxGen (st : State) (os : List DomIntArg) (r : DomIntArg) :
    ImpliedNB (propMaxGen st os r) := by
  unfold propMaxGen
  split
  case h_1 => exact impliedNB_stable
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      refine impliedNB_firstEvent _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact impliedNB_narrowLo _ _ _ _
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact impliedNB_narrowHi _ _ _ _
    case h_2 => exact impliedNB_stable

/-- PLAN L6: `propTimes` never implies a Boolean-atom literal: its two
    corner and eight guarded sign narrowings imply order literals only. -/
theorem nb_times (st : State) (i j k : Nat) : ImpliedNB (propTimes st i j k) := by
  unfold propTimes
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    rcases times_sign_arm hr with hcorner | hcorner |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩
    · rw [hcorner]; exact impliedNB_narrowLo _ _ _ _
    · rw [hcorner]; exact impliedNB_narrowHi _ _ _ _
    · rw [hr]; exact impliedNB_narrowLo _ _ _ _
    · rw [hr]; exact impliedNB_narrowHi _ _ _ _
    · rw [hr]; exact impliedNB_narrowHi _ _ _ _
    · rw [hr]; exact impliedNB_narrowLo _ _ _ _
    · rw [hr]; exact impliedNB_narrowLo _ _ _ _
    · rw [hr]; exact impliedNB_narrowHi _ _ _ _
    · rw [hr]; exact impliedNB_narrowHi _ _ _ _
    · rw [hr]; exact impliedNB_narrowLo _ _ _ _
  · exact impliedNB_stable
/-- PLAN L7: `propAbs` never implies a Boolean-atom literal: its five
    narrowings imply order literals on `i`/`k` only. -/
theorem nb_abs (st : State) (i k : Nat) : ImpliedNB (propAbs st i k) := by
  unfold propAbs
  split
  · refine impliedNB_firstEvent _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowHi _ _ _ _
    · exact impliedNB_narrowLo _ _ _ _
  · exact impliedNB_stable

/-- PLAN L7: `propDiv` never implies a Boolean-atom literal: it reports
    the zero-divisor conflict or emits a `narrowLo`/`narrowHi` result,
    whose implied literals are order literals. -/
theorem nb_div (st : State) (o₁ o₂ r : DomIntArg) :
    ImpliedNB (propDiv st o₁ o₂ r) := by
  unfold propDiv
  split
  · split
    · exact impliedNB_conflict _
    · split
      · split
        · refine impliedNB_firstEvent _ ?_
          intro r' hr'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
          rcases hr' with rfl | rfl
          · exact impliedNB_narrowLo _ _ _ _
          · exact impliedNB_narrowHi _ _ _ _
        · exact impliedNB_stable
      · exact impliedNB_stable
  · exact impliedNB_stable

/-- PLAN L7: `propMod`, the `modGen` twin of `nb_div`. -/
theorem nb_mod (st : State) (o₁ o₂ r : DomIntArg) :
    ImpliedNB (propMod st o₁ o₂ r) := by
  unfold propMod
  split
  · split
    · exact impliedNB_conflict _
    · split
      · split
        · refine impliedNB_firstEvent _ ?_
          intro r' hr'
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
          rcases hr' with rfl | rfl
          · exact impliedNB_narrowLo _ _ _ _
          · exact impliedNB_narrowHi _ _ _ _
        · exact impliedNB_stable
      · exact impliedNB_stable
  · exact impliedNB_stable


theorem nb_linLe (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    ImpliedNB (propLinLe2 st coeffs is b) := by
  rcases propLinLe2_emission_inv (res := propLinLe2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, -, -, -, -, hres⟩ | ⟨m, i, rest, lr, -, -, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, -, -, -, -, -, hres⟩ | ⟨m, i, rest, lr, c, -, -, -, -, -, hres⟩
  · rw [hs]; exact impliedNB_stable
  · rw [hres]; exact impliedNB_narrowHi _ _ _ _
  · rw [hres]; exact impliedNB_narrowLo _ _ _ _
  · rw [hres]; exact impliedNB_narrowHi _ _ _ _
  · rw [hres]; exact impliedNB_narrowLo _ _ _ _

theorem nb_linEq (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    ImpliedNB (propLinEq2 st coeffs is b) := by
  rcases propLinEq2_emission_inv (res := propLinEq2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, -, -, -, -, hres⟩ | ⟨m, i, rest, hr, -, -, -, -, hres⟩ |
    ⟨m, i, rest, lr, -, -, -, -, hres⟩ | ⟨m, i, rest, hr, -, -, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, -, -, -, -, -, hres⟩ | ⟨m, i, rest, hr, c, -, -, -, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, -, -, -, -, -, hres⟩ | ⟨m, i, rest, hr, c, -, -, -, -, -, hres⟩
  · rw [hs]; exact impliedNB_stable
  all_goals first
    | (rw [hres]; exact impliedNB_narrowHi _ _ _ _)
    | (rw [hres]; exact impliedNB_narrowLo _ _ _ _)

/-- PLAN G1-B: on an integer-valued state the `bool2intSlot` channel
    propagator implies only non-Boolean literals: the pinned arms need a
    `domBoolPin`, the `implyBool` arms need a Boolean present in the source
    domain, and the remaining implied arms are unit `posNe` removals. -/
theorem nb_bool2int (st : State) (h : IntState st) (i k : Nat) :
    ImpliedNB (propBool2intSlot st i k) := by
  rcases propBool2intSlot_cases st i k with hstable | ⟨hpt, w, hfb, he⟩ |
    ⟨hpf, w, hfb, he⟩ | ⟨hnb, he⟩ | ⟨hd0, he⟩ | ⟨hd1, he⟩ |
    ⟨w, hfb, he⟩ | ⟨mx, mn, hmx, hmn, hlt, he⟩ | ⟨mx, mn, hmx, hmn, hgt, he⟩
  · rw [hstable]; exact impliedNB_stable
  · exact absurd hpt (not_domBoolPin h)
  · exact absurd hpf (not_domBoolPin h)
  · rw [he]; exact impliedNB_conflict _
  · rw [he]
    unfold implyBool
    have hno : valueMemB (.bool false) (slotEnum st.domains i) = false := by
      rw [Bool.eq_false_iff]
      intro hv
      obtain ⟨c, hc⟩ := intState_getD h i (.bool false) (valueMemB_iff.mp hv)
      cases hc
    rw [if_neg (by rw [hno]; decide)]
    exact impliedNB_conflict _
  · rw [he]
    unfold implyBool
    have hno : valueMemB (.bool true) (slotEnum st.domains i) = false := by
      rw [Bool.eq_false_iff]
      intro hv
      obtain ⟨c, hc⟩ := intState_getD h i (.bool true) (valueMemB_iff.mp hv)
      cases hc
    rw [if_neg (by rw [hno]; decide)]
    exact impliedNB_conflict _
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe k w
  · rw [he]; exact impliedNB_conflict _
  · rw [he]; exact impliedNB_conflict _

/-- PLAN G1c: on an integer-valued state the constant-table element
    propagator implies only removal literals (`posNe` heads), so no
    Boolean atom. -/
theorem nb_arrayIntElement (st : State) (_h : IntState st) (xs : List Int)
    (i k : Nat) : ImpliedNB (propArrayIntElement st xs i k) := by
  rcases propArrayIntElement_cases st xs i k with hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, v, w, hidx, hent, hfb, he⟩ | ⟨v, idx, hk, hfb, he⟩ |
    ⟨idx, hfb, he⟩ | ⟨idx, v, hg, hfb, hent, he⟩
  · rw [hstable]; exact impliedNB_stable
  · rw [he]; exact impliedNB_conflict _
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe k w
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx

/-- On an integer-valued state an `implyBool` emission is never an implied
    Boolean atom (the presence premise contradicts an all-integer domain). -/
theorem impliedNB_implyBool (st : State) (h : IntState st) (s : Nat) (b : Bool)
    (ng : Clause) : ImpliedNB (implyBool st s b ng) := by
  cases hres : implyBool st s b ng with
  | stable => exact impliedNB_stable
  | conflict c => exact impliedNB_conflict c
  | implied l r =>
      obtain ⟨hmem, -, -⟩ := implyBool_implied_inv_mem hres
      obtain ⟨c, hc⟩ := intState_getD h s (.bool b) (valueMemB_iff.mp hmem)
      exact absurd hc (by simp)

/-- PLAN §3.3: on an integer-valued state the variable-table element
    propagator implies only removal literals (`posNe` heads), so no
    Boolean atom. -/
theorem nb_arrayVarIntElement (st : State) (_h : IntState st) (is : List Nat)
    (i k : Nat) : ImpliedNB (propArrayVarIntElement st is i k) := by
  rcases propArrayVarIntElement_cases st is i k with
    hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, j, w, hidx, hent, hfb, he⟩ |
    ⟨idx, j, w, hidx, hent, hfbK, hfb, he⟩ |
    ⟨idx, v, hk, hnone, hfb, he⟩ |
    ⟨idx, v, j, hk, hent, hvm, hfb, he⟩ |
    ⟨idx, hnone, hfb, he⟩ |
    ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, he⟩ |
    ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, he⟩ |
    ⟨idx, j, w, hent, hdj, hvm, hfb, he⟩ |
    ⟨w, hfbOut, hfbBelow, hfbAbove, hfbSingle, hfbw, he⟩
  · rw [hstable]; exact impliedNB_stable
  · rw [he]; exact impliedNB_conflict _
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe k w
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe j w
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe i idx
  · rw [he]
    exact fun l r hr => by
      cases hr
      exact noBoolAtom_posNe k w

/-- A Boolean-only slot contradicts an integer-valued state. -/
theorem domBoolOnlyB_false_of_intState {st : State} (h : IntState st) (s : Nat) :
    domBoolOnlyB (slotEnum st.domains s) = false := by
  by_cases hb : domBoolOnlyB (slotEnum st.domains s) = true
  · obtain ⟨hlen0, hall⟩ := domBoolOnlyB_eq hb
    obtain ⟨b, hbval⟩ := hall ((slotEnum st.domains s)[0])
      (List.getElem_mem hlen0)
    obtain ⟨k, hk⟩ := intState_getD h s (.bool b)
      (by rw [← hbval]; exact List.getElem_mem hlen0)
    cases hk
  · exact Bool.eq_false_iff.mpr hb

/-- The Boolean element guard fails on an integer-valued state. -/
theorem avbeGuardB_false_of_intState {st : State} (h : IntState st)
    (is : List Nat) (i k : Nat) : avbeGuardB st is i k = false := by
  unfold avbeGuardB
  rw [domBoolOnlyB_false_of_intState h k]
  simp

/-- PLAN §3.3 item 2: on an integer-valued state the variable-table
    Boolean element propagator is `.stable` (its Boolean target guard
    cannot hold), so it implies nothing. -/
theorem propArrayVarBoolElement_stable_of_intState {st : State}
    (h : IntState st) (is : List Nat) (i k : Nat) :
    propArrayVarBoolElement st is i k = .stable := by
  unfold propArrayVarBoolElement
  by_cases halias : i = k
  · rw [if_pos halias]
  · rw [if_neg halias]
    by_cases htab : (is.elem i || is.elem k) = true
    · rw [if_pos htab]
    · rw [if_neg htab]
      by_cases hnodup : decide is.Nodup = false
      · rw [if_pos hnodup]
      · rw [if_neg hnodup, avbeGuardB_false_of_intState h is i k]
        rfl

/-- PLAN §3.3 item 2: on an integer-valued state the variable-table
    Boolean element propagator implies nothing. -/
theorem nb_arrayVarBoolElement (st : State) (h : IntState st) (is : List Nat)
    (i k : Nat) : ImpliedNB (propArrayVarBoolElement st is i k) := by
  rw [propArrayVarBoolElement_stable_of_intState h is i k]
  exact impliedNB_stable

/-- PLAN G1e: on an integer-valued state the array-Boolean conjunction
    propagator implies no Boolean atom: every round is an `implyBool`
    emission. -/
theorem nb_arrayBoolAnd (st : State) (h : IntState st) (is : List Nat)
    (k : Nat) : ImpliedNB (propArrayBoolAnd st is k) := by
  rcases propArrayBoolAnd_cases st is k with
    hstable | ⟨hall, he⟩ | ⟨i, hfb, he⟩ | ⟨hk, i, hfb, he⟩ |
    ⟨hkf, i, his, hb, he⟩
  · rw [hstable]; exact impliedNB_stable
  · rw [he]; exact impliedNB_implyBool st h k true _
  · rw [he]; exact impliedNB_implyBool st h k false _
  · rw [he]; exact impliedNB_implyBool st h i true _
  · rw [he]; exact impliedNB_implyBool st h i false _

/-- **No Boolean-atom implication of the raw `lcgFamB` kit on an integer-valued state.** -/
theorem impliedNB_of_families {dcs : List DomConstraint}
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true) {p : Propagator}
    (hp : p ∈ dcs.filterMap propagatorOfProved) {st : State} (hst : IntState st) :
    ImpliedNB (p.run st) := by
  obtain ⟨dc, hdc, hprop⟩ := LeanFzn.Solver.Propagation.propagatorsOfProved_mem hp
  have hf := hfam dc hdc
  cases dc with
  | timesSlot i j k =>
      -- PLAN L6: the registered propagator is the bound propagator
      -- `propTimes`; its implied literals are order literals only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_times st i j k
  | minSlot i j k =>
      -- PLAN L3: the registered propagator is `propMin`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_min st i j k
  | maxSlot i j k =>
      -- PLAN L3: the registered propagator is `propMax`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_max st i j k
  | absSlot i k =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propAbs`; its implied literals are order literals.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_abs st i k
  | linNe coeffs is b =>
      -- PLAN L2: the registered propagator is `propLinNe`; its implied literal
      -- is a value-removal literal `posNe`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l r h => by
        obtain ⟨-, c, m, -, -, -, -, hl, -⟩ :=
          LeanFzn.Solver.Propagation.propLinNe_implied_inv h
        rw [hl]
        exact noBoolAtom_posNe _ _
  | eqReifSlot i j r =>
      -- PLAN L4: the heads are `propEq`/`propNe`'s literals; the pin
      -- escapes sit in the clause only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs (h : propEqReifSlot st i j r = _) => by
        rcases LeanFzn.Solver.Propagation.propEqReifSlot_cases st i j r with
          ⟨-, he⟩ | ⟨-, -, he⟩ | he
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ :=
            LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_eq st i j l rs0 hres
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ :=
            LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_ne st i j l rs0 hres
        · rw [he] at h; cases h
  | leReifSlot i j r =>
      -- PLAN G1: the pinned delegations emit `propLe`/`propLt`'s order
      -- literals only; the unpinned bounds arm's `posBool` pivot is excluded
      -- by its Boolean-domain guard, which contradicts the integer state.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs (h : propLeReifSlotB st i j r = _) => by
        rcases LeanFzn.Solver.Propagation.propLeReifSlotB_cases st i j r with
          ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ := LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_le st i j l rs0 hres
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ := LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_lt st j i l rs0 hres
        · rw [he] at h
          rcases LeanFzn.Solver.Propagation.propLeReifB_emission_inv h with
            hstable | ⟨-, hb, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ |
            ⟨-, hb, -, -, -, -, -, -, -, -, -, -, -, -, -⟩
          · cases hstable
          · exact absurd hst (not_intState_of_domBoolOnly hb)
          · exact absurd hst (not_intState_of_domBoolOnly hb)
  | neReifSlot i j r =>
      -- PLAN L4: the heads are `propNe`/`propEq`'s literals; the pin
      -- escapes sit in the clause only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs (h : propNeReifSlot st i j r = _) => by
        rcases LeanFzn.Solver.Propagation.propNeReifSlot_cases st i j r with
          ⟨-, he⟩ | ⟨-, -, he⟩ | he
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ :=
            LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_ne st i j l rs0 hres
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ :=
            LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_eq st i j l rs0 hres
        · rw [he] at h; cases h
  | linEqReif coeffs is b r =>
      -- PLAN L5: the implied head is the delegated `propLinEq2`/`propLinNe`
      -- literal (an order or value-removal literal); the pin/typing escapes
      -- sit in the clause only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs h => by
        rcases LeanFzn.Solver.Propagation.propLinEqReif_implied_order h with
          ⟨m, k, mn, mx, hord, -, -⟩ | ⟨m, v, hpos, -⟩
        · rcases hord with rfl | rfl
          · exact noBoolAtom_posLe m k
          · exact noBoolAtom_negLe m k
        · subst hpos
          exact noBoolAtom_posNe m v
  | linLeReif coeffs is b r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l' rs' h => by
        rcases LeanFzn.Solver.Propagation.propLinLeReif_implied_order h with
          ⟨m, k, mn, mx, hord, -, -⟩ | ⟨hbool, hguard⟩
        · rcases hord with rfl | rfl
          · exact noBoolAtom_posLe m k
          · exact noBoolAtom_negLe m k
        · -- PLAN L1b/G1d: both bounds-arm pins need a Boolean-only
          -- state domain, which `IntState` excludes
          exfalso
          obtain ⟨hlen', hall⟩ :=
            LeanFzn.Solver.Propagation.domBoolOnlyB_eq hguard
          have hlen'' : 0 < (Dom.enum (st.domains.getD r Dom.empty)).length := hlen'
          have hne : st.domains.getD r Dom.empty ≠ Dom.empty := by
            intro h0
            rw [h0, Dom.enum_empty] at hlen''
            simp at hlen''
          have hlt : r < st.domains.length := by
            by_cases hr : r < st.domains.length
            · exact hr
            · exact absurd
                (LeanFzn.Solver.Propagation.getD_nil_of_length_le hr) hne
          have hmem : st.domains.getD r Dom.empty ∈ st.domains :=
            LeanFzn.Solver.Propagation.getD_mem_of_lt hlt
          have hneE : Dom.enum (st.domains.getD r Dom.empty) ≠ [] := by
            intro h0
            rw [h0] at hlen''
            simp at hlen''
          obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hneE
          have hvE : v ∈ slotEnum st.domains r := hv
          obtain ⟨b2, hb2⟩ := hall v hvE
          have hvD : v ∈ st.domains.getD r Dom.empty :=
            (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
          obtain ⟨k2, hk2⟩ := hst _ hmem v hvD
          rw [hb2] at hk2
          exact absurd hk2 (by simp)
  | linNeReif coeffs is b r =>
      -- PLAN L5: the implied head is the delegated `propLinNe`/`propLinEq2`
      -- literal (an order or value-removal literal); the pin/typing escapes
      -- sit in the clause only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs h => by
        rcases LeanFzn.Solver.Propagation.propLinNeReif_implied_order h with
          ⟨m, k, mn, mx, hord, -, -⟩ | ⟨m, v, hpos, -⟩
        · rcases hord with rfl | rfl
          · exact noBoolAtom_posLe m k
          · exact noBoolAtom_negLe m k
        · subst hpos
          exact noBoolAtom_posNe m v
  | minPair o₀ o₁ r =>
      cases o₀ <;> cases o₁ <;> cases r <;>
        (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
         subst hprop
         first
           | exact nb_min st _ _ _
           | exact fun l r h => by
               simp only [Propagator.run_mk] at h
               exact (propCheck_implied_elim h).elim)
  | maxPair o₀ o₁ r =>
      cases o₀ <;> cases o₁ <;> cases r <;>
        (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
         subst hprop
         first
           | exact nb_max st _ _ _
           | exact fun l r h => by
               simp only [Propagator.run_mk] at h
               exact (propCheck_implied_elim h).elim)
  | divGen o₁ o₂ r =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propDiv`; its implied literals are order literals.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_div st o₁ o₂ r
  | modGen o₁ o₂ r =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propMod`; its implied literals are order literals.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_mod st o₁ o₂ r
  | maxGen os r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_maxGen st os r
  | bool2intSlot i k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_bool2int st hst i k
  | minGen os r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact nb_minGen st os r
  | _ =>
      first
        | (exfalso; revert hf; simp [lcgFamB]; done)
        | (simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
           first
            | (contradiction)
            | (simp only [Option.some.injEq] at hprop
               subst hprop
               first
                | exact nb_eq st _ _ | exact nb_ne st _ _ | exact nb_le st _ _ | exact nb_lt st _ _
                | exact nb_constEq st hst _ _ | exact nb_plus st _ _ _
                | exact impliedNB_narrowHi _ _ _ _ | exact impliedNB_narrowLo _ _ _ _
                | exact nb_allDiff st _ | exact nb_linLe st _ _ _ | exact nb_linEq st _ _ _
                | exact nb_boolNot hst _ _ | exact nb_boolAnd hst _ _ _ | exact nb_boolOr hst _ _ _
                | exact nb_arrayIntElement st hst _ _ _
                | exact nb_arrayVarIntElement st hst _ _ _
                | exact nb_arrayVarBoolElement st hst _ _ _
                | exact nb_arrayBoolAnd st hst _ _))

end LeanFzn.Solver.UIP.LcgNoBool
