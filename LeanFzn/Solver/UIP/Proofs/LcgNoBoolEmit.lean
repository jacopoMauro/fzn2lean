/-
File: LeanFzn/Solver/UIP/Proofs/LcgNoBoolEmit.lean

DL (decide-site liveness), part 1: on an integer-valued state no `lcgFamB` raw propagator ever
implies a Boolean-atom literal. Boolean atoms are only emitted behind a `domBoolPin` / `.bool`
membership guard, which an integer-valued state falsifies.
-/
import LeanFzn.Solver.UIP.Proofs.LcgEmissionTyped
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
    (h : domBoolOnlyB (st.domains.getD r []) = true) : ¬ IntState st := by
  intro hI
  obtain ⟨hlen0, hall⟩ := domBoolOnlyB_eq h
  have hne : st.domains.getD r [] ≠ [] := by
    intro h0
    rw [h0] at hlen0
    exact absurd hlen0 (by simp)
  have hlt : r < st.domains.length := by
    by_cases hlt' : r < st.domains.length
    · exact hlt'
    · exact absurd (getD_nil_of_length_le hlt') hne
  obtain ⟨b, hb⟩ := hall ((st.domains.getD r [])[0])
    (List.getElem_mem hlen0)
  obtain ⟨k, hk⟩ := hI (st.domains.getD r []) (getD_mem_of_lt hlt)
    (.bool b) (by rw [← hb]; exact List.getElem_mem hlen0)
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
    ∀ v ∈ st.domains.getD s [], ∃ k : Int, v = Value.int k := by
  intro v hv
  rw [List.getD_eq_getElem?_getD] at hv
  cases hs : st.domains[s]? with
  | none => rw [hs] at hv; simp at hv
  | some d => rw [hs] at hv; exact h d (List.mem_of_getElem? hs) v hv

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
      by_cases h1 : valueMemB (Value.bool b) (st.domains.getD i []) = true
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
      -- PLAN L4: the heads are `propLe`/`propLt`'s order literals; the pin
      -- escapes sit in the clause only.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact fun l rs (h : propLeReifSlot st i j r = _) => by
        rcases LeanFzn.Solver.Propagation.propLeReifSlot_cases st i j r with
          ⟨-, he⟩ | ⟨-, -, he⟩ | he
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ := LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_le st i j l rs0 hres
        · rw [he] at h
          obtain ⟨rs0, hres, -⟩ := LeanFzn.Solver.Propagation.augmentRes_implied_inv h
          exact nb_lt st j i l rs0 hres
        · rw [he] at h; cases h
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
        · -- PLAN L1b: the bounds arm's pin needs a Boolean-only state
          -- domain, which `IntState` excludes
          exfalso
          subst hbool
          obtain ⟨hlen', hall⟩ :=
            LeanFzn.Solver.Propagation.domBoolOnlyB_eq hguard
          have hne : st.domains.getD r [] ≠ [] := by
            intro h0
            rw [h0] at hlen'
            simp at hlen'
          have hlt : r < st.domains.length := by
            by_cases hr : r < st.domains.length
            · exact hr
            · exact absurd
                (LeanFzn.Solver.Propagation.getD_nil_of_length_le hr) hne
          have hmem : st.domains.getD r [] ∈ st.domains :=
            LeanFzn.Solver.Propagation.getD_mem_of_lt hlt
          obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨b2, hb2⟩ := hall v hv
          obtain ⟨k2, hk2⟩ := hst _ hmem v hv
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
           | exact fun l r h => (propCheck_implied_elim h).elim)
  | maxPair o₀ o₁ r =>
      cases o₀ <;> cases o₁ <;> cases r <;>
        (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
         subst hprop
         first
           | exact nb_max st _ _ _
           | exact fun l r h => (propCheck_implied_elim h).elim)
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
                | exact nb_boolNot hst _ _ | exact nb_boolAnd hst _ _ _ | exact nb_boolOr hst _ _ _))

end LeanFzn.Solver.UIP.LcgNoBool
