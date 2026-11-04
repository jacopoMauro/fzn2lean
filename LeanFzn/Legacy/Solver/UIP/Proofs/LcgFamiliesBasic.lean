/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamiliesBasic.lean
U1a/U1b part 1: `PropSemContract` for the five unit families, the three
Boolean families and `leSlot`/`ltSlot`/`eqSlot`/`plusSlot`, from the `run`
equations, relative to the frame-explanation invariant `FrameExplained`
(see `LcgFamilies.lean`).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamilies
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies

namespace LeanFzn.Solver.UIP.LcgFamilies

variable {leaf : Assignment → Bool}

/-- Cons-list helper: all tail literals falsified. -/
theorem sf_cons {orig : List Domain} {pre : List TrailEntry} (h : Literal) {l : List Literal}
    (hl : ∀ q ∈ l, SemFalsifiedBefore orig pre q) :
    ∀ q ∈ h :: l, q ≠ h → SemFalsifiedBefore orig pre q := by
  intro q hq hne
  rcases List.mem_cons.mp hq with rfl | hq
  · exact absurd rfl hne
  · exact hl q hq

theorem sfl_nil {orig : List Domain} {pre : List TrailEntry} :
    ∀ q ∈ ([] : List Literal), SemFalsifiedBefore orig pre q := by
  intro q hq; cases hq

theorem sfl_cons {orig : List Domain} {pre : List TrailEntry} {a : Literal} {l : List Literal}
    (ha : SemFalsifiedBefore orig pre a) (hl : ∀ q ∈ l, SemFalsifiedBefore orig pre q) :
    ∀ q ∈ a :: l, SemFalsifiedBefore orig pre q := by
  intro q hq
  rcases List.mem_cons.mp hq with h | h
  · rw [h]; exact ha
  · exact hl q h

macro "sfs" : tactic => `(tactic|
  (repeat' (first | exact sfl_nil | refine sfl_cons ?_ ?_)
   all_goals assumption))

/-! ## Unit families -/

theorem propLeConstHi_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i : Nat) (c : Int) : ResSem orig pre (propLeConstHi st i c) :=
  narrowHi_sem hB (by simp) (sf_cons _ (by sfs))

theorem propLeConstLo_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i : Nat) (c : Int) : ResSem orig pre (propLeConstLo st i c) :=
  narrowLo_sem hB (by simp) (sf_cons _ (by sfs))

theorem propLtConstHi_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i : Nat) (c : Int) : ResSem orig pre (propLtConstHi st i c) :=
  narrowHi_sem hB (by simp) (sf_cons _ (by sfs))

theorem propLtConstLo_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i : Nat) (c : Int) : ResSem orig pre (propLtConstLo st i c) := by
  unfold propLtConstLo
  have h : c + 1 - 1 = c := by omega
  exact narrowLo_sem hB (by rw [h]; simp) (by rw [h]; exact sf_cons _ (by sfs))

theorem propConstEq_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains) (i : Nat) (v : Value) :
    ResSem orig pre (propConstEq st i v) := by
  unfold propConstEq
  cases v with
  | int k =>
      apply firstEvent_sem
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
      · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  | bool b =>
      simp only
      split
      · split
        · trivial
        · exact reasonOK_of_bool (by simp) (sf_cons _ (by sfs))
      · rename_i hn
        intro q hq
        have : q = posBool i b := by simpa using hq
        subst this
        exact hA i b (by simpa [slotEnum, List.getD_eq_getElem?_getD] using hn)
  | setOfInt _ => trivial
  | array _ => trivial


/-! ## Boolean families -/

theorem propBoolNot_sem {orig pre} {st : State} (hA : AbsentExpl orig pre st.domains)
    (i j : Nat) : ResSem orig pre (propBoolNot st i j) := by
  rcases propBoolNot_emit (res := propBoolNot st i j) rfl with
    ⟨hp, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | hs
  all_goals first
    | (rw [hs]; trivial)
    | (rw [← h2]
       have := pins_of_absent hA hp
       try simp only [Bool.not_true, Bool.not_false] at *
       exact implyBool_sem hA (by simp) (sf_cons _ (by sfs)))

theorem propBoolAnd_sem {orig pre} {st : State} (hA : AbsentExpl orig pre st.domains)
    (i j k : Nat) : ResSem orig pre (propBoolAnd st i j k) := by
  rcases propBoolAnd_emit (res := propBoolAnd st i j k) rfl with
    ⟨hp, hq, h2⟩ | ⟨hp, hq, h2⟩ | ⟨hp, hq, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | hs
  all_goals first
    | (rw [hs]; trivial)
    | (rw [← h2]
       have := pins_of_absent hA hp
       have := pins_of_absent hA hq
       try simp only [Bool.not_true, Bool.not_false] at *
       exact implyBool_sem hA (by simp) (sf_cons _ (by sfs)))
    | (rw [← h2]
       have := pins_of_absent hA hp
       try simp only [Bool.not_true, Bool.not_false] at *
       exact implyBool_sem hA (by simp) (sf_cons _ (by sfs)))

theorem propBoolOr_sem {orig pre} {st : State} (hA : AbsentExpl orig pre st.domains)
    (i j k : Nat) : ResSem orig pre (propBoolOr st i j k) := by
  rcases propBoolOr_emit (res := propBoolOr st i j k) rfl with
    ⟨hp, hq, h2⟩ | ⟨hp, hq, h2⟩ | ⟨hp, hq, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | hs
  all_goals first
    | (rw [hs]; trivial)
    | (rw [← h2]
       have := pins_of_absent hA hp
       have := pins_of_absent hA hq
       try simp only [Bool.not_true, Bool.not_false] at *
       exact implyBool_sem hA (by simp) (sf_cons _ (by sfs)))
    | (rw [← h2]
       have := pins_of_absent hA hp
       try simp only [Bool.not_true, Bool.not_false] at *
       exact implyBool_sem hA (by simp) (sf_cons _ (by sfs)))


/-! ## Binary integer families -/

theorem propLe_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i j : Nat) : ResSem orig pre (propLe st i j) := by
  unfold propLe
  cases h1 : domMaxI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some yj =>
  cases h2 : domMinI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some xi' =>
  have b1 := (hB j).1 yj h1
  have b2 := (hB i).2 xi' h2
  apply firstEvent_sem
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))

theorem propLt_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i j : Nat) : ResSem orig pre (propLt st i j) := by
  unfold propLt
  cases h1 : domMaxI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some yj =>
  cases h2 : domMinI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some xi' =>
  have b1 := (hB j).1 yj h1
  have b2 := (hB i).2 xi' h2
  have e : xi' + 1 - 1 = xi' := by omega
  apply firstEvent_sem
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowLo_sem hB (by rw [e]; simp) (by rw [e]; exact sf_cons _ (by sfs))

theorem propEq_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i j : Nat) : ResSem orig pre (propEq st i j) := by
  unfold propEq
  cases h1 : domMinI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some mi =>
  cases h2 : domMaxI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some Mi =>
  cases h3 : domMinI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some mj =>
  cases h4 : domMaxI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some Mj =>
  have b1 := (hB i).2 mi h1
  have b2 := (hB i).1 Mi h2
  have b3 := (hB j).2 mj h3
  have b4 := (hB j).1 Mj h4
  apply firstEvent_sem
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))

theorem propPlus_sem {orig pre} {st : State} (hB : BoundsExpl orig pre st.domains)
    (i j k : Nat) : ResSem orig pre (propPlus st i j k) := by
  unfold propPlus
  cases h1 : domMinI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some xi' =>
  cases h2 : domMaxI (st.domains.getD i Dom.empty) with
  | none => trivial
  | some xi =>
  cases h3 : domMinI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some yj' =>
  cases h4 : domMaxI (st.domains.getD j Dom.empty) with
  | none => trivial
  | some yj =>
  cases h5 : domMinI (st.domains.getD k Dom.empty) with
  | none => trivial
  | some zk' =>
  cases h6 : domMaxI (st.domains.getD k Dom.empty) with
  | none => trivial
  | some zk =>
  have b1 := (hB i).2 xi' h1
  have b2 := (hB i).1 xi h2
  have b3 := (hB j).2 yj' h3
  have b4 := (hB j).1 yj h4
  have b5 := (hB k).2 zk' h5
  have b6 := (hB k).1 zk h6
  apply firstEvent_sem
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))

end LeanFzn.Solver.UIP.LcgFamilies
