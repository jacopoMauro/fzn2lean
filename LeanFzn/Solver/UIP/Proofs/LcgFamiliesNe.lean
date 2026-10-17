/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamiliesNe.lean
U1b: `PropSemContract` for `neSlot` (`propNe`).
-/
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesBasic
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies

namespace LeanFzn.Solver.UIP.LcgFamilies

variable {orig : List Domain} {pre : List TrailEntry} {st : State}

theorem reasonOK_of_fix {l : Literal} {c : Clause} (hl : l.norm = l) (hmem : l ∈ c)
    (hc : ∀ q ∈ c, q ≠ l → SemFalsifiedBefore orig pre q) : SemReasonOK orig pre l c := by
  refine ⟨by rw [hl]; exact hmem, fun q hq hne => hc q hq ?_⟩
  intro hq'
  subst hq'
  simp [litEqB] at hne

theorem domMinMax_singleton {x : Value} {c : Int} (h : domSingletonI [x] = some c) :
    domMinI [x] = some c ∧ domMaxI [x] = some c := by
  cases x with
  | int a =>
      simp [domSingletonI] at h
      subst h
      simp [domMinI, domMaxI, domInts]
  | bool b =>
      simp [domSingletonI] at h
      subst h
      cases b <;> simp [domMinI, domMaxI, domInts]
  | setOfInt _ => simp [domSingletonI] at h
  | array _ => simp [domSingletonI] at h

/-- The integer-sort root fact: a Boolean literal on an integer-sorted slot is
false at the root (its evaluation is undefined). -/
def BoolRoot (orig : List Domain) (s : Nat) : Prop :=
  ∀ b, litFalseAtRoot orig (posBool s b) = true

theorem neBoolLit_sf_self {doms : List Domain} (hA : AbsentExpl orig pre doms) {s : Nat}
    {k c : Int} (hy : doms.getD s [] = [Value.int k])
    (hn : SemFalsifiedBefore orig pre (negLe s c)) :
    SemFalsifiedBefore orig pre (neBoolLit s s c) := by
  unfold neBoolLit
  split
  · exact hA s _ (by rw [hy]; simp [DomainFiltering.valueMemB, Value.eqB])
  · exact hn

theorem neBoolLit_sf_other {doms : List Domain} (hA : AbsentExpl orig pre doms) {p s : Nat}
    {k c : Int} (hg : domNeGate (Value.int k) c (doms.getD s []) = true)
    (hn : SemFalsifiedBefore orig pre (negLe p c)) :
    SemFalsifiedBefore orig pre (neBoolLit p s c) := by
  unfold neBoolLit
  split
  · rename_i h01
    refine hA s _ ?_
    cases hm : DomainFiltering.valueMemB (Value.bool (decide (c = 1))) (doms.getD s []) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨v, hv, hveq⟩ := List.any_eq_true.mp hm
      have hvb : v = Value.bool (decide (c = 1)) := by
        cases v <;> simp_all [Value.eqB]
      subst hvb
      have := List.all_eq_true.mp hg _ hv
      rcases h01 with rfl | rfl <;> simp [Value.intView, Value.eqB] at this
  · exact hn

theorem propNe_sem (hB : BoundsExpl orig pre st.domains) (hA : AbsentExpl orig pre st.domains)
    (hF : FixExpl orig pre st.domains) (i j : Nat) : ResSem orig pre (propNe st i j) := by
  unfold propNe
  split
  · rename_i x y hx hy
    split
    · rename_i hxy
      intro q hq
      cases x with
      | int a =>
          cases y with
          | int b' =>
              have hab : a = b' := by simpa [Value.eqB] using hxy
              subst hab
              simp only [neConflictClause, List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl
              · exact hF i a hx
              · exact hF j a hy
          | bool _ => simp [Value.eqB] at hxy
          | setOfInt _ => simp [Value.eqB] at hxy
          | array _ => simp [Value.eqB] at hxy
      | bool a =>
          cases y with
          | bool b' =>
              have hab : a = b' := by simpa [Value.eqB] using hxy
              subst hab
              simp only [neConflictClause, List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl
              · exact hA i (!a) (by rw [hx]; cases a <;> rfl)
              · exact hA j (!a) (by rw [hy]; cases a <;> rfl)
          | int _ => simp [Value.eqB] at hxy
          | setOfInt _ => simp [Value.eqB] at hxy
          | array _ => simp [Value.eqB] at hxy
      | setOfInt _ => simp [neConflictClause] at hq
      | array _ => simp [neConflictClause] at hq
    · trivial
  · rename_i _ dy x hy hne
    cases hs : domSingletonI [x] with
    | none => trivial
    | some c =>
      simp only []
      split
      · rename_i hcond
        obtain ⟨hmn, hmx⟩ := domMinMax_singleton hs
        have b1 := (hB i).2 c (by rw [hy]; exact hmn)
        have b2 := (hB i).1 c (by rw [hy]; exact hmx)
        obtain ⟨h12, hint⟩ := Bool.and_eq_true_iff.mp hcond
        obtain ⟨-, hgate⟩ := Bool.and_eq_true_iff.mp h12
        obtain ⟨k, rfl⟩ : ∃ k, x = Value.int k := by
          cases x <;> simp [isIntValue] at hint ⊢
        have b3 : SemFalsifiedBefore orig pre (neBoolLit i i c) :=
          neBoolLit_sf_self hA hy b2
        have b4 : SemFalsifiedBefore orig pre (neBoolLit i j c) :=
          neBoolLit_sf_other hA hgate b2
        exact reasonOK_of_fix (by rfl) (by simp) (sf_cons _ (by sfs))
      · trivial
  · rename_i _ dx y hy hne
    cases hs : domSingletonI [y] with
    | none => trivial
    | some c =>
      simp only []
      split
      · rename_i hcond
        obtain ⟨hmn, hmx⟩ := domMinMax_singleton hs
        have b1 := (hB j).2 c (by rw [hy]; exact hmn)
        have b2 := (hB j).1 c (by rw [hy]; exact hmx)
        obtain ⟨h12, hint⟩ := Bool.and_eq_true_iff.mp hcond
        obtain ⟨-, hgate⟩ := Bool.and_eq_true_iff.mp h12
        obtain ⟨k, rfl⟩ : ∃ k, y = Value.int k := by
          cases y <;> simp [isIntValue] at hint ⊢
        have b3 : SemFalsifiedBefore orig pre (neBoolLit j j c) :=
          neBoolLit_sf_self hA hy b2
        have b4 : SemFalsifiedBefore orig pre (neBoolLit j i c) :=
          neBoolLit_sf_other hA hgate b2
        exact reasonOK_of_fix (by rfl) (by simp) (sf_cons _ (by sfs))
      · trivial
  · trivial

end LeanFzn.Solver.UIP.LcgFamilies
