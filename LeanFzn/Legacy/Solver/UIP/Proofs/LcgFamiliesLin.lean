/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamiliesLin.lean
U1b: `PropSemContract` for `linLe` (`propLinLe2`) and `linEq` (`propLinEq2`),
relative to `BoundsExpl` (every cause literal is built from a domain
extremum).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesBasic
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies

namespace LeanFzn.Solver.UIP.LcgFamilies

variable {orig : List Domain} {pre : List TrailEntry} {st : State}

theorem linCauseMinPair_sf (hB : BoundsExpl orig pre st.domains) (p : Int × Nat) {q : Literal}
    (h : linCauseMinPair st p = some q) : SemFalsifiedBefore orig pre q := by
  unfold linCauseMinPair at h
  by_cases h1 : p.1 > 0
  · rw [if_pos h1] at h
    cases hm : domMinI (st.domains.getD p.2 Dom.empty) with
    | none => rw [hm] at h; simp at h
    | some mn => rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact (hB p.2).2 mn hm
  · rw [if_neg h1] at h
    by_cases h2 : p.1 < 0
    · rw [if_pos h2] at h
      cases hm : domMaxI (st.domains.getD p.2 Dom.empty) with
      | none => rw [hm] at h; simp at h
      | some mx => rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact (hB p.2).1 mx hm
    · rw [if_neg h2] at h; simp at h

theorem linCauseMaxPair_sf (hB : BoundsExpl orig pre st.domains) (p : Int × Nat) {q : Literal}
    (h : linCauseMaxPair st p = some q) : SemFalsifiedBefore orig pre q := by
  unfold linCauseMaxPair at h
  by_cases h1 : p.1 > 0
  · rw [if_pos h1] at h
    cases hm : domMaxI (st.domains.getD p.2 Dom.empty) with
    | none => rw [hm] at h; simp at h
    | some mx => rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact (hB p.2).1 mx hm
  · rw [if_neg h1] at h
    by_cases h2 : p.1 < 0
    · rw [if_pos h2] at h
      cases hm : domMinI (st.domains.getD p.2 Dom.empty) with
      | none => rw [hm] at h; simp at h
      | some mn => rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact (hB p.2).2 mn hm
    · rw [if_neg h2] at h; simp at h

theorem linCausesMin_sf (hB : BoundsExpl orig pre st.domains) (rest : List (Int × Nat)) :
    ∀ q ∈ linCausesMin st rest, SemFalsifiedBefore orig pre q := by
  intro q hq
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hq
  exact linCauseMinPair_sf hB p hp

theorem linCausesMax_sf (hB : BoundsExpl orig pre st.domains) (rest : List (Int × Nat)) :
    ∀ q ∈ linCausesMax st rest, SemFalsifiedBefore orig pre q := by
  intro q hq
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hq
  exact linCauseMaxPair_sf hB p hp

theorem linGenArmHiMin_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linGenArmHiMin st m b c rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowHi_sem hB (by simp) (sf_cons _ (linCausesMin_sf hB rest))

theorem linGenArmLoMin_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linGenArmLoMin st m b c rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowLo_sem hB (by simp) (sf_cons _ (linCausesMin_sf hB rest))

theorem linGenArmLoMax_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linGenArmLoMax st m b c rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowLo_sem hB (by simp) (sf_cons _ (linCausesMax_sf hB rest))

theorem linGenArmHiMax_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linGenArmHiMax st m b c rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowHi_sem hB (by simp) (sf_cons _ (linCausesMax_sf hB rest))

theorem linEqArmHiMin_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linEqArmHiMin st m b rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowHi_sem hB (by simp) (sf_cons _ (linCausesMin_sf hB rest))

theorem linEqArmLoMax_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linEqArmLoMax st m b rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowLo_sem hB (by simp) (sf_cons _ (linCausesMax_sf hB rest))

theorem linEqArmLoMin_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linEqArmLoMin st m b rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowLo_sem hB (by simp) (sf_cons _ (linCausesMin_sf hB rest))

theorem linEqArmHiMax_sem (hB : BoundsExpl orig pre st.domains) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) (o : Option Int) :
    ResSem orig pre (linEqArmHiMax st m b rest o) := by
  cases o with
  | none => trivial
  | some lr => exact narrowHi_sem hB (by simp) (sf_cons _ (linCausesMax_sf hB rest))

theorem linDeduceLe_sem (hB : BoundsExpl orig pre st.domains) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : ResSem orig pre (linDeduceLe st b m c rest) := by
  unfold linDeduceLe
  by_cases h0 : rest.all (fun p => (minContrib st p).isSome) = true
  · rw [if_pos h0]
    by_cases h1 : c = 1
    · rw [if_pos h1]
      cases hs : sumMin st rest with
      | none => trivial
      | some lr => exact linEqArmHiMin_sem hB m b rest (some lr)
    · rw [if_neg h1]
      by_cases h2 : c = -1
      · rw [if_pos h2]
        cases hs : sumMin st rest with
        | none => trivial
        | some lr => exact linEqArmLoMin_sem hB m b rest (some lr)
      · rw [if_neg h2]
        by_cases h3 : c > 0
        · rw [if_pos h3]
          cases hs : sumMin st rest with
          | none => trivial
          | some lr => exact linGenArmHiMin_sem hB m b c rest (some lr)
        · rw [if_neg h3]
          by_cases h4 : c < 0
          · rw [if_pos h4]
            cases hs : sumMin st rest with
            | none => trivial
            | some lr => exact linGenArmLoMin_sem hB m b c rest (some lr)
          · rw [if_neg h4]; trivial
  · rw [if_neg h0]; trivial

theorem linDeduceEq_sem (hB : BoundsExpl orig pre st.domains) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : ResSem orig pre (linDeduceEq st b m c rest) := by
  unfold linDeduceEq
  by_cases h0 : rest.all (fun p => (minContrib st p).isSome) = true
  · rw [if_pos h0]
    by_cases h1 : c = 1
    · rw [if_pos h1]
      apply firstEvent_sem; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact linEqArmHiMin_sem hB m b rest _
      · exact linEqArmLoMax_sem hB m b rest _
    · rw [if_neg h1]
      by_cases h2 : c = -1
      · rw [if_pos h2]
        apply firstEvent_sem; intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact linEqArmLoMin_sem hB m b rest _
        · exact linEqArmHiMax_sem hB m b rest _
      · rw [if_neg h2]
        by_cases h3 : c > 0
        · rw [if_pos h3]
          apply firstEvent_sem; intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact linGenArmHiMin_sem hB m b c rest _
          · exact linGenArmLoMax_sem hB m b c rest _
        · rw [if_neg h3]
          by_cases h4 : c < 0
          · rw [if_pos h4]
            apply firstEvent_sem; intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact linGenArmLoMin_sem hB m b c rest _
            · exact linGenArmHiMax_sem hB m b c rest _
          · rw [if_neg h4]; trivial
  · rw [if_neg h0]; trivial

theorem linSweep_sem (coeffs : List Int) (is : List Nat)
    (f : Nat → Int → List (Int × Nat) → PropagationResult)
    (hf : ∀ m c rest, ResSem orig pre (f m c rest)) :
    ∀ (ps : List ((Int × Nat) × Nat)) (idx : Nat),
      ResSem orig pre (linSweep coeffs is f ps idx) := by
  intro ps
  induction ps with
  | nil => intro idx; trivial
  | cons p ps ih =>
      intro idx
      obtain ⟨⟨c, m⟩, i⟩ := p
      simp only [linSweep]
      cases hh : f m c (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1)) with
      | stable => exact ih (idx + 1)
      | implied l r =>
          have := hf m c (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1))
          rw [hh] at this; exact this
      | conflict cl =>
          have := hf m c (((coeffs.zip is).zipIdx.filter (fun p => p.2 != i)).map (·.1))
          rw [hh] at this; exact this

theorem propLinLe2_sem (hB : BoundsExpl orig pre st.domains) (coeffs : List Int)
    (is : List Nat) (b : Int) : ResSem orig pre (propLinLe2 st coeffs is b) := by
  unfold propLinLe2
  split
  · trivial
  · exact linSweep_sem coeffs is (linDeduceLe st b) (fun m c rest => linDeduceLe_sem hB b m c rest) _ _

theorem propLinEq2_sem (hB : BoundsExpl orig pre st.domains) (coeffs : List Int)
    (is : List Nat) (b : Int) : ResSem orig pre (propLinEq2 st coeffs is b) := by
  unfold propLinEq2
  split
  · trivial
  · exact linSweep_sem coeffs is (linDeduceEq st b) (fun m c rest => linDeduceEq_sem hB b m c rest) _ _

end LeanFzn.Solver.UIP.LcgFamilies
