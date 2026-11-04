/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunCert.lean
H2c (part 5): the restoration certificate and the norm-falsification of the recorded analysis from
`LcgReachableState` only (copies of `analyzeAtAllowance_certificate` and
`recordedAnalysis_normFalsified` whose `ReachableState` premise is weakened to the two fields
actually used: distinct, norm).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunJump
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting

namespace LeanFzn.Solver.UIP.LcgRunCert

theorem lcg_certificate {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    {an : ConflictAnalysis} {below : List (Literal × Nat)} {uip : Literal}
    {orig' : List Domain}
    (hdistinct : TrailLiteralsDistinct bs.trail)
    (hnorm : ∀ e ∈ bs.trail, e.literal = e.literal.norm)
    (hpos : 0 < bs.level)
    (h : analyzeAtAllowance orig' bs.trail bs.level c = some (below, uip))
    (hanL : an.learned = uip.negate :: below.map (fun p => p.1))
    (hanA : an.asserting = uip.negate)
    (hanB : an.backjumpLevel = below.foldl (fun a p => max a p.2) 0)
    (hent : LearnedEntailed leaf [an.learned]) :
    RestorationCertificate leaf bs an := by
  obtain ⟨hm0, hl0⟩ := lcgInv_init bs.trail bs.level c
  obtain ⟨hok, i, m, hmi, hmLit, hmLev⟩ :=
    analyzeLoop_inv _ _ below uip hm0 hl0 h
  have hmMem : m ∈ bs.trail := List.mem_of_getElem? hmi
  have hbelowStrict : ∀ p ∈ below, p.2 < bs.level := by
    intro p hp
    obtain ⟨-, -, -, -, -, hlt⟩ := hok p hp
    exact hlt
  have huipnorm : uip = uip.norm := by
    rw [← hmLit]
    exact hnorm m hmMem
  have hass : m.literal = (an.asserting.negate).norm := by
    rw [hanA, Literal.negate_negate, ← huipnorm]
    exact hmLit
  have hmaxLe : ∀ p ∈ below, p.2 ≤ an.backjumpLevel := by
    intro p hp
    rw [hanB]
    exact foldl_max_mem_le below 0 p hp
  have hlg : an.asserting ∈ an.learned := by
    rw [hanL, hanA]
    exact List.mem_cons_self ..
  have hlt : an.backjumpLevel < bs.level := by
    rw [hanB]
    exact foldl_max_lt below 0 bs.level hbelowStrict hpos
  refine
    { assertingMem := hlg
      learnedEntailed := hent
      learnedFalsified := ?_
      assertingAtConflict := ⟨m, hmMem, hass, hmLev⟩
      othersBelow := ?_
      targetLegal := Nat.le_of_lt hlt
      targetDescends := Or.inr hlt
      targetMaximal := ?_
      assertingSurvives := ?_
      unitAfterRestore := ?_
      conservation := ?_
      targetAttained := ?_ }
  · intro q hq
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · refine ⟨m, hmMem, ?_⟩
      rw [hEq, Literal.negate_negate, ← huipnorm]
      exact hmLit
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨⟨e, he, -, hlit⟩, -, -⟩ :=
        lcg_below_pair_facts (target := an.backjumpLevel) hok hdistinct hnorm hmaxLe hp
      exact ⟨e, he, by rw [← hpq]; exact hlit⟩
  · intro q hq hne
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨hf1, hf2, _⟩ := lcg_below_pair_facts hok hdistinct hnorm hmaxLe hp
      refine ⟨?_, ?_⟩
      · obtain ⟨e, he, hlev, hlit⟩ := hf1
        exact ⟨e, he, hlev, by rw [← hpq]; exact hlit⟩
      · intro e₂ he₂ hlev₂ hlit₂
        rw [← hpq] at hlit₂
        exact hf2 e₂ he₂ hlev₂ hlit₂
  · intro q hq hne e₂ he₂ hlit₂
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      rw [← hpq] at hlit₂
      exact (lcg_below_pair_facts hok hdistinct hnorm hmaxLe hp).2.2 e₂ he₂ hlit₂
  · intro e he hlevel hlit
    have hsame : e.literal = m.literal := hlit.trans hass.symm
    have heq : e = m := hdistinct.1 m hmMem e he (hsame.trans (hnorm m hmMem))
    rw [heq, hmLev] at hlevel
    omega
  · intro a hleaf htrail
    refine asserting_of_entailed (an := an) hent hlg ?_ hleaf
    intro q hq hne
    rw [hanL] at hq
    rcases List.mem_cons.mp hq with hEq | hq
    · exact absurd (by rw [hEq, hanA]) hne
    · obtain ⟨p, hp, hpq⟩ := List.mem_map.mp hq
      obtain ⟨⟨e, he, hlev, hlit⟩, _, _⟩ :=
        lcg_below_pair_facts hok hdistinct hnorm hmaxLe hp
      exact eval_false_of_surviving ⟨e, he, hlev, by rw [← hpq]; exact hlit⟩ htrail
  · intro a hleaf _ q _
    obtain ⟨q', hq', hq'true⟩ := hent an.learned (List.mem_singleton_self _) a hleaf
    exact Or.inr ⟨q', hq', hq'true⟩
  · rcases Nat.eq_zero_or_pos an.backjumpLevel with h0 | hposT
    · exact Or.inl h0
    · have hne : below.foldl (fun a p => max a p.2) 0 ≠ 0 := by
        rw [← hanB]
        omega
      obtain ⟨p, hp, hpv⟩ := foldl_max_attained_mem hne
      obtain ⟨e, he, hp1, hlev, -, -⟩ := hok p hp
      refine Or.inr ⟨e, he, ?_, p.1, ?_, ?_⟩
      · rw [hlev, hpv, hanB]
      · rw [hanL]
        exact List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun p : Literal × Nat => p.1) hp)
      · rw [hp1, lcg_learnt_negate_norm (hnorm e he)]


theorem lcg_normFalsified {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hb : cfg.branch = bs) (hreach : LcgReachableState leaf orig bs)
    (hcfg : SchedulerReachable cfg)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    FalsifiedByTrailNorm bs an.learned := by
  obtain ⟨below, uip, hrun, heq⟩ :=
    reachable_analysis_success leaf cfg ev an hcfg hconf hana
  rw [hb] at hrun
  subst heq
  have hL : (ConflictAnalysis.ofUIP below uip).normalized.learned
      = (uip.negate :: below.map (fun p => p.1)).map Literal.norm := rfl
  obtain ⟨hm0, hl0⟩ := lcgInv_init bs.trail bs.level ev.clause
  obtain ⟨hbf, i, m, hmi, hmlit, -⟩ := analyzeLoop_inv _ _ below uip hm0 hl0 hrun
  have hm : m ∈ bs.trail := List.mem_of_getElem? hmi
  have hnorm : ∀ e ∈ bs.trail, e.literal = e.literal.norm :=
    hreach.norm
  have huipnorm : uip = uip.norm := by
    have h := hnorm m hm
    rw [hmlit] at h
    exact h
  intro q hq
  rw [hL] at hq
  rcases List.mem_map.mp hq with ⟨q₀, hq₀, rfl⟩
  rcases List.mem_cons.mp hq₀ with rfl | hq₀
  · exact ⟨m, hm, by
      simpa [norm_negate_norm_local, Literal.negate_negate]
        using hmlit.trans huipnorm⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq₀
    obtain ⟨e, he, hp1, -⟩ := hbf p hp
    exact ⟨e, he, by
      rw [norm_negate_norm_local, hp1, lcg_learnt_negate_norm (hnorm e he)]⟩


end LeanFzn.Solver.UIP.LcgRunCert
