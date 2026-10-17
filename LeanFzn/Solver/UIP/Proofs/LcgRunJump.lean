/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunJump.lean
H2c (part 4): the restoration pre-state of a successful jump is `LcgReachableState`, from a
checkpoint snapshot (itself Lcg-reachable), the restoration certificate and the usual site
facts. No `hbr`, no exact chronology: the asserting entry's reason is justified semantically by
the checkpoint trail (`semFalsifiedBefore_of_others`).
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunArms
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting

namespace LeanFzn.Solver.UIP.LcgRunJump

variable {leaf : Assignment → Bool}

/-- A checkpoint is the frame/trail/level of some Lcg-reachable state. -/
def LcgSnapshot (leaf : Assignment → Bool) (orig : List Domain) (cp : DecisionCheckpoint leaf) :
    Prop :=
  ∃ bs : BranchState leaf, LcgReachableState leaf orig bs ∧
    bs.frame = cp.frame ∧ bs.trail = cp.trail ∧ bs.level = cp.level

theorem lcgSnapshot_ofBranch {orig : List Domain} {bs : BranchState leaf}
    (h : LcgReachableState leaf orig bs) :
    LcgSnapshot leaf orig (DecisionCheckpoint.ofBranch bs) :=
  ⟨bs, h, rfl, rfl, rfl⟩

/-- **The Lcg restoration pre-state** of a successful jump. -/
theorem lcgRestorationState_reachable {orig : List Domain}
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis} {g : BranchFrame}
    (hsnap : LcgSnapshot leaf orig cp)
    (hbs : LcgReachableState leaf orig bs)
    (hcert : RestorationCertificate leaf bs an)
    (hstable : an.asserting.norm = an.asserting)
    (hsurv : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hrange : an.asserting.atom.slot < orig.length)
    (hg : filterFrame an.asserting cp.frame = some g) :
    LcgReachableState leaf orig (restorationState cp bs an g) := by
  obtain ⟨bs', hbs', hf, ht, hl⟩ := hsnap
  have hgpre : g.2 = cp.frame.2 := filterFrame_prefix hg
  have hglen : g.1.length = cp.frame.1.length := filterFrame_rem_length hg
  have hsub : ∀ e ∈ bs'.trail, e ∈ cp.trail := fun e he => by
    rw [ht] at he
    exact he
  have hsub' : ∀ e ∈ cp.trail, e ∈ bs'.trail := fun e he => by
    rw [← ht] at he
    exact he
  have hsorted : TrailLevelSorted cp.trail := by
    rw [← ht]
    exact hbs'.sorted
  have hdistinct : TrailLiteralsDistinct cp.trail := by
    rw [← ht]
    exact hbs'.distinct
  have hnormT : ∀ e ∈ cp.trail, e.literal = e.literal.norm :=
    fun e he => hbs'.norm e (hsub' e he)
  have hlen : (fullDomains g).length = orig.length := by
    have h1 : (fullDomains g).length = (fullDomains cp.frame).length := by
      rw [fullDomains_length, fullDomains_length, hgpre, hglen]
    have h2 : (fullDomains cp.frame).length = (fullDomains bs'.frame).length := by
      rw [← hf]
    exact h1.trans (h2.trans hbs'.length_ok)
  have hmem : (an.asserting.norm ∈ an.learned) = True :=
    hcert.asserting_norm_mem_of_stable hstable
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- full_fits
    intro i v hv
    exact hbs'.full_fits i v (by
      rw [hf]
      exact Frame.domains_subsets hg i v hv)
  · -- prefix_forced
    intro a htrail hfit i hi
    have hi' : i < bs'.frame.2.length := by
      rw [hf, ← hgpre]
      exact hi
    have h := hbs'.prefix_forced a
      (fun e he => htrail e (List.mem_append.mpr (Or.inl (hsub e he))))
      hfit i hi'
    rw [hf, ← hgpre] at h
    exact h
  · -- agrees
    intro e he a hcov
    replace he := restorationState_mem he
    rcases he with he | he
    · exact hbs'.agrees e (hsub' e he) a (by
        rw [hf]
        exact filterFrame_refines hg hcov)
    · subst he
      exact filterFrame_literal_holds hg hcov (by rw [hlen]; exact hrange)
  · -- narrowing_complete
    intro i w horig hnot
    have horig0 : w ∈ orig.getD (g.2.length + i) [] := horig
    have hnot0 : w ∉ g.1.getD i [] := hnot
    have horig' : w ∈ orig.getD (cp.frame.2.length + i) [] := by
      rw [hgpre] at horig0
      exact horig0
    by_cases hwas : w ∈ cp.frame.1.getD i []
    · obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hg hwas hnot0
      obtain ⟨e0, he0, hel⟩ : ∃ e0 ∈ (restorationState cp bs an g).trail,
          e0.literal = an.asserting.norm := by
        rcases restorationState_trail_cases cp bs an g with ⟨h, e0, he0, hel⟩ | ⟨h, -⟩
        · exact ⟨e0, by rw [h]; exact he0, hel⟩
        · refine ⟨{ literal := an.asserting.norm, level := cp.level,
                      reason := some { clause := an.learned } }, ?_, rfl⟩
          rw [h]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      refine ⟨e0, he0, ?_, ?_⟩
      · show e0.literal.atom.slot = g.2.length + i
        rw [hel, norm_atom_slot, hslot, hgpre]
      · rw [hel]; rwa [norm_valueHolds]
    · have horig'' : w ∈ orig.getD (bs'.frame.2.length + i) [] := by
        rw [hf]
        exact horig'
      have hnot' : w ∉ bs'.frame.1.getD i [] := by
        rw [hf]
        exact hwas
      obtain ⟨e, he, hslot, hfalse⟩ := hbs'.narrowing_complete i w horig'' hnot'
      refine ⟨e, ?_, ?_, hfalse⟩
      · rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]; exact hsub e he
        · rw [h]; exact List.mem_append.mpr (Or.inl (hsub e he))
      · show e.literal.atom.slot = g.2.length + i
        rw [hslot, hgpre, ← hf]
  · -- levels
    intro e he
    replace he := restorationState_mem he
    show e.level ≤ cp.level
    rcases he with he | he
    · simpa only [hl] using hbs'.levels e (hsub' e he)
    · subst he
      exact Nat.le_refl _
  · -- norm
    intro e he
    replace he := restorationState_mem he
    rcases he with he | he
    · exact hnormT e he
    · subst he
      exact (norm_norm an.asserting).symm
  · -- reason_ent
    intro e he r hr
    replace he := restorationState_mem he
    rcases he with he | he
    · exact hbs'.reason_ent e (hsub' e he) r hr
    · subst he
      have hr1 : { clause := an.learned } = r := by
        simpa only [Option.mem_some_iff] using hr
      rw [← hr1]
      exact ⟨hcert.learnedEntailed, hmem⟩
  · -- trail_sem
    have hts : TrailSem orig cp.trail := by rw [← ht]; exact hbs'.trail_sem
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hts
    rw [h]
    refine hts.snoc (fun r hr => ?_)
    have hr1 : { clause := an.learned } = r := Option.some.inj hr
    rw [← hr1]
    refine ⟨by rw [norm_norm]; exact of_eq_true hmem, fun q hq hne => ?_⟩
    have hqa : q ≠ an.asserting := by
      intro h
      rw [h, norm_norm] at hne
      have htrue : litEqB an.asserting.norm an.asserting.norm = true := litEqB_iff.mpr rfl
      rw [htrue] at hne
      exact Bool.noConfusion hne
    exact semFalsifiedBefore_of_others hcert hsurv hq hqa
  · -- learned_ent
    intro c hc
    rw [restorationState_learned] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hcert.learnedEntailed _ (List.mem_singleton_self _)
    · exact hbs.learned_ent c hc
  · -- sorted
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hsorted
    rw [h]
    refine levelSorted_append hsorted ?_
    intro e' he'
    have hle := hbs'.levels e' (hsub' e' he')
    rw [hl] at hle
    show e'.level ≤ cp.level
    exact hle
  · -- distinct
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, hfresh⟩
    · rw [h]; exact hdistinct
    rw [h]
    exact TrailLiteralsDistinct.enqueue hdistinct hnormT hfresh

end LeanFzn.Solver.UIP.LcgRunJump
