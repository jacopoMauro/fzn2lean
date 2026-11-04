/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunJump.lean
H2c (part 4): the restoration pre-state of a successful jump is `LcgReachableState`, from a
checkpoint snapshot (itself Lcg-reachable), the restoration certificate and the usual site
facts. No `hbr`, no exact chronology: the asserting entry's reason is justified semantically by
the checkpoint trail (`semFalsifiedBefore_of_others`).

M2 sparse-frame port: the restored frame's order is the checkpoint's
(`Frame.filterFrame_order`), its slot count is preserved (`filterFrame_rem_length`), and the
narrowing completeness is the absolute-slot statement `NarrowingComplete` (no positional
`order.length + i` offsets).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunArms
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
  have hgpre : g.order = cp.frame.order := Frame.filterFrame_order hg
  have hglen : g.doms.length = cp.frame.doms.length := filterFrame_rem_length hg
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
  have htrailcp : ∀ a, (∀ e ∈ (restorationState cp bs an g).trail,
      e.literal.eval a = some true) → ∀ e ∈ cp.trail,
      e.literal.eval a = some true := by
    intro a ha e he
    rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at ha
      exact ha e he
    · rw [h] at ha
      exact ha e (List.mem_append.mpr (Or.inl he))
  have hlen : (fullDomains g).length = orig.length := by
    have h1 : (fullDomains g).length = (fullDomains cp.frame).length := by
      rw [fullDomains_length, fullDomains_length, hglen]
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
  · -- pins_forced
    intro k hk
    have hk' : k ∈ bs'.frame.order := by
      rw [hf, ← hgpre]
      exact hk
    obtain ⟨v, hv, hforce⟩ := hbs'.pins_forced k hk'
    have hv' : cp.frame.doms[k]?.map Dom.enum = some [v] := by rwa [hf] at hv
    refine ⟨v, filterFrame_singleton hg hv', ?_⟩
    intro a ha hfit
    exact hforce a (fun e he => htrailcp a ha e (hsub e he)) hfit
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
    intro k hk w horig hnot
    have hk' : k ∉ bs'.frame.order := by
      rw [hf, ← hgpre]
      exact hk
    by_cases hwas : w ∈ cp.frame.doms.getD k Dom.empty
    · obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hg hwas hnot
      obtain ⟨e0, he0, hel⟩ : ∃ e0 ∈ (restorationState cp bs an g).trail,
          e0.literal = an.asserting.norm := by
        rcases restorationState_trail_cases cp bs an g with ⟨h, e0, he0, hel⟩ | ⟨h, -⟩
        · exact ⟨e0, by rw [h]; exact he0, hel⟩
        · refine ⟨{ literal := an.asserting.norm, level := cp.level,
                      reason := some { clause := an.learned } }, ?_, rfl⟩
          rw [h]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      refine ⟨e0, he0, ?_, ?_⟩
      · show e0.literal.atom.slot = k
        rw [hel, norm_atom_slot, hslot]
      · rw [hel]; rwa [norm_valueHolds]
    · have hnot' : w ∉ bs'.frame.doms.getD k Dom.empty := by
        rw [hf]
        exact hwas
      obtain ⟨e, he, hslot, hfalse⟩ := hbs'.narrowing_complete k hk' w horig hnot'
      refine ⟨e, ?_, ?_, hfalse⟩
      · rcases restorationState_trail_cases cp bs an g with ⟨h, -⟩ | ⟨h, -⟩
        · rw [h]; exact hsub e he
        · rw [h]; exact List.mem_append.mpr (Or.inl (hsub e he))
      · show e.literal.atom.slot = k
        rw [hslot]
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
    rcases restorationState_trail_cases cp bs an g with ⟨h, hfresh⟩ | ⟨h, hfresh⟩
    · rw [h]; exact hdistinct
    rw [h]
    exact TrailLiteralsDistinct.enqueue hdistinct hnormT hfresh

end LeanFzn.Solver.UIP.LcgRunJump
