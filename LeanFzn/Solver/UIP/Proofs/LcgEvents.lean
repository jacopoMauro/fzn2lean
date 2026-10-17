/-
File: LeanFzn/Solver/UIP/Proofs/LcgEvents.lean
H2b: the per-event premise `LcgEventPremise` of `LcgReachable.lean` for the clamped LCG kit.
Sources of deductions: the entailed learned-database unit scan and the clamped registered
propagators. The only state-level premise is `LcgFrameState` (frame explanation + shape + snap
fixedness of the trail), named explicitly.
-/
import LeanFzn.Solver.UIP.Proofs.LcgReachable
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable

namespace LeanFzn.Solver.UIP.LcgEvents

variable {leaf : Assignment → Bool}

/-- The state-level frame facts the event contract consumes (named premise, maintained by the
`frameJ_*` lemmas along the run). -/
structure LcgFrameState (orig : List Domain) (bs : BranchState leaf) : Prop where
  frameJ : FrameJ orig bs.trail bs.frame
  shape : FrameShape orig bs.frame
  snap : TrailSnapFixed orig bs.trail

/-- A productive deduction names an in-range slot (an out-of-range literal filters nothing). -/
theorem slot_lt_of_productive {f g : BranchFrame} {l : Literal}
    (hf : filterFrame l f = some g) (hd : Frame.mass g < Frame.mass f) :
    l.atom.slot < (fullDomains f).length := by
  by_cases hlt : l.atom.slot < (fullDomains f).length
  · exact hlt
  · exfalso
    have hlen : (Frame.domains f).length ≤ l.atom.slot := by
      simpa only [fullDomains] using Nat.le_of_not_lt hlt
    have hnil : (Frame.domains f).getD l.atom.slot [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    have := LcgRunInv.filterFrame_self_of_holds
      (l := l) (F := f) (by intro v hv; rw [hnil] at hv; simp at hv)
    rw [this] at hf
    cases hf
    omega

/-- **H2b (per-state form)**: the per-event conclusion at ONE state satisfying both
`LcgReachableState` and `LcgFrameState`. -/
theorem lcgEvent_of_kit_at {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw) (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hcontract : PropagationContract leaf raw)
    {bs : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    (hS : LcgFrameState orig bs) :
    ∀ d : ProductiveDeduction leaf bs, explainedDeduction original props bs = some d →
      LearnedEntailed leaf [d.reason] ∧
      d.literal.atom.slot < (fullDomains bs.frame).length ∧
      SemReasonOK orig bs.trail d.literal.norm d.reason := by
  intro d hd
  obtain ⟨lr, fl, hev⟩ := LcgRunInv.explainedDeduction_event hd
  have hP : ∀ p ∈ props, PropSemContract orig p bs :=
    propSem_of_state hraw hprops hfam (frameExplainedFull_of_explDoms hint hS.frameJ.expl) hS.snap
  refine ⟨?_, slot_lt_of_productive d.filtered d.decreases, ?_⟩
  · intro c hc a ha
    rw [List.mem_singleton] at hc
    subst hc
    rcases nextPruningEvent_implied_cases hev with hdb | ⟨-, hview, hprop⟩
    · obtain ⟨hmem, -, -⟩ := scanDatabase_implied_facts hdb
      exact hreach.learned_ent _ hmem a ha
    · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ := scanPropagators_implied_facts hprop
      rw [hcl]
      rw [hprops] at hpm
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
      obtain ⟨l0, r0, hrun0, -, hcl0⟩ := clamp_run_implied hrun
      rw [hcl0]
      exact (snapClause_satisfied (hfits a ha)).mpr (hcontract.reason _ hview p0 hp0 l0 r0 hrun0 a ha)
  · exact semReasonOK_norm (nextPruningEvent_implied_sem hint hS.frameJ hS.shape hP hev)

/-- **H2b**: the per-event premise for the clamped LCG kit. -/
theorem lcgEventPremise_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw) (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hcontract : PropagationContract leaf raw)
    (hframe : ∀ bs : BranchState leaf, LcgReachableState leaf orig bs →
      LcgFrameState orig bs) :
    LcgEventPremise leaf orig original props :=
  fun bs hreach d hd =>
    lcgEvent_of_kit_at hraw hprops hfam hint hfits hcontract hreach (hframe bs hreach) d hd

end LeanFzn.Solver.UIP.LcgEvents
