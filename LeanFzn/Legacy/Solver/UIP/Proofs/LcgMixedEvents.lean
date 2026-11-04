/-
Purpose: productive propagation event correctness on shape-typed integer/Boolean boxes.
Dependencies: LcgEvents supplies unchanged reachable/event interfaces and slot bounds;
LcgBooleanFalsity supplies shape-aware database unit semantics and frame falsity.
DAG: mixed frame + normalized database -> this event bridge -> mixed run induction.
Canonical learned clauses are a syntax invariant to be produced along the run,
not an assumed correctness conclusion. Reason-pivot contracts remain unchanged.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEvents
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgBooleanFalsity
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv LeanFzn.Solver.UIP.LcgEvents
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies
open LeanFzn.Solver.UIP.LcgClamp LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.ClampPool
namespace LeanFzn.Solver.UIP.LcgMixedEvents
variable {leaf : Assignment → Bool}

/-- Structural state facts for a mixed-domain event. -/
structure MixedLcgFrameState (orig : List Domain) (bs : BranchState leaf) : Prop
    extends LcgFrameState orig bs where
  boolPins : BoolPinsOn bs.trail bs.frame
  canonical : ∀ c ∈ bs.learned, ∀ q ∈ c, q.norm = q

theorem lcgEvent_of_kit_at_shape {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw) (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : ShapeTypedDomains orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hcontract : PropagationContract leaf raw)
    {bs : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    (hS : MixedLcgFrameState orig bs) :
    ∀ d : ProductiveDeduction leaf bs, explainedDeduction original props bs = some d →
      LearnedEntailed leaf [d.reason] ∧
      d.literal.atom.slot < (fullDomains bs.frame).length ∧
      SemReasonOK orig bs.trail d.literal.norm d.reason := by
  intro d hd
  obtain ⟨lr, fl, hev⟩ := LcgRunInv.explainedDeduction_event hd
  have hP : ∀ p ∈ props, PropSemContract orig p bs :=
    propSem_of_state hraw hprops hfam (frameExplainedFull_of_frameJ_shape hint hS.frameJ hS.boolPins) hS.snap
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
  · exact semReasonOK_norm (nextPruningEvent_implied_sem_shape hint hS.frameJ hS.shape hS.boolPins hS.canonical hP hev)


end LeanFzn.Solver.UIP.LcgMixedEvents
