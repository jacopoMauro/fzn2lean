/-
Purpose: mixed-domain semantic state and propagation-closure preservation.
Dependencies: mixed event semantics, Boolean pins, and canonical emission producers.
DAG: mixed structural facts -> this closure bundle -> mixed scheduler run assembly.
The original integer kit and its accepted public theorems remain intact.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunGood
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedEvents
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgBooleanPins
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalRun
open LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgMixedEvents
open LeanFzn.Solver.UIP.LcgCanonicalRun
open LeanFzn.Solver.UIP.LcgCanonicalClauses LeanFzn.Solver.UIP.LcgCanonicalFamilies
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents

namespace LeanFzn.Solver.UIP.LcgMixedGood

variable {leaf : Assignment → Bool}

/-- The legitimate problem-level hypotheses of the clamped LCG kit. -/
structure MixedLcgKit (leaf : Assignment → Bool) (orig : List Domain) (original : List Clause)
    (dcs : List DomConstraint) (raw props : List Propagator) : Prop where
  raw_eq : raw = dcs.filterMap propagatorOfProved
  props_eq : props = clampProps orig raw
  fam : ∀ dc ∈ dcs, lcgFamB dc = true
  shape : ShapeTypedDomains orig
  canonicalOriginal : DatabaseCanonical original
  nd : ∀ d ∈ orig, (Dom.enum d).Nodup
  fits : ∀ a, leaf a = true → a.Fits orig
  contract : PropagationContract leaf raw
  typed : EmissionTyped orig raw
  aligned : DatabaseAligned orig original

theorem MixedLcgKit.vocab {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props) :
    EmissionPoolAt (litPool orig) props := by
  rw [K.props_eq]; exact emissionPoolAt_clampProps K.typed

/-- The per-state bundle. -/
structure MixedLcgGood (leaf : Assignment → Bool) (orig : List Domain) (bs : BranchState leaf) : Prop where
  reach : LcgReachableState leaf orig bs
  fj : FrameJ orig bs.trail bs.frame
  fs : FrameShape orig bs.frame
  voc : TrailVocabularyAt (litPool orig) bs.trail
  db : DatabaseAlignedAt (litPool orig) bs.learned
  boolPins : BoolPinsOn bs.trail bs.frame
  canonical : DatabaseCanonical bs.learned

theorem MixedLcgGood.frameState {orig : List Domain} {bs : BranchState leaf}
    (h : MixedLcgGood leaf orig bs) : MixedLcgFrameState orig bs :=
  ⟨⟨h.fj, h.fs, fun e he => snapLit_fixed_of_norm_pool (h.voc e he)⟩, h.boolPins, h.canonical⟩

theorem MixedLcgGood.stepNarrowSync {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : MixedLcgGood leaf orig bs)
    {d : ProductiveDeduction leaf bs} (hd : explainedDeduction original props bs = some d) :
    MixedLcgGood leaf orig (stepNarrowSync orig bs d) := by
  obtain ⟨hent, hin, hsem⟩ := lcgEvent_of_kit_at_shape (original := original) K.raw_eq K.props_eq
    K.fam K.shape K.fits K.contract hg.reach hg.frameState d hd
  have hl := deduction_literal_pooled_at K.vocab hg.db hd
  have hpay := databaseAlignedAt_deduction_learned K.vocab hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepNarrowSync_lcgReachable d
      (lcgExplainedStep_narrow_reachable hg.reach d.filtered (explainedDeduction_fresh hd) hin
        (explainedDeduction_learned_entailed hd hent) hent hsem) K.fits
  · exact frameJ_stepNarrowSync_shape K.shape bs d hg.fj
  · rw [stepNarrowSync_frame]; exact frameShape_filter d.filtered hg.fs
  · have hv0 : TrailVocabularyAt (litPool orig)
        (narrowState bs d.frame d.literal d.reason d.learned).trail := by
      show TrailVocabularyAt (litPool orig) (bs.trail ++
        [{ literal := d.literal.norm, level := bs.level, reason := some { clause := d.reason } }])
      exact trailVocabularyAt_append_entry hg.voc (by rw [norm_norm]; exact hl)
    exact syncSlot_trail_vocab (orig := orig) _ d.literal.atom.slot (fun l hl => hl) hv0
  · rw [stepNarrowSync_learned]
    exact databaseAlignedAt_append hpay hg.db

  · exact boolPinsOn_stepNarrowSync bs d hg.boolPins
  · apply stepNarrowSync_canonical _ hg.canonical hd
    rw [K.props_eq, K.raw_eq]
    exact clampProps_canonical orig (emissionCanonical_of_families K.fam)

theorem MixedLcgGood.closure {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : MixedLcgGood leaf orig bs) :
    MixedLcgGood leaf orig (explainedClosure orig original props bs) :=
  explainedClosure_induction orig original props (fun b => MixedLcgGood leaf orig b)
    (fun _b _d hd h => h.stepNarrowSync K hd) bs hg

end LeanFzn.Solver.UIP.LcgMixedGood
