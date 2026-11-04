/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunGood.lean
H2c (part 1): the per-state `LcgGood` bundle (Lcg reachability, frame explanation, shape, pooled
trail vocabulary, pooled database), its preservation by one narrow+sync closure step, and hence
by the whole propagation closure. No `hbr`: every step uses the per-state event conclusion
`lcgEvent_of_kit_at`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEvents
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgAsserting
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantSnap
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents

namespace LeanFzn.Solver.UIP.LcgRunGood

variable {leaf : Assignment → Bool}

/-- The legitimate problem-level hypotheses of the clamped LCG kit. -/
structure LcgKit (leaf : Assignment → Bool) (orig : List Domain) (original : List Clause)
    (dcs : List DomConstraint) (raw props : List Propagator) : Prop where
  raw_eq : raw = dcs.filterMap propagatorOfProved
  props_eq : props = clampProps orig raw
  fam : ∀ dc ∈ dcs, lcgFamB dc = true
  int : AllIntBox orig
  nd : ∀ d ∈ orig, (Dom.enum d).Nodup
  fits : ∀ a, leaf a = true → a.Fits orig
  contract : PropagationContract leaf raw
  typed : EmissionTyped orig raw
  aligned : DatabaseAligned orig original

theorem LcgKit.vocab {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props) :
    EmissionPoolAt (litPool orig) props := by
  rw [K.props_eq]; exact emissionPoolAt_clampProps K.typed

/-- Fuel induction principle for the propagation closure. -/
theorem explainedClosure_induction (orig : List Domain) (original : List Clause)
    (props : List Propagator) (P : BranchState leaf → Prop)
    (hstep : ∀ (bs : BranchState leaf) (d : ProductiveDeduction leaf bs),
      explainedDeduction original props bs = some d → P bs → P (stepNarrowSync orig bs d)) :
    ∀ bs : BranchState leaf, P bs → P (explainedClosure orig original props bs) := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      P bs → P (explainedClosure orig original props bs) from
    fun bs => h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hP
    rw [explainedClosure]
    split
    · exact hP
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hP
    rw [explainedClosure]
    split
    · exact hP
    · rename_i d hd
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      exact ih _ hmass (hstep bs d hd hP)

/-- The per-state bundle. -/
structure LcgGood (leaf : Assignment → Bool) (orig : List Domain) (bs : BranchState leaf) : Prop where
  reach : LcgReachableState leaf orig bs
  fj : FrameJ orig bs.trail bs.frame
  fs : FrameShape orig bs.frame
  voc : TrailVocabularyAt (litPool orig) bs.trail
  db : DatabaseAlignedAt (litPool orig) bs.learned

theorem LcgGood.frameState {orig : List Domain} {bs : BranchState leaf}
    (h : LcgGood leaf orig bs) : LcgFrameState orig bs :=
  ⟨h.fj, h.fs, fun e he => snapLit_fixed_of_norm_pool (h.voc e he)⟩

theorem LcgGood.stepNarrowSync {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs)
    {d : ProductiveDeduction leaf bs} (hd : explainedDeduction original props bs = some d) :
    LcgGood leaf orig (stepNarrowSync orig bs d) := by
  obtain ⟨hent, hin, hsem⟩ := lcgEvent_of_kit_at (original := original) K.raw_eq K.props_eq
    K.fam K.int K.fits K.contract hg.reach hg.frameState d hd
  have hl := deduction_literal_pooled_at K.vocab hg.db hd
  have hpay := databaseAlignedAt_deduction_learned K.vocab hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact stepNarrowSync_lcgReachable d
      (lcgExplainedStep_narrow_reachable hg.reach d.filtered (explainedDeduction_fresh hd) hin
        (explainedDeduction_learned_entailed hd hent) hent hsem) K.fits
  · exact frameJ_stepNarrowSync K.int bs d hg.fj
  · rw [stepNarrowSync_frame]; exact frameShape_filter d.filtered hg.fs
  · have hv0 : TrailVocabularyAt (litPool orig)
        (narrowState bs d.frame d.literal d.reason d.learned).trail := by
      show TrailVocabularyAt (litPool orig) (bs.trail ++
        [{ literal := d.literal.norm, level := bs.level, reason := some { clause := d.reason } }])
      exact trailVocabularyAt_append_entry hg.voc (by rw [norm_norm]; exact hl)
    exact syncSlot_trail_vocab (orig := orig) _ d.literal.atom.slot (fun l hl => hl) hv0
  · rw [stepNarrowSync_learned]
    exact databaseAlignedAt_append hpay hg.db

theorem LcgGood.closure {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs) :
    LcgGood leaf orig (explainedClosure orig original props bs) :=
  explainedClosure_induction orig original props (fun b => LcgGood leaf orig b)
    (fun b d hd h => h.stepNarrowSync K hd) bs hg

end LeanFzn.Solver.UIP.LcgRunGood
