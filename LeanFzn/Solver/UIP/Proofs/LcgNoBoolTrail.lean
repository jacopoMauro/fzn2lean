/-
File: LeanFzn/Solver/UIP/Proofs/LcgNoBoolTrail.lean

DL (decide-site liveness), part 2: no trail literal of a supported LCG run is a Boolean-atom
literal (the box is integer-valued). State-level arm lemmas: pushes, synchronisation, closure.
-/
import LeanFzn.Solver.UIP.Proofs.LcgNoBoolEmit
import LeanFzn.Solver.UIP.Proofs.LcgRunStep
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgNoBool

namespace LeanFzn.Solver.UIP.LcgNoBoolTrail

variable {leaf : Assignment → Bool}

/-- Every trail literal is an order/removal literal. -/
def NBTrail (tr : List TrailEntry) : Prop := ∀ e ∈ tr, NoBoolAtom e.literal

theorem noBoolAtom_negate (l : Literal) : NoBoolAtom l.negate ↔ NoBoolAtom l := by
  obtain ⟨a, p⟩ := l
  simp [NoBoolAtom, Literal.negate]

theorem noBoolAtom_norm (l : Literal) : NoBoolAtom l.norm ↔ NoBoolAtom l := by
  obtain ⟨a, p⟩ := l
  cases a with
  | boolEq s b =>
      have h1 : ¬ NoBoolAtom (⟨.boolEq s b, p⟩ : Literal) := fun h => h s b rfl
      have h2 : ¬ NoBoolAtom (Literal.norm ⟨.boolEq s b, p⟩) := by
        cases p <;> exact fun h => h _ _ rfl
      exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
  | intLe s k => exact Iff.rfl
  | intNe s k => exact Iff.rfl

theorem noBoolAtom_negNe (s : Nat) (k : Int) : NoBoolAtom (negNe s k) := by
  intro s' b h; simp [negNe] at h

theorem nbTrail_snoc {tr : List TrailEntry} {e : TrailEntry} (h : NBTrail tr)
    (he : NoBoolAtom e.literal) : NBTrail (tr ++ [e]) := by
  intro e' he'
  rcases List.mem_append.mp he' with h1 | h1
  · exact h e' h1
  · rw [List.mem_singleton.mp h1]; exact he

theorem noBoolAtom_snapLit (orig : List Domain) (l : Literal) :
    NoBoolAtom l → NoBoolAtom (snapLit orig l) := by
  intro h
  obtain ⟨a, p⟩ := l
  cases a with
  | boolEq s b => exact absurd rfl (h s b)
  | intLe s k =>
      unfold snapLit
      simp only
      split
      · exact h
      · split
        · exact h
        · intro s' b hh; simp at hh
  | intNe s k =>
      unfold snapLit
      simp only
      split
      · exact h
      · split
        · exact h
        · intro s' b hh; simp at hh

/-- Frame domains of an integer box (given the fits-in-box fact) are integer-valued. -/
theorem domains_ints {orig : List Domain} {F : BranchFrame} (hint : AllIntBox orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []) :
    ∀ d ∈ Frame.domains F, ∀ v ∈ d, ∃ k : Int, v = Value.int k := by
  intro d hd v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have : (Frame.domains F).getD i [] = (Frame.domains F)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [← this] at hv
  exact allInt_getD hint i v (hfits i v hv)

theorem intState_frameState {orig : List Domain} {F : BranchFrame} (hint : AllIntBox orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []) :
    IntState (frameState F) := domains_ints hint hfits

theorem frameInts_of {orig : List Domain} {F : BranchFrame} (hint : AllIntBox orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []) :
    ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k :=
  fun d hd => domains_ints hint hfits d (List.mem_append_right _ hd)

/-! ## Synchronisation pushes -/

theorem syncCands_nb {orig : List Domain} {F : BranchFrame} {s : Nat}
    (hF : ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k) :
    ∀ lit ∈ syncCands orig F s, NoBoolAtom lit.norm := by
  intro lit hlit
  obtain ⟨-, hs, d, hd, h⟩ := syncCands_cases hlit
  rw [noBoolAtom_norm]
  rcases h with ⟨lo, -, -, rfl⟩ | ⟨hi, -, -, rfl⟩ | ⟨i, -, -, rfl⟩ | ⟨b, hdb, rfl⟩ |
    ⟨lo, hi, h0, -, -, -, rfl⟩
  · exact noBoolAtom_negLe _ _
  · exact noBoolAtom_posLe _ _
  · exact noBoolAtom_negNe _ _
  · exfalso
    obtain ⟨k, hk⟩ := hF d (List.mem_of_getElem? hd) (Value.bool b) (by rw [hdb]; simp)
    cases hk
  · exact noBoolAtom_posNe _ _

theorem nbTrail_syncSlot {orig : List Domain} (bs : BranchState leaf) (s : Nat)
    (hF : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k) (h : NBTrail bs.trail) :
    NBTrail (syncSlot orig bs s).trail :=
  syncSlot_trail_prop orig bs s (Q := NoBoolAtom) (syncCands_nb hF) h

theorem nbTrail_syncAll {orig : List Domain} (bs : BranchState leaf)
    (hF : ∀ d ∈ bs.frame.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k) (h : NBTrail bs.trail) :
    NBTrail (syncAll orig bs).trail :=
  syncAll_trail_prop orig bs (Q := NoBoolAtom) (fun _ _ => syncCands_nb hF) h

/-! ## The deduction literal -/

/-- Every deduction of a supported run is over an order/removal atom. -/
theorem deduction_literal_nb {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs)
    {d : ProductiveDeduction leaf bs}
    (hd : explainedDeduction original props bs = some d) : NoBoolAtom d.literal := by
  obtain ⟨c, lr, fl, hev, -, -⟩ := explainedDeduction_learned_shape hd
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨-, -, hrem⟩ := scanDatabase_implied_facts hsrc
    have h1 : d.literal ∈ clauseRemaining bs.frame c := by
      rw [hrem]; exact List.mem_singleton_self _
    have h2 := (List.mem_filter.mp h1).2
    have hnot : literalImpossible bs.frame d.literal = false := by simpa using h2
    exact not_boolEq_of_remaining K.int hg.fj hnot
  · obtain ⟨p, hpm, r, hrun, -, -, -⟩ := scanPropagators_implied_facts hprop
    rw [K.props_eq] at hpm
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
    obtain ⟨l0, r0, hrun0, hl, -⟩ := clamp_run_implied hrun
    rw [K.raw_eq] at hp0
    have hst : IntState (frameState bs.frame) := intState_frameState K.int hg.fj.fits
    have := impliedNB_of_families K.fam hp0 hst l0 r0 hrun0
    rw [hl]
    exact noBoolAtom_snapLit orig l0 this

theorem nbTrail_stepNarrowSync {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs) (hnb : NBTrail bs.trail)
    {d : ProductiveDeduction leaf bs}
    (hd : explainedDeduction original props bs = some d) :
    NBTrail (stepNarrowSync orig bs d).trail := by
  have hl := deduction_literal_nb K hg hd
  have hg' := hg.stepNarrowSync K hd
  have hF : ∀ d' ∈ (narrowState bs d.frame d.literal d.reason d.learned).frame.1,
      ∀ v ∈ d', ∃ k : Int, v = Value.int k := by
    have := frameInts_of K.int hg'.fj.fits
    rw [stepNarrowSync_frame] at this
    exact this
  refine nbTrail_syncSlot _ _ hF ?_
  have hpush : (narrowState bs d.frame d.literal d.reason d.learned).trail =
      bs.trail ++ [({ literal := d.literal.norm, level := bs.level, reason := some { clause := d.reason } } : TrailEntry)] := rfl
  rw [hpush]
  exact nbTrail_snoc hnb ((noBoolAtom_norm _).mpr hl)

theorem nbTrail_closure {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs) (hnb : NBTrail bs.trail) :
    NBTrail (explainedClosure orig original props bs).trail := by
  have := explainedClosure_induction orig original props
    (fun b => LcgGood leaf orig b ∧ NBTrail b.trail)
    (fun b d hd h => ⟨h.1.stepNarrowSync K hd, nbTrail_stepNarrowSync K h.1 h.2 hd⟩) bs ⟨hg, hnb⟩
  exact this.2

end LeanFzn.Solver.UIP.LcgNoBoolTrail
