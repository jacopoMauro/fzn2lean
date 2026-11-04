/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedRunDrop.lean
A2d: shape-typed (mixed integer/Boolean) versions of the frame-coverage and
dead-site helpers of `LcgRunDrop`: `propagate_covers`, `skip_covers`,
`closure_frameSnd`, `terminal_conflict_dead` and `stableNone_dead_lcg` over
`MixedLcgKit`/`MixedLcgGood`. The statements are the direct
`ShapeTypedDomains` analogues (the integer `AllIntBox` hypothesis is replaced
by the shape discipline, and the event/reason producers by their mixed
counterparts); every supporting fact is reused, not reproved.
One local helper is added: `unsupportedHead_absent_of_lcgReach` discharges the
`stableNone` unsupported-head case for the shape discipline, by the exact
proof of `SchedulerArmsPreserve.unsupportedHead_absent_of_shape` with
`LcgReachableState.full_fits` in place of `ReachableState.full_fits`.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunDrop
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedDecisions
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgBooleanFalsity
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerArmsPreserve
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgRunArms LeanFzn.Solver.UIP.LcgRunConflict
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedEvents
open LeanFzn.Solver.UIP.LcgMixedDecisions LeanFzn.Solver.UIP.LcgRunDrop

namespace LeanFzn.Solver.UIP.LcgMixedRunDrop

variable {leaf : Assignment → Bool}

/-! ## Propagation -/

theorem propagate_covers_shape {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : MixedLcgGood leaf orig bs)
    {d : ProductiveDeduction leaf bs} (hd : explainedDeduction original props bs = some d) :
    ∀ a, leaf a = true → FrameCovers bs.frame a → FrameCovers d.frame a := by
  intro a ha hcv
  obtain ⟨hent, -, hsem⟩ := lcgEvent_of_kit_at_shape (original := original) K.raw_eq K.props_eq
    K.fam K.shape K.fits K.contract hg.reach hg.frameState d hd
  have hsat := hent d.reason (List.mem_singleton_self _) a ha
  have h1 := pivot_true hsem (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv) hsat
  rw [norm_norm, Literal.norm_eval] at h1
  obtain ⟨g, hgf, hcv'⟩ := filterFrame_preserves hcv h1
  have hg' : g = d.frame := Option.some.inj (hgf.symm.trans d.filtered)
  rw [← hg']
  exact hcv'

/-! ## Split / skip -/

theorem skip_covers_shape {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hs : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (cfg.branch.frame.pin k v) a := by
  have hpin := lcgPinFits_shape hs hreach hshape
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons ((splitData_eq_some_iff.mp hs).2.1)
  intro a ha hcov
  have h1 : (l.norm).eval a = some true := by
    have h3 := hreach.agrees e he a hcov
    rwa [hil] at h3
  have hread := (hpin a (hfits a ha)).mp h1
  exact (SparseFrame.Frame.covers_pin_iff hd
    ((DomainLike.mem_iff d v).mpr (by
      rw [domElems_eq_enum, hde]
      exact List.mem_cons_self)) a).mpr ⟨hcov, hread⟩

/-! ## The propagation closure -/

theorem closure_frameSnd_shape {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : MixedLcgGood leaf orig bs) (hs : FrameSndOrder leaf bs.frame) :
    FrameSndOrder leaf (explainedClosure orig original props bs).frame := by
  have := explainedClosure_induction orig original props
    (fun b => MixedLcgGood leaf orig b ∧ FrameSndOrder leaf b.frame)
    (fun b d hd h => by
      refine ⟨MixedLcgGood.stepNarrowSync K h.1 hd, ?_⟩
      rw [stepNarrowSync_frame]
      intro a ha hp
      have hp' : Frame.PinsOnOrder b.frame a := by
        intro j hj w hjw
        have hjd : j ∈ (d.frame).order := by
          rw [Frame.filterFrame_order d.filtered]
          exact hj
        exact hp j hjd w (filterFrame_singleton d.filtered hjw)
      exact propagate_covers_shape K h.1 hd a ha (h.2 a ha hp')) bs ⟨hg, hs⟩
  exact this.2

/-! ## Dead sites -/

theorem terminal_conflict_dead_shape {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs s : BranchState leaf} (hg : MixedLcgGood leaf orig bs) {cs learned : List Clause}
    (ht : terminalResult orig original props bs = .conflict s cs learned) :
    ∀ a, leaf a = true → ¬ FrameCovers bs.frame a := by
  intro a ha hcv
  obtain ⟨-, h⟩ := terminalResult_conflict_cases ht
  rcases h with ⟨hev, -⟩ | ⟨l, c, lr, fl, hev, hnone, hcs, -⟩ | ⟨w, hev, hw, hcs, -⟩
  · rcases nextPruningEvent_conflict_cases hev with hdb | ⟨-, hview, hprop⟩
    · obtain ⟨c, hmem, hunit, -⟩ := scanDatabase_conflict_facts hdb
      exact clauseRemaining_empty_excludes hcv hunit (hg.reach.learned_ent c hmem a ha)
    · obtain ⟨p, hpm, c, hrun, -⟩ := scanPropagators_conflict_facts hprop
      rw [K.props_eq] at hpm
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
      obtain ⟨c0, hrun0, -⟩ := clamp_run_conflict hrun
      exact K.contract.conflict bs.frame hview p0 hp0 c0 hrun0 a ha hcv
  · have hP : ∀ p ∈ props, PropSemContract orig p bs :=
      propSem_of_state K.raw_eq K.props_eq K.fam
        (frameExplainedFull_of_frameJ_shape K.shape hg.fj hg.boolPins) hg.frameState.snap
    have hsem := nextPruningEvent_implied_sem_shape K.shape hg.fj hg.fs hg.boolPins hg.canonical
      hP hev
    have hent := LeanFzn.Solver.UIP.LcgMixedConflict.implied_reason_entailed K hg.reach hev
    have h1 := pivot_true hsem (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv)
      (hent c (List.mem_singleton_self _) a ha)
    rw [Literal.norm_eval] at h1
    obtain ⟨g, hgf, -⟩ := filterFrame_preserves hcv h1
    rw [hnone] at hgf
    cases hgf
  · exact wipeoutClause_excludes hw (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv)

/-- The unsupported-head case is vacuous under the shape discipline at an
`LcgReachableState` (the proof of `unsupportedHead_absent_of_shape` with
`LcgReachableState.full_fits`; both int and bool values are covered by the
shape split). -/
theorem unsupportedHead_absent_of_lcgReach {orig : List Domain} {bs : BranchState leaf}
    (hshape : ShapeTypedDomains orig)
    (hreach : LcgReachableState leaf orig bs) :
    ¬ ∃ (k : Nat) (v : Value) (vs : Domain),
      bs.frame.doms[k]?.map Dom.enum = some (v :: vs.enum) ∧
        valueLiteral k v = none := by
  rintro ⟨k, v, vs, hdom, hnone⟩
  obtain ⟨d, hdk, -⟩ := exists_dom_of_enum_cons hdom
  have hk : k < bs.frame.doms.length := (List.getElem?_eq_some_iff.mp hdk).1
  have hmem : v ∈ (fullDomains bs.frame).getD k Dom.empty := by
    show v ∈ (bs.frame.doms.getD k Dom.empty)
    exact (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum, enum_getD_of_enum_cons hdom]
      exact List.mem_cons_self)
  have hfit : v ∈ orig.getD k Dom.empty := hreach.full_fits _ _ hmem
  have hkO : k < orig.length := by
    rw [← hreach.length_ok, fullDomains_length]
    exact hk
  have hdmem : orig.getD k Dom.empty ∈ orig := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkO]
    exact List.getElem_mem hkO
  rcases hshape _ hdmem with hint | hbool
  · obtain ⟨i, rfl⟩ := hint v hfit
    simp [valueLiteral] at hnone
  · obtain ⟨b, rfl⟩ := hbool v hfit
    simp [valueLiteral] at hnone

theorem stableNone_dead_lcg_shape {orig : List Domain} {cfg : SchedulerConfig leaf}
    (hshape : ShapeTypedDomains orig) (hr : LcgReachableState leaf orig cfg.branch)
    (hwit : leafWitness leaf cfg = none) (hsp : splitData cfg.branch.frame cfg.prio = none) :
    ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a :=
  stableNone_dead hwit hsp (fun h => absurd h (unsupportedHead_absent_of_lcgReach hshape hr))

end LeanFzn.Solver.UIP.LcgMixedRunDrop
