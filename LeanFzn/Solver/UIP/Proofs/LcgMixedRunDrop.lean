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
import LeanFzn.Solver.UIP.Proofs.LcgRunDrop
import LeanFzn.Solver.UIP.Proofs.LcgMixedDecisions
import LeanFzn.Solver.UIP.Proofs.LcgMixedConflict
import LeanFzn.Solver.UIP.Proofs.LcgBooleanFalsity
import LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve
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
    {v : Value} {vs : Domain} {doms : List Domain}
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a := by
  have hpin := lcgPinFits_shape hs hreach hshape
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have hslots := (splitData_eq_some_iff.mp hs).1
  intro a ha hcov
  have h1 : (l.norm).eval a = some true := by
    have h3 := hreach.agrees e he a hcov
    rwa [hil] at h3
  have hslot := (hpin a (hfits a ha)).mp h1
  obtain ⟨tail, htail, heq⟩ := hcov
  have htail' : tail ∈ allAssigns ((v :: vs) :: doms) := by
    rwa [← hslots]
  obtain ⟨w, hw, suffix, hsuffix, rfl⟩ := (mem_allAssigns_singleton v vs doms tail).mp htail'
  have hwv : w = v := by
    have hget : (cfg.branch.frame.2 ++ (w :: suffix))[cfg.branch.frame.2.length]? = some w := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [heq, hget] at hslot
    exact Option.some.inj hslot
  subst hwv
  refine ⟨suffix, hsuffix, ?_⟩
  rw [heq]
  simp only [List.append_assoc, List.singleton_append]

/-! ## The propagation closure -/

theorem closure_frameSnd_shape {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : MixedLcgGood leaf orig bs) (hs : FrameSnd leaf bs.frame) :
    FrameSnd leaf (explainedClosure orig original props bs).frame := by
  have := explainedClosure_induction orig original props
    (fun b => MixedLcgGood leaf orig b ∧ FrameSnd leaf b.frame)
    (fun b d hd h => by
      refine ⟨MixedLcgGood.stepNarrowSync K h.1 hd, ?_⟩
      rw [stepNarrowSync_frame]
      intro a ha hp
      have hpre : d.frame.2 = b.frame.2 := filterFrame_prefix d.filtered
      rw [hpre] at hp
      exact propagate_covers_shape K h.1 hd a ha (h.2 a ha hp)) bs ⟨hg, hs⟩
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
    ¬ ∃ v vs doms, bs.frame.1 = (v :: vs) :: doms ∧
      valueLiteral bs.frame.2.length v = none := by
  rintro ⟨v, vs, doms, hslots, hnone⟩
  have hmem : v ∈ (fullDomains bs.frame).getD bs.frame.2.length [] := by
    rw [List.getD_eq_getElem?_getD]
    have hfr := fullDomains_remaining (f := bs.frame) (i := 0)
    rw [Nat.add_zero, hslots] at hfr
    rw [hfr]
    simp
  have hfit : v ∈ orig.getD bs.frame.2.length [] := hreach.full_fits _ _ hmem
  have hdmem : orig.getD bs.frame.2.length [] ∈ orig := by
    rw [List.getD_eq_getElem?_getD]
    cases hgt : orig[bs.frame.2.length]? with
    | none =>
        rw [List.getD_eq_getElem?_getD] at hfit
        rw [hgt] at hfit
        simp only [Option.getD_none] at hfit
        exact absurd hfit (List.not_mem_nil)
    | some d => simpa using List.mem_of_getElem? hgt
  rcases hshape _ hdmem with hint | hbool
  · obtain ⟨k, rfl⟩ := hint v hfit
    simp [valueLiteral] at hnone
  · obtain ⟨b, rfl⟩ := hbool v hfit
    simp [valueLiteral] at hnone

theorem stableNone_dead_lcg_shape {orig : List Domain} {cfg : SchedulerConfig leaf}
    (hshape : ShapeTypedDomains orig) (hr : LcgReachableState leaf orig cfg.branch)
    (hwit : leafWitness leaf cfg = none) (hsp : splitData cfg.branch.frame = none) :
    ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a :=
  stableNone_dead hwit hsp (fun h => absurd h (unsupportedHead_absent_of_lcgReach hshape hr))

end LeanFzn.Solver.UIP.LcgMixedRunDrop
