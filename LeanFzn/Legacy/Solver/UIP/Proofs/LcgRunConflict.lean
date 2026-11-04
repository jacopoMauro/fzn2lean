/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunConflict.lean
H2c (part 2): entailment of the terminal conflict payload and of the selected implied event's
reason, at a single `LcgReachableState` (no `hbr`).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunGood
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood

namespace LeanFzn.Solver.UIP.LcgRunConflict

variable {leaf : Assignment → Bool}

theorem allInt_viewed {orig : List Domain} (h : AllIntBox orig) :
    ∀ d ∈ orig, ∀ v ∈ d, Value.intView v ≠ none := by
  intro d hd v hv
  obtain ⟨k, rfl⟩ := h d hd v hv
  simp [Value.intView]

theorem allInt_domsShape {orig : List Domain} (h : AllIntBox orig) : DomsShapeTyped orig :=
  fun d hd => Or.inl (h d hd)

/-- The reason clause of any selected implied event is globally entailed. -/
theorem implied_reason_entailed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    {l : Literal} {c : Clause} {lr fl : Bool}
    (hev : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl) :
    LearnedEntailed leaf [c] := by
  intro c' hc' a ha
  rw [List.mem_singleton] at hc'
  subst hc'
  rcases nextPruningEvent_implied_cases hev with hdb | ⟨-, hview, hprop⟩
  · obtain ⟨hmem, -, -⟩ := scanDatabase_implied_facts hdb
    exact hreach.learned_ent _ hmem a ha
  · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ := scanPropagators_implied_facts hprop
    rw [hcl]
    rw [K.props_eq] at hpm
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
    obtain ⟨l0, r0, hrun0, -, hcl0⟩ := clamp_run_implied hrun
    rw [hcl0]
    exact (snapClause_satisfied (K.fits a ha)).mpr
      (K.contract.reason _ hview p0 hp0 l0 r0 hrun0 a ha)

/-- Every clause of a selected conflict event is globally entailed. -/
theorem conflict_event_entailed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    {cs : List Clause}
    (hev : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    LearnedEntailed leaf cs := by
  rcases nextPruningEvent_conflict_cases hev with hdb | ⟨hsd, hview, hprop⟩
  · obtain ⟨c, hmem, hunit, hcs⟩ := scanDatabase_conflict_facts hdb
    rw [hcs]
    intro c' hc' a hleaf
    rw [List.mem_singleton] at hc'
    rw [hc']
    exact hreach.learned_ent c hmem a hleaf
  · obtain ⟨p, hpm, c, hrun, hcs⟩ := scanPropagators_conflict_facts hprop
    rw [hcs]
    intro c' hc' a hleaf
    obtain ⟨hc'', hne⟩ := mem_conflict_payload hc'
    rw [hc'']
    rw [K.props_eq] at hpm
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
    obtain ⟨c0, hrun0, hc0⟩ := clamp_run_conflict hrun
    have hne0 : c0 ≠ [] := by
      intro h0; apply hne; rw [hc0, h0]; rfl
    rw [hc0]
    exact (snapClause_satisfied (K.fits a hleaf)).mpr
      (K.contract.conflictReason bs.frame hview p0 hp0 c0 hrun0 hne0 a hleaf
        (frameFaithful_of_domSub (allInt_viewed K.int) (allInt_domsShape K.int) (K.fits a hleaf)
          ⟨hreach.length_ok, hreach.full_fits⟩))

/-- **The terminal conflict payload is entailed**, and the reported new clauses are among it. -/
theorem terminal_conflict_entailed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs s : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    {cs learned : List Clause}
    (ht : terminalResult orig original props bs = .conflict s cs learned) :
    LearnedEntailed leaf cs ∧ (∀ c ∈ learned, c ∈ cs) := by
  obtain ⟨-, h⟩ := terminalResult_conflict_cases ht
  rcases h with ⟨hev, hl⟩ | ⟨l, c, lr, fl, hev, -, hcs, hl⟩ | ⟨w, hev, hw, hcs, hl⟩
  · exact ⟨conflict_event_entailed K hreach hev, by
      intro c hc; rw [hl] at hc; exact (List.mem_filter.mp hc).1⟩
  · refine ⟨?_, ?_⟩
    · rw [hcs]; exact implied_reason_entailed K hreach hev
    · intro c' hc'
      rw [hl] at hc'
      rw [hcs]
      split at hc'
      · simpa using hc'
      · simp at hc'
  · refine ⟨?_, ?_⟩
    · rw [hcs]
      intro c' hc' a hleaf
      rw [List.mem_singleton] at hc'
      rw [hc']
      exact wipeoutClause_entailed hw (K.fits a hleaf)
    · intro c' hc'
      rw [hl] at hc'
      simp at hc'

end LeanFzn.Solver.UIP.LcgRunConflict
