/-
File: LeanFzn/Solver/UIP/Proofs/ClosureRefutation.lean

PURPOSE (P1 evidence): the retained counterexample showing that the
∀-state form of the closure's learned-database discipline is FALSE.

`ClosureContract`'s `pivot`/`chronology` fields quantify over EVERY
`ReachableState`-coherent branch, not only over branches of an actual
run. A *live* (all remaining domains nonempty), coherent state whose
learned database contains a clause that is unit for the frame — but
whose co-member has no recorded falsifier — refutes the contract as
stated. This is the live-frame successor of the coverless-frame
refutation that motivated the `frameLiveB` gate: the gate fixes the
coverless case, but a live frame with a spurious (reachable-coherent but
run-unreachable) learned multi-clause still breaks `StepChronology`.

The consequence for P1 is the interface decision recorded in
coordination.md: the learned half of the closure must be relativized to
the ACTUAL run (N1's `UnitRunInvariant` gives `UnitLearned` at every
reachable configuration of the supported kit, and a normalized unit is
its own pivot — `unit_clause_provenance`), not stated over all
`ReachableState`s.

DAG: BranchState + ExplainedPropagation + Pruning (leaf).
-/
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.Propagation.ExplainedPropagation
import LeanFzn.Solver.Propagation.DomExplained
import LeanFzn.Solver.Propagation.Pruning
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## The witness -/

/-- The witness leaf: true exactly when slot 0 carries `true`. -/
private def refLeaf : Assignment → Bool :=
  fun a => ((posBool 0 true).eval a == some true)

/-- One Boolean slot. -/
private def refDomains : List Domain := [[.bool true, .bool false]]

/-- The original database: the single unit clause pinning slot 0 true. -/
private def refOriginal : List Clause := [[posBool 0 true]]

/-- The witness frame: the whole box at prefix `[]`. -/
private def refFrame : BranchFrame := (refDomains, [])

/-- The spurious learned clause: unit for the frame (slot 1 is ABSENT
from the frame, so its `posBool 1 true` member is frame-impossible and
filtered by `clauseRemaining`), but multi-literal, so its provenance
would need a recorded falsifier of `posBool 1 true`. -/
private def refC : Clause := [posBool 0 true, posBool 1 true]

/-- The witness branch: the box frame, the EMPTY trail, and the spurious
learned clause. Coherent (`ReachableState` holds: every trail field is
vacuous and the clause is globally entailed because the leaf forces slot
0 true) yet no recorded falsifier exists for the co-member. -/
private def refBs : BranchState refLeaf :=
  { frame := refFrame, trail := [], level := 0, learned := [refC] }

/-! ## Coherence of the witness -/

private theorem ref_length_ok : (fullDomains refBs.frame).length
    = refDomains.length := rfl

private theorem ref_full_fits : ∀ i v,
    v ∈ (fullDomains refBs.frame).getD i [] → v ∈ refDomains.getD i [] := by
  intro i v hv
  simpa [refBs, refFrame, refDomains, fullDomains, Frame.domains] using hv

private theorem ref_prefix_forced :
    PrefixForced refBs.trail refDomains refBs.frame.2 := by
  intro a _ _ i hi
  simp [refBs, refFrame] at hi

private theorem ref_agrees : ∀ e ∈ refBs.trail, ∀ a, FrameCovers refBs.frame a →
    e.literal.eval a = some true := by
  intro e he
  simp [refBs] at he

private theorem ref_narrowing_complete :
    NarrowingComplete refBs.trail refDomains refBs.frame := by
  intro i w hw hnot
  exact absurd (by simpa [refBs, refFrame, refDomains] using hw) hnot

private theorem ref_wf : refBs.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp [refBs] at he
  · intro e he
    simp [refBs] at he
  · intro e he
    simp [refBs] at he
  · intro e he
    simp [refBs] at he
  · intro c hc a hleaf
    have hc' : c = refC := by simpa [refBs] using hc
    subst hc'
    refine ⟨posBool 0 true, List.mem_cons_self .., ?_⟩
    simpa [refLeaf] using hleaf

private theorem ref_sorted : TrailLevelSorted refBs.trail := levelSorted_nil

private theorem ref_distinct : TrailLiteralsDistinct refBs.trail :=
  TrailLiteralsDistinct.nil

/-- **THE WITNESS IS COHERENT**: the spurious state satisfies the full
eight-field `ReachableState` invariant. -/
theorem refBs_reachable : ReachableState refLeaf refDomains refBs :=
  ⟨ref_length_ok, ref_full_fits, ref_prefix_forced, ref_agrees,
    ref_narrowing_complete, ref_wf, ref_sorted, ref_distinct⟩

/-! ## The event fires at the witness -/

/-- The scan selects the spurious clause: its remaining shape is the unit
`posBool 0 true`, narrowing is productive, and the frame is live — so
the extended `.implied` event is NOT gated to `.stable`. -/
theorem refBs_event :
    nextPruningEvent refOriginal [] refBs.frame refBs.learned =
      .implied (posBool 0 true) refC false true := rfl

/-- The `chronology` obligation fails at the witness: the co-member
`posBool 1 true` has no recorded falsifier on the empty trail. -/
theorem refBs_chronology_fails : ¬ StepChronology refBs (posBool 0 true) refC := by
  intro h
  obtain ⟨e, he, helit⟩ :=
    h (posBool 1 true) (by decide) (by decide)
  simp [refBs] at he

/-- **THE REFUTATION** (retained as the justification of the unit gate):
the UNGATED form of the contract's `chronology` field — quantified over
every coherent `ReachableState` — is FALSE. It is instantiated at the
coherent witness state and the selected live event; the co-member's
falsifier does not exist. Hence any producer stated over ALL
`ReachableState`s (the former `hShape` premise of
`supportedHclos_of_compiled`) is unsound; the learned half must be
RELATIVIZED to the unit-database discipline, under which the same content
is free (`hshape_of_unitLearned`, `Proofs/DomExplained.lean`). This
refutation is the recorded reason for the `UnitDB` gate now present on
`ClosureContract.pivot`/`.chronology`. -/
theorem chronology_without_unitGate_false :
    ¬ (∀ (bs : BranchState refLeaf), ReachableState refLeaf refDomains bs →
        ∀ (l : Literal) (c : Clause) (lr fl : Bool),
          nextPruningEvent refOriginal [] bs.frame bs.learned
            = .implied l c lr fl →
          StepChronology bs l c) := by
  intro h
  exact refBs_chronology_fails
    (h refBs refBs_reachable (posBool 0 true) refC false true refBs_event)

/-- The `hShape`-shaped premise of the compiled closure provider is
likewise refuted at the witness: `clauseRemaining refBs.frame refC` is
the unit `[posBool 0 true]` (the co-member is frame-impossible), the
frame is live, yet no recorded pivot exists. -/
theorem hShape_false_at_refBs :
    ¬ (∀ (c : Clause) (l : Literal), c ∈ refBs.learned →
        clauseRemaining refBs.frame c = [l] → frameLiveB refBs.frame = true →
        ∃ p : Literal, RecordedWith refLeaf refBs c p ∧ l.norm = p) := by
  intro h
  obtain ⟨p, hp, -⟩ :=
    h refC (posBool 0 true) (by simp [refBs])
      (by decide) (by decide)
  have h1 : p = (posBool 0 true) ∨ p = (posBool 1 true) := by
    have hp' : p ∈ refC := by rw [hp.2.1]; trivial
    simpa [refC] using hp'
  rcases h1 with rfl | rfl
  · have hf := hp.2.2 (posBool 1 true) (by decide) (by decide)
    simp [refBs] at hf
  · have hf := hp.2.2 (posBool 0 true) (by decide) (by decide)
    simp [refBs] at hf

end LeanFzn.Solver.UIP
