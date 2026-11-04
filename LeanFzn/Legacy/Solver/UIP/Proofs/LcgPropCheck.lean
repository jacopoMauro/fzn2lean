/-
File: LeanFzn/Solver/UIP/Proofs/LcgPropCheck.lean

PLAN L0a: the UIP-layer obligations for `propCheck`
(`LeanFzn.Solver.Propagation.Proofs.PropCheck`): semantic soundness
(`ResSem`, from `FrameExplainedFull` via `FixExpl`/`AbsentExpl`),
syntactic canonicity (`ResCanonical`, from the `posNe`/`posBool` normal
forms), slot typing (`ResTyped`, from `SlotOK` on `dcSlotsFull`) and the
no-Boolean-atom discipline on an integer-valued state. `propCheck` itself
(the definition, `dcSlotsFull`, the `satisfiedB` congruence and the
conflict-entailment obligation) stays in the Propagation layer (UIP
imports Propagation, never the reverse); this module only adds the
obligations that need the UIP trail vocabulary.

No registration or gate change in this module (PLAN L0a sub-box): `propCheck`
is not yet wired into `propagatorOfProved`, and `lcgFamB` is untouched.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.PropCheck: `propCheck`, `dcSlotsFull`,
    the conflict-clause characterization lemmas.
  - LeanFzn.Solver.UIP.Proofs.LcgFamiliesRun: `FrameExplainedFull`.
  - LeanFzn.Solver.UIP.Proofs.LcgCanonicalClauses: `ResCanonical`.
  - LeanFzn.Solver.UIP.Proofs.LcgEmissionTyped: `ResTyped`, `SlotOK`, `LitWF`.
  - LeanFzn.Solver.UIP.Proofs.LcgNoBoolEmit: `IntState`, `NoBoolAtom`.

DAG:
  LeanFzn.Solver.Propagation.Proofs.PropCheck
    + LeanFzn.Solver.UIP.Proofs.LcgFamiliesRun
    + LeanFzn.Solver.UIP.Proofs.LcgCanonicalClauses
    + LeanFzn.Solver.UIP.Proofs.LcgNoBoolEmit
    -> LeanFzn.Solver.UIP.Proofs.LcgPropCheck (this file)
    -> LeanFzn.Solver.UIP.Proofs.LcgPropCheck consumers (L0b).
-/
import LeanFzn.Solver.Propagation.Proofs.PropCheck
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalClauses
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgNoBoolEmit
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies
open LeanFzn.Solver.UIP.LcgCanonicalClauses LeanFzn.Solver.UIP.LcgEmissionTyped
open LeanFzn.Solver.UIP.LcgNoBool

namespace LeanFzn.Solver.UIP.LcgPropCheck

variable {leaf : Assignment → Bool}

/-- **Semantic soundness** (PLAN L0a): under the frame-explanation
invariant, `propCheck`'s result is semantically justified by the current
trail — it never implies, and a reported conflict clause is semantically
falsified, every literal being exactly the `FixExpl`/`AbsentExpl`
falsified form of a singleton slot. -/
theorem propCheck_sem {orig : List Domain} {bs : BranchState leaf}
    (hF : FrameExplainedFull orig bs) (dc : DomConstraint) :
    ResSem orig bs.trail ((propCheck dc).run (frameState bs.frame)) :=
  propCheck_sem_aux hF dc

/-- **Canonicity** (PLAN L0a): `propCheck`'s result is already
normalized — a reported conflict clause's literals are all `posNe`/
`posBool` normal forms. -/
theorem propCheck_canonical (dc : DomConstraint) (st : State) :
    ResCanonical ((propCheck dc).run st) := by
  cases hres : (propCheck dc).run st with
  | stable => trivial
  | implied l r => exact (propCheck_implied_elim hres).elim
  | conflict c =>
      obtain ⟨-, -, hc⟩ := propCheck_conflict_inv hres
      intro q hq
      rw [hc] at hq
      exact propCheckConflict_literal_norm hq

/-- **Typing** (PLAN L0a): under `ShapeTypedDomains orig` and `SlotOK` on
every slot `dc` reads, `propCheck`'s result is well-slotted. -/
theorem propCheck_typed {orig : List Domain} (hsh : ShapeTypedDomains orig)
    {dc : DomConstraint} (hslot : ∀ s ∈ dcSlotsFull dc, SlotOK orig s) (st : State) :
    ResTyped orig ((propCheck dc).run st) := by
  cases hres : (propCheck dc).run st with
  | stable => exact resTyped_stable orig
  | implied l r => exact (propCheck_implied_elim hres).elim
  | conflict c =>
      obtain ⟨-, -, hc⟩ := propCheck_conflict_inv hres
      refine resTyped_conflict ?_
      intro q hq
      rw [hc] at hq
      exact litWF_of_slotOK hsh (hslot _ (propCheckConflict_atomSlot_mem hq))

/-- **No Boolean atom on an integer-valued state** (PLAN L0a): if every
domain of the state is integer-only, `propCheck`'s conflict clause (when
reported) never carries a Boolean-atom literal — an integer-valued state
has no Boolean singleton to contribute `posBool`. -/
theorem propCheck_noBool {st : State} (h : IntState st) (dc : DomConstraint) :
    ∀ c, (propCheck dc).run st = .conflict c → ∀ q ∈ c, NoBoolAtom q := by
  intro c hres q hq
  obtain ⟨-, -, hc⟩ := propCheck_conflict_inv hres
  rw [hc] at hq
  obtain ⟨s, -, hbind⟩ := mem_propCheckConflict_iff.mp hq
  obtain ⟨v, hv, hv2⟩ := Option.bind_eq_some_iff.mp hbind
  cases v with
  | int c' =>
      simp only [singletonLit] at hv2
      injection hv2 with hv2
      rw [← hv2]
      exact noBoolAtom_posNe s c'
  | bool b =>
      exfalso
      obtain ⟨k, hk⟩ := intState_getD h s (.bool b) (by
        show Value.bool b ∈ Dom.enum (st.domains.getD s Dom.empty)
        rw [frameSingleton_iff.mp hv]; exact List.mem_singleton_self _)
      simp at hk
  | setOfInt w => simp [singletonLit] at hv2
  | array w => simp [singletonLit] at hv2

end LeanFzn.Solver.UIP.LcgPropCheck
