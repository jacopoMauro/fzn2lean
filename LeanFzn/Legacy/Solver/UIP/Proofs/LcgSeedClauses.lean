/-
File: LeanFzn/Solver/UIP/Proofs/LcgSeedClauses.lean

Purpose:
  The pool-level facts of the compiler's `bool_clause` seed (PLAN C2):
  the seeded clause database is canonical (`DatabaseCanonical`) and
  aligned with the original literal pool (`DatabaseAligned (litPool orig)`)
  as soon as every slot the seeded constraints name is in range. These
  are the two database hypotheses the generalized compiled-kit producers
  consume (`LcgCompiledKit.kit_of_compiled`,
  `LcgMixedCompiledKit.kit_of_compiled_mixed`).
Dependencies: the compiler seed (`Compiler.seedClauses`), the canonical
clause algebra (`LcgCanonicalClauses`) and the pin-pool membership row
(`EmissionVocabulary.pooledEmission_constEqBool`).
DAG: Compiler.SeedClauses + EmissionVocabulary -> this file -> the kit
producers and Integration.Lcg.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalClauses
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedDatabaseFacts
import LeanFzn.Legacy.Solver.UIP.Proofs.EmissionVocabulary
import LeanFzn.Compiler.SeedClauses

namespace LeanFzn.Solver.UIP.LcgSeedClauses
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Compiler
open LeanFzn.Solver.UIP.LcgCanonicalClauses
open LeanFzn.Solver.UIP.LcgEmissionTyped

/-- Every slot a `boolClauseSlot` names is on one of its two sides. -/
theorem mem_dcSlots_boolClauseSlot {ps ns : List Nat} {s : Nat} :
    s ∈ dcSlots (.boolClauseSlot ps ns) ↔ s ∈ ps ∨ s ∈ ns := by
  simp only [dcSlots, List.mem_append]

/-- **THE CANONICAL HALF**: the seeded database is canonical — every
    seed literal is a positive pin, hence in normal form. -/
theorem seedClauses_canonical {dcs : List DomConstraint} :
    DatabaseCanonical (seedClauses dcs) :=
  fun c hc => seedClauses_norm hc

/-- **THE ALIGNMENT HALF**: the seeded database normalizes into the
    original literal pool, given the slot range of the seeded
    constraints (the compiled gate's `dcSlots` condition). -/
theorem seedClauses_aligned {orig : List Domain} {dcs : List DomConstraint}
    (hslots : ∀ dc ∈ dcs, ∀ s ∈ dcSlots dc, s < orig.length) :
    DatabaseAligned orig (seedClauses dcs) := by
  intro c hc q hq
  obtain ⟨ps, ns, hmem, rfl⟩ := seedClauses_mem_inv hc
  have hlt : ∀ s, s ∈ dcSlots (.boolClauseSlot ps ns) → s < orig.length :=
    hslots _ hmem
  rcases mem_boolClauseSeed.mp hq with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · have hi' : i < orig.length :=
      hlt i (mem_dcSlots_boolClauseSlot.mpr (Or.inl hi))
    show (posBool i true).norm ∈ litPool orig
    rw [show (posBool i true).norm = posBool i true from rfl]
    exact pooledEmission_constEqBool hi' true
  · have hj' : j < orig.length :=
      hlt j (mem_dcSlots_boolClauseSlot.mpr (Or.inr hj))
    show (posBool j false).norm ∈ litPool orig
    rw [show (posBool j false).norm = posBool j false from rfl]
    exact pooledEmission_constEqBool hj' false

/-- The same alignment read from `SlotOK` slots (the executable gate's
    shape), for consumers holding `slots_of_mixedGate`-style facts. -/
theorem seedClauses_aligned_of_slotOK {orig : List Domain}
    {dcs : List DomConstraint}
    (hslots : ∀ dc ∈ dcs, ∀ s ∈ dcSlots dc, SlotOK orig s) :
    DatabaseAligned orig (seedClauses dcs) :=
  seedClauses_aligned fun dc hdc s hs =>
    (List.getElem?_eq_some_iff.mp (hslots dc hdc s hs).choose_spec.1).choose

end LeanFzn.Solver.UIP.LcgSeedClauses
