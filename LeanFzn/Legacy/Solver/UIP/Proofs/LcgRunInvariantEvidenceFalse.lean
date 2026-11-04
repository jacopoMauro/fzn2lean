/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantEvidenceFalse.lean
U1c finding 2: `LcgRunInv.evidence` (the recorded conflict clause is semantically falsified by the
trail or the root) is FALSE along real supported runs.

The original witness (one forced decision on a singleton slot, whose sibling frame emptied that
slot) is no longer reachable after the S1 minimum-cardinality `selectSlot`/sparse-frame
migration: `splitData` only splits LIVE slots (`Frame.split_live`), `pin` writes a singleton and
`retire` keeps a nonempty tail, and `explainedDeduction` never narrows to an empty domain.  The
refutation is therefore re-witnessed on a frame shape the migrated scheduler actually builds:

Witness (no propagators): box `x ∈ {false, 5}`, `y ∈ {0,1}`, original clause `[x > 4 ∨ x = 5]`.
`x` is the S1-selected slot (cardinality 2, smallest index), its head value is the Boolean
`false`, so the first transition is the real decision `posBool 0 false` (the index-1 sibling is
pending).  Pinning `x` to `false` makes both literals of the clause impossible at the frame
(int views: `false ↦ 0`), so the database scan reports the conflict `[x > 4, x = 5]` at level 1,
recorded as evidence with `analysis = none`.

The conflict is not semantically falsified: the decision literal is Boolean, while `x`'s slot is
NOT Boolean-only in `orig` (it also contains the integer `5`), so R3's kind guard of `impliesP`
prevents `posBool 0 false` from implying the int-form negation of `x = 5`; both clause literals
are nonetheless true at the original value `5`.  This is the faithful migrated counterpart of the
old emptied-slot finding: a literal that is impossible in the frame without a single trail
falsifier.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFinal
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

def evLeaf : Assignment → Bool := fun _ => false

def evBox : List Domain :=
  [Dom.ofList [Value.bool false, Value.int 5], Dom.ofList [Value.int 0, Value.int 1]]

def evOriginal : List Clause := [[negLe 0 4, negNe 0 5]]

/-- Iterate the real dispatcher `n` times from a configuration. -/
def iterNext {leaf : Assignment → Bool} : Nat → SchedulerConfig leaf → Option (SchedulerConfig leaf)
  | 0, c => some c
  | n + 1, c => match (schedulerNext c).successor with
      | none => none
      | some c' => iterNext n c'

theorem supportedReach_iterNext {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator} :
    ∀ (n : Nat) {c c' : SchedulerConfig leaf}, SupportedReach orig original props c →
      iterNext n c = some c' → SupportedReach orig original props c' := by
  intro n
  induction n with
  | zero => intro c c' h hi; simp [iterNext] at hi; subst hi; exact h
  | succ n ih =>
      intro c c' h hi
      simp only [iterNext] at hi
      cases hs : (schedulerNext c).successor with
      | none => rw [hs] at hi; cases hi
      | some c1 =>
          rw [hs] at hi
          exact ih (SupportedReach.step h hs) hi

theorem evidence_refuted :
    ∃ cfg : SchedulerConfig evLeaf, SupportedReach evBox evOriginal [] cfg ∧
      ∃ ev, cfg.conflict = some ev ∧
        ¬ ClauseSemFalsifiedR evBox cfg.branch.trail ev.clause := by
  have hinit : SupportedReach (leaf := evLeaf) evBox evOriginal []
      (SchedulerConfig.init evBox evOriginal []) :=
    SupportedReach.init (fun c hc a h => by simp [evLeaf] at h)
  have hshape : (iterNext 2 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal [])).map
      (fun c => (c.conflict.map (·.clause), c.branch.trail.map (·.literal)))
      = some (some [negLe 0 4, negNe 0 5], [posBool 0 false]) := by rfl
  have hsome : (iterNext 2 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal [])).isSome
      = true := by
    cases h : iterNext 2 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal []) with
    | none => rw [h] at hshape; cases hshape
    | some c => rfl
  cases hi : iterNext 2 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal []) with
  | none => rw [hi] at hsome; cases hsome
  | some c =>
      rw [hi] at hshape
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
      obtain ⟨hcl, htr⟩ := hshape
      refine ⟨c, supportedReach_iterNext 2 hinit hi, ?_⟩
      cases hc : c.conflict with
      | none => rw [hc] at hcl; cases hcl
      | some ev =>
          rw [hc] at hcl
          simp only [Option.map_some, Option.some.injEq] at hcl
          refine ⟨ev, rfl, ?_⟩
          intro h
          have hq : negNe 0 5 ∈ ev.clause := by rw [hcl]; simp
          have h1 := h (negNe 0 5) hq
          rcases h1 with h1 | ⟨e, he, himp⟩
          · revert h1; decide
          · have hmem : e.literal ∈ c.branch.trail.map (·.literal) :=
              List.mem_map.mpr ⟨e, he, rfl⟩
            rw [htr] at hmem
            simp only [List.mem_singleton] at hmem
            rw [hmem] at himp
            revert himp
            unfold impliesP impliesBase slotBoolB
            decide

/-- The residual premise `EvidenceRun` is false even for the propagator-free kit. -/
theorem evidenceRun_refuted : ¬ EvidenceRun evBox evOriginal [] evLeaf := by
  intro h
  obtain ⟨cfg, hreach, ev, hev, hnot⟩ := evidence_refuted
  have := h hreach ev hev
  rw [SupportedReach.orig_eq hreach] at this
  exact hnot this

end LeanFzn.Solver.UIP.LcgRunInv
