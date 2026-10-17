/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantEvidenceFalse.lean
U1c finding 2: `LcgRunInv.evidence` (the recorded conflict clause is semantically falsified by the
trail or the root) is FALSE along real supported runs: a database clause whose literals lie on an
EMPTIED slot is "impossible" at the frame (`literalImpossible` is vacuous on an empty domain) but
is not falsified by any single trail entry.

Witness (no propagators): box `x ∈ {0,1}`, `y ∈ {0}`, original clause `[y ≤ 5]`.  The sibling
of the (forced) decision `y = 0` is the pending frame `([[]], [0])` (slot `y` EMPTY, level 1);
resuming it makes the database scan report the conflict `[y ≤ 5]`, recorded as evidence at level 1.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

def evLeaf : Assignment → Bool := fun _ => false

def evBox : List Domain := [[Value.int 0, Value.int 1], [Value.int 0]]

def evOriginal : List Clause := [[posLe 1 5]]

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
  have hsome : (iterNext 5 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal [])).isSome
      = true := by rfl
  have hshape : (iterNext 5 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal [])).map
      (fun c => (c.conflict.map (·.clause), c.branch.trail.map (·.literal)))
      = some (some [posLe 1 5], [negNe 0 0, posNe 1 0]) := by rfl
  cases hi : iterNext 5 (SchedulerConfig.init (leaf := evLeaf) evBox evOriginal []) with
  | none => rw [hi] at hsome; cases hsome
  | some c =>
      rw [hi] at hshape
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hshape
      obtain ⟨hcl, htr⟩ := hshape
      refine ⟨c, supportedReach_iterNext 5 hinit hi, ?_⟩
      cases hc : c.conflict with
      | none => rw [hc] at hcl; cases hcl
      | some ev =>
          rw [hc] at hcl
          simp only [Option.map_some, Option.some.injEq] at hcl
          refine ⟨ev, rfl, ?_⟩
          intro h
          have h1 := h (posLe 1 5) (by rw [hcl]; exact List.mem_singleton_self _)
          rcases h1 with h1 | ⟨e, he, hi⟩
          · revert h1; decide
          · have hmem : e.literal ∈ c.branch.trail.map (·.literal) :=
              List.mem_map.mpr ⟨e, he, rfl⟩
            rw [htr] at hmem
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
            rcases hmem with h2 | h2 <;> rw [h2] at hi <;> revert hi <;> decide

/-- The residual premise `EvidenceRun` is false even for the propagator-free kit. -/
theorem evidenceRun_refuted : ¬ EvidenceRun evBox evOriginal [] evLeaf := by
  intro h
  obtain ⟨cfg, hreach, ev, hev, hnot⟩ := evidence_refuted
  have := h hreach ev hev
  rw [SupportedReach.orig_eq hreach] at this
  exact hnot this

end LeanFzn.Solver.UIP.LcgRunInv
