/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantSnap.lean
U1c (1): `TrailSnapFixed orig trail` as a THEOREM along clamped supported runs.

Trail literals are pooled (`TrailInvWith.branch` at the box's own pool, from the
clamped emission vocabulary), and every pooled literal is a fixed point of
`snapLit`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesRun
import LeanFzn.Legacy.Solver.UIP.Proofs.ClampedRun
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

theorem snapBound_self {ints : List Int} {k : Int} (hk : k ∈ clampPool ints) :
    snapBound ints k = k := by
  have h1 : k ≤ snapBound ints k :=
    snapBound_ge_of_mem hk (Int.le_refl _)
  have h2 : snapBound ints k ≤ k := by
    rcases snapBound_le_or (ints := ints) k with h | h
    · exact h
    · rw [h]; exact clampMin_le hk
  omega

/-- Atoms of the base pool: structural inverse. -/
theorem atomPoolBase_inv : ∀ (ds : List Domain) (s0 : Nat) (a : Atom),
    a ∈ atomPoolBase s0 ds →
      (∃ s b, a = Atom.boolEq s b) ∨
      (∃ s k d, a = Atom.intLe s k ∧ ∃ i, i < ds.length ∧ s = s0 + i ∧ ds[i]? = some d
          ∧ k ∈ threshPool d) ∨
      (∃ s v d, a = Atom.intNe s v ∧ ∃ i, i < ds.length ∧ s = s0 + i ∧ ds[i]? = some d
          ∧ v ∈ vocabDomInts d) := by
  intro ds
  induction ds with
  | nil => intro s0 a h; simp [atomPoolBase] at h
  | cons d ds ih =>
      intro s0 a h
      simp only [atomPoolBase, List.mem_append] at h
      rcases h with h | h
      · simp only [slotAtomPool, List.mem_append, List.mem_cons, List.mem_nil_iff,
          or_false, List.mem_map] at h
        rcases h with (h | h) | h
        · rcases h with h | h
          · exact Or.inl ⟨s0, true, h⟩
          · exact Or.inl ⟨s0, false, h⟩
        · obtain ⟨k, hk, rfl⟩ := h
          exact Or.inr (Or.inl ⟨s0, k, d, rfl, 0, by simp, by simp, by simp, hk⟩)
        · obtain ⟨k, hk, rfl⟩ := h
          exact Or.inr (Or.inr ⟨s0, k, d, rfl, 0, by simp, by simp, by simp, hk⟩)
      · rcases ih (s0 + 1) a h with h | ⟨s, k, d', rfl, i, hi, hs, hd, hk⟩ |
            ⟨s, k, d', rfl, i, hi, hs, hd, hk⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨s, k, d', rfl, i + 1, by simp; omega, by rw [hs, Nat.add_assoc, Nat.add_comm 1 i], by simpa using hd, hk⟩)
        · exact Or.inr (Or.inr ⟨s, k, d', rfl, i + 1, by simp; omega, by rw [hs, Nat.add_assoc, Nat.add_comm 1 i], by simpa using hd, hk⟩)

theorem atomPool_inv {orig : List Domain} {a : Atom} (h : a ∈ atomPool orig) :
    (∃ s b, a = Atom.boolEq s b) ∨
      (∃ s k d, a = Atom.intLe s k ∧ orig[s]? = some d ∧ k ∈ threshPool d) ∨
      (∃ s v d, a = Atom.intNe s v ∧ orig[s]? = some d ∧ v ∈ vocabDomInts d) := by
  have key : ∀ a', a' ∈ atomPoolBase 0 orig →
      (∃ s b, a' = Atom.boolEq s b) ∨
      (∃ s k d, a' = Atom.intLe s k ∧ orig[s]? = some d ∧ k ∈ threshPool d) ∨
      (∃ s v d, a' = Atom.intNe s v ∧ orig[s]? = some d ∧ v ∈ vocabDomInts d) := by
    intro a' ha'
    rcases atomPoolBase_inv orig 0 a' ha' with h | ⟨s, k, d, rfl, i, hi, hs, hd, hk⟩ |
        ⟨s, k, d, rfl, i, hi, hs, hd, hk⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨s, k, d, rfl, by simpa [hs] using hd, hk⟩)
    · exact Or.inr (Or.inr ⟨s, k, d, rfl, by simpa [hs] using hd, hk⟩)
  rw [atomPool] at h
  rcases List.mem_append.mp h with h | h
  · exact key a h
  · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp h
    rcases key a' ha' with ⟨s, b, rfl⟩ | ⟨s, k, d, rfl, h2⟩ | ⟨s, k, d, rfl, h2⟩
    · exact Or.inl ⟨s, !b, rfl⟩
    · exact Or.inr (Or.inl ⟨s, k, d, rfl, h2⟩)
    · exact Or.inr (Or.inr ⟨s, k, d, rfl, h2⟩)

/-- Every pooled literal is a `snapLit` fixed point. -/
theorem snapLit_fixed_of_pool {orig : List Domain} {l : Literal}
    (h : l ∈ litPool orig) : snapLit orig l = l := by
  obtain ⟨atom, pos⟩ := l
  have hatom : atom ∈ atomPool orig ∨ atom.boolFlip ∈ atomPool orig := by
    rw [litPool] at h
    simp only [List.mem_append, List.mem_map, posLit, negLit, flipPosLit, flipNegLit] at h
    rcases h with ((⟨a, ha, he⟩ | ⟨a, ha, he⟩) | ⟨a, ha, he⟩) | ⟨a, ha, he⟩
    · left; have := congrArg Literal.atom he; simp at this; rw [← this]; exact ha
    · left; have := congrArg Literal.atom he; simp at this; rw [← this]; exact ha
    · right; have := congrArg Literal.atom he; simp at this; rw [← this, Atom.boolFlip_invol]; exact ha
    · right; have := congrArg Literal.atom he; simp at this; rw [← this, Atom.boolFlip_invol]; exact ha
  have hap : atom ∈ atomPool orig := by
    rcases hatom with h | h
    · exact h
    · simpa [Atom.boolFlip_invol] using atomPool_boolFlip_mem h
  rcases atomPool_inv hap with ⟨s, b, rfl⟩ | ⟨s, k, d, rfl, hd, hk⟩ | ⟨s, k, d, rfl, hd, hk⟩
  · rfl
  · by_cases hemp : (clampInts d).isEmpty = true
    · simp [snapLit, hd, hemp]
    · have hne : clampInts d ≠ [] := fun h' => hemp (by simp [h'])
      have : snapBound (clampInts d) k = k := snapBound_self hk
      simp [snapLit, hd, hemp, this]
  · by_cases hv : k ∈ clampInts d
    · simp [snapLit, hd, hv]
    · exact absurd (by simpa [vocabDomInts, clampInts] using hk) hv

theorem snapLit_fixed_of_norm_pool {orig : List Domain} {l : Literal}
    (h : l.norm ∈ litPool orig) : snapLit orig l = l := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => rfl
  | intLe s k => exact snapLit_fixed_of_pool (by simpa [Literal.norm] using h)
  | intNe s k => exact snapLit_fixed_of_pool (by simpa [Literal.norm] using h)

/-- **(1) `TrailSnapFixed` ALONG A CLAMPED SUPPORTED RUN.** 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem trailSnapFixed_of_clampedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {raw props : List Propagator}
    (hprops : props = clampProps orig raw)
    (htyped : EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      TrailSnapFixed orig cfg.branch.trail := by
  intro cfg hreach e he
  have hv : EmissionPoolAt (litPoolWith [] orig) props := by
    rw [litPoolWith_nil, hprops]; exact emissionPoolAt_clampProps htyped
  have h := (trailInvWith_of_supportedRun (extra := []) hv
    (by rw [litPoolWith_nil]; exact horig) hbr hshape hreach).branch e he
  rw [litPoolWith_nil] at h
  exact snapLit_fixed_of_norm_pool h

end LeanFzn.Solver.UIP.LcgRunInv
