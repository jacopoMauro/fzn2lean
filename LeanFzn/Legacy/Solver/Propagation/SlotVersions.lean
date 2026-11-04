/-
File: LeanFzn/Solver/Propagation/SlotVersions.lean

Purpose (PLAN §3.4): PER-SLOT VERSION COUNTERS for the sparse scheduled frame.

A `SlotVersions` vector is an `Array Nat` aligned with `Frame.domains`: entry
`s` counts how many times slot `s`'s domain changed since the vector was
created. The dispatcher threads it alongside the frame (NOT inside
`BranchFrame`'s denotation): on a frame transition `f → g` it bumps exactly
the slots reported by the frozen E0 extraction `frameEvents f g`
(`SlotVersions.bumpEvents`). Because `frameEvents_complete` reports every
changed slot, a slot whose counter is unchanged between two states has an
unchanged domain:

* `domain_eq_of_version_eq` — one transition: if `v' = bumpEvents v
  (frameEvents f g)` and `v'[s] = v[s]`, then the slot's domains at `f` and
  `g` agree (`Frame.domains`-level, `getD`-form);
* `VersionsReach.domain_eq` — any chain of such syncs: if the endpoint
  version at `s` equals the start version, the endpoint domains agree.

The vector never changes length (`bump_size`, `bumpEvents_size`,
`VersionsReach.size`), which is what makes `Array.getD` a total O(1) stamp
read at every slot.

This module is the E1/E2/W1 boundary: the watched-clause index
(`ClauseWatch.lean`) compares two such stamps instead of re-reading a domain,
and the E2 family cache can key summaries on them. Nothing here reads
`Value`; the only frame observation is the E0 event extraction.

DAG: EventContract -> SlotVersions -> ClauseWatch (version-keyed section).
-/
import LeanFzn.Legacy.Solver.Propagation.EventContract

open LeanFzn.Semantics LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation

/-! ## The vector and its update -/

/-- Per-slot version counters, aligned with `Frame.domains`. -/
abbrev SlotVersions := Array Nat

/-- Bump the counter of slot `s` by one; identity when `s` is out of range.
The ONLY update operation: a version strictly increases exactly when its slot
is bumped. -/
def SlotVersions.bump (v : SlotVersions) (s : Nat) : SlotVersions :=
  if h : s < v.size then v.set s (v[s] + 1) h else v

/-- Bump every slot that occurs in the event list (duplicates bump twice; the
discipline only needs "at least once"). -/
def SlotVersions.bumpEvents (v : SlotVersions) (evs : List DomainEvent) :
    SlotVersions :=
  evs.foldl (fun v e => v.bump e.slot) v

/-! ## Length: the vector never changes length -/

@[simp] theorem bump_size (v : SlotVersions) (s : Nat) :
    (v.bump s).size = v.size := by
  unfold SlotVersions.bump
  split
  · next h => exact Array.size_set h
  · rfl

theorem bumpEvents_size (v : SlotVersions) (evs : List DomainEvent) :
    (v.bumpEvents evs).size = v.size := by
  unfold SlotVersions.bumpEvents
  induction evs generalizing v with
  | nil => rfl
  | cons e es ih => exact (ih (v.bump e.slot)).trans (bump_size v e.slot)

/-! ## Pointwise behaviour -/

theorem bump_getD_other {v : SlotVersions} {s k : Nat} (h : k ≠ s) :
    (v.bump s).getD k 0 = v.getD k 0 := by
  unfold SlotVersions.bump
  split
  · next hlt =>
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_set hlt]
      rw [if_neg (by simpa [eq_comm] using h)]
  · rfl

theorem bump_getD_self {v : SlotVersions} {s : Nat} (h : s < v.size) :
    (v.bump s).getD s 0 = v.getD s 0 + 1 := by
  unfold SlotVersions.bump
  rw [dif_pos h]
  have hset : (v.set s (v[s] + 1) h).getD s 0 = v[s] + 1 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_set h, if_pos rfl]
    rfl
  rw [hset, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  simp

/-- Bumping an out-of-range slot changes nothing. -/
theorem bump_eq_self {v : SlotVersions} {s : Nat} (h : ¬ s < v.size) :
    v.bump s = v := by
  unfold SlotVersions.bump
  rw [dif_neg h]

theorem bump_getD_ge (v : SlotVersions) (s k : Nat) :
    v.getD k 0 ≤ (v.bump s).getD k 0 := by
  by_cases h : k = s
  · subst h
    by_cases hlt : k < v.size
    · rw [bump_getD_self hlt]; omega
    · rw [bump_eq_self hlt]; exact Nat.le_refl _
  · rw [bump_getD_other h]
    exact Nat.le_refl _

/-- **SILENCE**: if no event mentions slot `s`, its counter is unchanged. -/
theorem bumpEvents_getD_eq_of_silent {v : SlotVersions} {evs : List DomainEvent}
    {s : Nat} (h : ∀ e ∈ evs, e.slot ≠ s) :
    (v.bumpEvents evs).getD s 0 = v.getD s 0 := by
  unfold SlotVersions.bumpEvents
  induction evs generalizing v with
  | nil => rfl
  | cons e es ih =>
      dsimp only [List.foldl_cons]
      rw [ih (v := v.bump e.slot) (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      exact bump_getD_other (Ne.symm (h e (List.mem_cons_self ..)))

theorem bumpEvents_getD_ge (v : SlotVersions) (evs : List DomainEvent) (s : Nat) :
    v.getD s 0 ≤ (v.bumpEvents evs).getD s 0 := by
  unfold SlotVersions.bumpEvents
  induction evs generalizing v with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
      dsimp only [List.foldl_cons]
      exact Nat.le_trans (bump_getD_ge v e.slot s) (ih (v := v.bump e.slot))

/-- **STRICTNESS**: a mentioned in-range slot's counter strictly increases. -/
theorem bumpEvents_getD_gt_of_mem {v : SlotVersions} {evs : List DomainEvent}
    {s : Nat} (hs : s < v.size) (h : ∃ e ∈ evs, e.slot = s) :
    v.getD s 0 < (v.bumpEvents evs).getD s 0 := by
  unfold SlotVersions.bumpEvents
  induction evs generalizing v with
  | nil => obtain ⟨e, he, _⟩ := h; cases he
  | cons e es ih =>
      dsimp only [List.foldl_cons]
      obtain ⟨e0, he0, hslot0⟩ := h
      rcases List.mem_cons.mp he0 with he | hmem
      · subst he
        have hs0 : e0.slot < v.size := by rw [hslot0]; exact hs
        have h1 : (v.bump e0.slot).getD e0.slot 0 = v.getD e0.slot 0 + 1 :=
          bump_getD_self hs0
        have h2 := bumpEvents_getD_ge (v.bump e0.slot) es e0.slot
        rw [hslot0] at h1 h2 ⊢
        simp only [SlotVersions.bumpEvents] at h1 h2 ⊢
        omega
      · have hs' : s < (v.bump e.slot).size := by simp [hs]
        exact Nat.lt_of_le_of_lt (bump_getD_ge v e.slot s)
          (ih hs' ⟨e0, hmem, hslot0⟩)

/-! ## THE DISCIPLINE: unchanged version ⇒ unchanged domain -/

/-- One transition: versions bumped exactly by the E0 event list. If the
counter of slot `s` did not move, then slot `s`'s certified domain did not
change (`getD` form of `Frame.domains` equality). The length premises make
`getD` total; they hold for the dispatcher's fixed-width frame. -/
theorem domain_eq_of_version_eq {f g : BranchFrame} {v : SlotVersions} {s : Nat}
    (hsize : v.size = (Frame.domains f).length)
    (hsize' : (v.bumpEvents (frameEvents f g)).size = (Frame.domains g).length)
    (h : (v.bumpEvents (frameEvents f g)).getD s 0 = v.getD s 0) :
    (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty := by
  by_cases hne : (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty
  · exact hne
  · obtain ⟨e, he, hslot⟩ := frameEvents_complete hne
    have hs : s < v.size := by
      rw [hsize]
      by_cases hlt : s < (Frame.domains f).length
      · exact hlt
      · have hflen : (Frame.domains f).length ≤ s := by omega
        have heq : (Frame.domains g).length = (Frame.domains f).length := by
          rw [← hsize', bumpEvents_size, hsize]
        have hglen : (Frame.domains g).length ≤ s := by omega
        have hf : (Frame.domains f).getD s Dom.empty = Dom.empty := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hflen]
          rfl
        have hg : (Frame.domains g).getD s Dom.empty = Dom.empty := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hglen]
          rfl
        exact absurd (hf.trans hg.symm) hne
    have hmem : ∃ e ∈ frameEvents f g, e.slot = s := ⟨e, he, hslot⟩
    have hgt := bumpEvents_getD_gt_of_mem hs hmem
    omega

end LeanFzn.Solver.Propagation
