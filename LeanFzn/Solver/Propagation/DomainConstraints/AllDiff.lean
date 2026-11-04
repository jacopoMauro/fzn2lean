import LeanFzn.Solver.Propagation.DomainConstraints.Repr
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The all-different propagator (pigeonhole counting) -/

/-- The slots of `is` whose current domain is nonempty: an out-of-range
    position and an in-range empty slot both read no value in any
    assignment, so only the nonempty ones demand distinct values of the
    union.  (Dropping empty slots only weakens the pigeonhole count, so
    the preservation theorem is unaffected.)  This makes the result
    depend only on `getSlot doms i` for `i ∈ is`, i.e. watch-local in
    the slots of `is`. -/
def inRangeSlots (doms : List (List Value)) (is : List Nat) : List Nat :=
  is.filter (fun i => !(getSlot doms i).isEmpty)

/-- The slots of `inRangeSlots` are slots of `is`. -/
theorem mem_inRangeSlots_left {doms : List (List Value)} {is : List Nat} {i : Nat}
    (h : i ∈ inRangeSlots doms is) : i ∈ is :=
  (List.mem_filter.mp h).1

/-- A slot of `inRangeSlots` has a nonempty current domain. -/
theorem getSlot_ne_nil_of_mem_inRangeSlots {doms : List (List Value)} {is : List Nat}
    {i : Nat} (h : i ∈ inRangeSlots doms is) : getSlot doms i ≠ [] := by
  have hb := (List.mem_filter.mp h).2
  intro hnil
  rw [hnil] at hb
  simp at hb

/-- A nonempty slot read lies in range: the out-of-range read is `[]`. -/
theorem getSlot_ne_nil_lt_length {doms : List (List Value)} {i : Nat}
    (h : getSlot doms i ≠ []) : i < doms.length := by
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
  exact lt_length_of_mem_getSlot doms i v hv

/-- Every slot of `inRangeSlots` is in range of the domain list. -/
theorem lt_length_of_mem_inRangeSlots {doms : List (List Value)} {is : List Nat}
    {i : Nat} (h : i ∈ inRangeSlots doms is) : i < doms.length :=
  getSlot_ne_nil_lt_length (getSlot_ne_nil_of_mem_inRangeSlots h)

/-- The number of distinct values in the union of the domains of the
    slots `is` (the deduplicated concatenation, first occurrence
    kept). -/
def distinctUnionVals (doms : List (List Value)) (is : List Nat) : List Value :=
  dedupVals (is.flatMap (getSlot doms))

/-- **The all-different propagator** (`all_different` style over a
    sub-list of slots): pigeonhole counting — if the number of slots of
    `is` with a nonempty current domain is greater than the number of
    distinct values in the union of their domains, `contradiction` (any
    satisfying assignment reads pairwise-distinct values at those slots,
    each in its slot's domain, so the union must hold at least as many
    distinct values as there are such slots); otherwise nothing is
    narrowed (bounds and Hall-interval reasoning are future work). -/
def propAllDiff (is : List Nat) (doms : List (List Value)) : PropResult :=
  if (inRangeSlots doms is).length > (distinctUnionVals doms is).length then
    .contradiction
  else
    .narrowed doms

/-- **The pigeonhole bound, membership form**: if an assignment satisfies
    the pairwise-distinctness and reads, at every slot of `inRangeSlots`, a
    value of the deduplicated union, then those slots are at most as many as
    the union's distinct values. (The `allAssigns` form below derives the
    membership from the domains; this form is what the Hall-clause
    entailment needs, where the membership is DERIVED from the clause's
    falsity instead.) -/
theorem allDiff_pigeonhole_of_mem {doms : List (List Value)} {is : List Nat}
    {a : List Value}
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.allDiff is) a)
    (hmem : ∀ i ∈ inRangeSlots doms is, a[i]! ∈ distinctUnionVals doms is) :
    (inRangeSlots doms is).length ≤ (distinctUnionVals doms is).length := by
  have hmem' : ∀ (x : Value), x ∈ (inRangeSlots doms is).map (fun i => a[i]!) →
      x ∈ distinctUnionVals doms is := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_map.mp hx
    rw [← hxi]
    exact hmem i hi
  have hnd : ((inRangeSlots doms is).map (fun i => a[i]!)).Nodup := by
    have hfilt : inRangeSlots doms is <+ is := List.filter_sublist
    have hsub : (inRangeSlots doms is).map (fun i => a[i]!) <+
        is.map (fun i => a[i]!) := List.Sublist.map _ hfilt
    exact List.Nodup.sublist hsub hsat
  have hwnd : (distinctUnionVals doms is).Nodup := nodup_dedupVals _
  have hle := nodup_subset_length_le _ _ hnd hmem' hwnd
  rw [List.length_map] at hle
  exact hle

/-- **The pigeonhole bound**: if a complete assignment of `doms`
    makes the values read at the slots of `is` pairwise distinct, then
    the number of slots of `is` with a nonempty current domain is at most
    the number of distinct values in the union of their domains.  The
    proof maps each such slot to the value the assignment reads there — a
    duplicate-free list (pairwise distinctness) whose values all lie
    in the duplicate-free union — and applies the list pigeonhole
    `nodup_subset_length_le`. -/
private theorem allDiff_pigeonhole {doms : List (List Value)} {is : List Nat}
    {a : List Value} (ha : a ∈ allAssigns doms)
    (hsat : DomConstraint.SatisfiedBy (DomConstraint.allDiff is) a) :
    (inRangeSlots doms is).length ≤ (distinctUnionVals doms is).length := by
  obtain ⟨hlen, hget⟩ := allAssigns_spec doms a ha
  -- each nonempty slot's read value is in its slot's domain, hence in
  -- the deduplicated union
  have hmem : ∀ (x : Value), x ∈ (inRangeSlots doms is).map (fun i => a[i]!) →
      x ∈ distinctUnionVals doms is := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_map.mp hx
    obtain ⟨hin, hilt⟩ := List.mem_filter.mp hi
    have hilt' : i < doms.length := getSlot_ne_nil_lt_length (by
      intro hnil
      rw [hnil] at hilt
      simp at hilt)
    -- a[i]! is the read value, in slot i's domain by the assignment spec
    have hread : a[i]? = some (a[i]!) := by
      have hlt : i < a.length := by rw [hlen]; exact hilt'
      rw [List.getElem?_eq_getElem hlt, getElem!_pos a i hlt]
    have hdom : a[i]! ∈ getSlot doms i := hget i _ hread
    rw [← hxi]
    exact mem_dedupVals _ _ |>.mpr
      (List.mem_flatMap.mpr ⟨i, hin, hdom⟩)
  -- the read values are pairwise distinct (the slots are, per the
  -- filter, a sub-list of is, and the reads along is are distinct)
  have hnd : ((inRangeSlots doms is).map (fun i => a[i]!)).Nodup := by
    have hfilt : inRangeSlots doms is <+ is := List.filter_sublist
    have hsub : (inRangeSlots doms is).map (fun i => a[i]!) <+
        is.map (fun i => a[i]!) := List.Sublist.map _ hfilt
    exact List.Nodup.sublist hsub hsat
  -- the union's deduplication is duplicate-free
  have hwnd : (distinctUnionVals doms is).Nodup := nodup_dedupVals _
  -- the pigeonhole
  have hle := nodup_subset_length_le _ _ hnd hmem hwnd
  rw [List.length_map] at hle
  exact hle

/-- **Preservation for `propAllDiff`** (PLAN 6.3's local preservation
    theorem, all-different case): on `narrowed doms'` (the domains
    unchanged — the propagator only detects contradictions today),
    every assignment satisfying the pairwise-distinctness is trivially
    kept; on `contradiction`, the pigeonhole bound certifies that no
    assignment of the input domains makes the slots pairwise
    distinct. -/
theorem propAllDiff_preserves (is : List Nat) :
    Preserves (DomConstraint.allDiff is) (propAllDiff is) := by
  constructor
  · intro doms doms' h a ha _hsat
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : doms' = doms := (PropResult.narrowed.inj h).symm
      subst hd
      exact ha
  · intro doms doms' h
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      exact absurd h (by simp)
    · rw [if_neg hc] at h
      have hd : doms' = doms := (PropResult.narrowed.inj h).symm
      rw [hd]
      exact DomPointwiseSub.refl doms
  · intro doms h a ha hsat
    simp only [propAllDiff] at h
    by_cases hc : (inRangeSlots doms is).length > (distinctUnionVals doms is).length
    · rw [if_pos hc] at h
      have hle := allDiff_pigeonhole ha hsat
      omega
    · rw [if_neg hc] at h
      exact absurd h (by simp)


end LeanFzn.Solver.Propagation.DomainFiltering
