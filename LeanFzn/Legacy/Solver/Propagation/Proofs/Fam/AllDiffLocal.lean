/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/AllDiffLocal.lean

Purpose:
  Watch-locality of the `allDiff` LCG propagator: `propAllDiffLCG st is`
  reads the state's domains only at the slots listed in `is` (and nothing
  else in the state).  This is the footprint theorem behind the
  `is`-watch registration of the family.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Fam.AllDiff: the propagator, its
    component scans (`allDiffElimFirst`, `hallClause`) and the slot
    enumeration bridge `getSlot_map_enum`.

Why:
  The theorem is stated over the raw `State` and its domain list, so the
  module deliberately does NOT import `ScheduledPropagation` /
  `ScheduledFamilies`: those modules register the propagator and will
  import this one, and importing them here would create a cycle.

DAG:
  LeanFzn.Solver.Propagation.Proofs.Fam.AllDiff
    -> LeanFzn.Solver.Propagation.Proofs.Fam.AllDiffLocal
    -> (registration modules: ScheduledFamilies / Proofs.Propagators)
-/

import LeanFzn.Legacy.Solver.Propagation.Proofs.Fam.AllDiff

open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation

/-! ## The domain-list view of the decision

`propAllDiff` runs on the slot-wise enumeration `doms.map Dom.enum`, and
every read of that list at a slot of `is` is the enumeration of the
corresponding compact domain (`getSlot_map_enum`).  The two lemmas below
transfer a pointwise equality on the slots of `is` through the filter and
the deduplicated union. -/

/-- `inRangeSlots` reads only the slots of `is`. -/
theorem inRangeSlots_congr {doms doms' : List (List Value)} {is : List Nat}
    (h : ∀ i ∈ is, getSlot doms i = getSlot doms' i) :
    inRangeSlots doms is = inRangeSlots doms' is := by
  unfold inRangeSlots
  apply List.filter_congr
  intro i hi
  rw [h i hi]

/-- The deduplicated union reads only the slots of `is`. -/
theorem distinctUnionVals_congr {doms doms' : List (List Value)} {is : List Nat}
    (h : ∀ i ∈ is, getSlot doms i = getSlot doms' i) :
    distinctUnionVals doms is = distinctUnionVals doms' is := by
  unfold distinctUnionVals
  have hflat : is.flatMap (getSlot doms) = is.flatMap (getSlot doms') := by
    induction is with
    | nil => rfl
    | cons i is ih =>
        have hi : getSlot doms i = getSlot doms' i := h i (by simp)
        have his : ∀ k ∈ is, getSlot doms k = getSlot doms' k :=
          fun k hk => h k (by simp [hk])
        simp only [List.flatMap_cons, hi, ih his]
  rw [hflat]

/-- **The pigeonhole test reads only the slots of `is`.**  (The result's
`narrowed` arm carries the whole domain list, so `propAllDiff` itself is
not equal across frames; only the branch it selects is watch-local, and
that is all `propAllDiffLCG` matches on.) -/
theorem propAllDiff_test_congr {doms doms' : List (List Value)} {is : List Nat}
    (h : ∀ i ∈ is, getSlot doms i = getSlot doms' i) :
    ((inRangeSlots doms is).length > (distinctUnionVals doms is).length ↔
      (inRangeSlots doms' is).length > (distinctUnionVals doms' is).length) := by
  rw [inRangeSlots_congr h, distinctUnionVals_congr h]

/-! ## The Hall clause

`hallClause doms is` filters the enumerated domains by nonemptiness and
then concatenates one `slotHall` report per surviving slot, each read from
`doms.getD s Dom.empty`.  All surviving slots lie in `is`, so the same
pointwise hypothesis on `is` gives the same clause. -/

/-- The per-slot concatenation reads only the domains at the listed slots. -/
theorem hallClauses_congr {doms doms' : List Domain} :
    ∀ {ss : List Nat}, (∀ s ∈ ss, doms.getD s Dom.empty = doms'.getD s Dom.empty) →
      hallClauses doms ss = hallClauses doms' ss
  | [], _ => rfl
  | s :: ss, h => by
      simp only [hallClauses]
      rw [h s (by simp),
        hallClauses_congr (fun t ht => h t (by simp [ht]))]

/-- **The Hall conflict clause reads only the slots of `is`.** -/
theorem hallClause_congr {doms doms' : List Domain} {is : List Nat}
    (h : ∀ i ∈ is, doms.getD i Dom.empty = doms'.getD i Dom.empty) :
    hallClause doms is = hallClause doms' is := by
  have hfil : inRangeSlots (doms.map Dom.enum) is =
      inRangeSlots (doms'.map Dom.enum) is := by
    apply inRangeSlots_congr
    intro i hi
    rw [getSlot_map_enum, getSlot_map_enum, h i hi]
  unfold hallClause
  rw [hfil]
  have hc : hallClauses doms (inRangeSlots (doms'.map Dom.enum) is) =
      hallClauses doms' (inRangeSlots (doms'.map Dom.enum) is) :=
    hallClauses_congr (fun s hs => h s (mem_inRangeSlots_left hs))
  rw [hc]

/-! ## The elimination scan

The gate `allDiffElimB` also tests `j < doms.length`, which is not a
domain read.  It is, however, implied by the value-membership conjunct:
an empty target domain makes that conjunct false on both sides, and a
nonempty one places `j` in range on both sides.  This is what makes the
whole gate watch-local. -/

/-- A nonempty enumerated domain read is in range (the out-of-range read
is `Dom.empty`, whose enumeration is empty). -/
theorem allDiff_enum_getD_ne_nil_lt_length {doms : List Domain} {j : Nat}
    (h : Dom.enum (doms.getD j Dom.empty) ≠ []) : j < doms.length := by
  have hget : getSlot (doms.map Dom.enum) j ≠ [] := by
    rwa [getSlot_map_enum]
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hget
  have := lt_length_of_mem_getSlot (doms.map Dom.enum) j v hv
  simpa using this

/-- A false value-membership conjunct makes the whole gate false (it is the
last conjunct), independently of the range test. -/
theorem allDiffElimB_eq_false_of_valueMemB_false {doms : List Domain} {i j : Nat}
    {c : Int}
    (h : valueMemB (.int c) (Dom.enum (doms.getD j Dom.empty)) = false) :
    allDiffElimB doms i j c = false := by
  unfold allDiffElimB
  rw [h]
  simp

/-- The value-membership test is false on an empty enumeration. -/
theorem valueMemB_enum_getD_eq_false_of_enum_eq_nil {doms : List Domain} {j : Nat}
    {c : Int} (h : Dom.enum (doms.getD j Dom.empty) = []) :
    valueMemB (.int c) (Dom.enum (doms.getD j Dom.empty)) = false := by
  rw [h]
  rfl

/-- **The elimination gate reads only the target slot's domain.** -/
theorem allDiffElimB_congr {doms doms' : List Domain} {i j : Nat} {c : Int}
    (h : doms.getD j Dom.empty = doms'.getD j Dom.empty) :
    allDiffElimB doms i j c = allDiffElimB doms' i j c := by
  by_cases hnil : Dom.enum (doms.getD j Dom.empty) = []
  · have hnil' : Dom.enum (doms'.getD j Dom.empty) = [] := by
      rw [← h]; exact hnil
    rw [allDiffElimB_eq_false_of_valueMemB_false
          (valueMemB_enum_getD_eq_false_of_enum_eq_nil hnil),
      allDiffElimB_eq_false_of_valueMemB_false
          (valueMemB_enum_getD_eq_false_of_enum_eq_nil hnil')]
  · have hne' : Dom.enum (doms'.getD j Dom.empty) ≠ [] := by
      rw [← h]; exact hnil
    have hlt : j < doms.length := allDiff_enum_getD_ne_nil_lt_length hnil
    have hlt' : j < doms'.length := allDiff_enum_getD_ne_nil_lt_length hne'
    unfold allDiffElimB
    rw [h]
    simp [hlt, hlt']

/-- The target scan reads only the domains at the listed slots. -/
theorem allDiffElimTarget_congr {doms doms' : List Domain} {i : Nat} {c : Int} :
    ∀ {is : List Nat},
      (∀ j ∈ is, doms.getD j Dom.empty = doms'.getD j Dom.empty) →
      allDiffElimTarget doms is i c = allDiffElimTarget doms' is i c
  | [], _ => rfl
  | j :: js, h => by
      have hb := allDiffElimB_congr (doms := doms) (doms' := doms') (i := i)
        (j := j) (c := c) (h j (by simp))
      simp only [allDiffElimTarget, hb]
      cases hbv : allDiffElimB doms i j c with
      | true =>
          have hbv' : allDiffElimB doms' i j c = true := by
            rw [← hb]; exact hbv
          simp only [hbv', if_true]
      | false =>
          have hbv' : allDiffElimB doms' i j c = false := by
            rw [← hb]; exact hbv
          simp only [hbv']
          exact allDiffElimTarget_congr (fun k hk => h k (by simp [hk]))

/-- **The first-elimination scan reads only the slots of `is`.** -/
theorem allDiffElimFirst_congr {doms doms' : List Domain} {is : List Nat}
    (h : ∀ i ∈ is, doms.getD i Dom.empty = doms'.getD i Dom.empty) :
    allDiffElimFirst doms is = allDiffElimFirst doms' is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hi : doms.getD i Dom.empty = doms'.getD i Dom.empty := h i (by simp)
      have his : ∀ k ∈ is, doms.getD k Dom.empty = doms'.getD k Dom.empty :=
        fun k hk => h k (by simp [hk])
      simp only [allDiffElimFirst]
      rw [hi]
      cases hen : Dom.enum (doms'.getD i Dom.empty) with
      | nil => exact ih his
      | cons v vs =>
          cases v with
          | int k =>
              cases vs with
              | nil =>
                  dsimp only
                  rw [allDiffElimTarget_congr (is := i :: is) (i := i) (c := k)
                    (fun t ht => h t ht), ih his]
              | cons w ws => exact ih his
          | bool b => exact ih his
          | setOfInt s => exact ih his
          | array l => exact ih his

/-! ## The propagator

`propAllDiffLCG` is the match of the pigeonhole decision, whose
contradiction arm embeds `hallClause`, and of the elimination scan on the
narrowed arm.  The three components are watch-local, hence so is the
propagator. -/

/-- **WATCH-LOCALITY OF `allDiff`**: the LCG propagator over the slots
`is` depends only on the domains of those slots — equality of the
`getD` reads at every slot of `is` gives the same propagation result. -/
theorem propAllDiffLCG_domains_local (is : List Nat) {st st' : State}
    (h : ∀ i ∈ is, st.domains.getD i Dom.empty = st'.domains.getD i Dom.empty) :
    propAllDiffLCG st is = propAllDiffLCG st' is := by
  have hslot : ∀ i ∈ is, getSlot (st.domains.map Dom.enum) i =
      getSlot (st'.domains.map Dom.enum) i := by
    intro i hi
    rw [getSlot_map_enum, getSlot_map_enum, h i hi]
  have hA : inRangeSlots (st.domains.map Dom.enum) is =
      inRangeSlots (st'.domains.map Dom.enum) is := inRangeSlots_congr hslot
  have hB : distinctUnionVals (st.domains.map Dom.enum) is =
      distinctUnionVals (st'.domains.map Dom.enum) is :=
    distinctUnionVals_congr hslot
  have hhc : hallClause st.domains is = hallClause st'.domains is :=
    hallClause_congr h
  have hf : allDiffElimFirst st.domains is = allDiffElimFirst st'.domains is :=
    allDiffElimFirst_congr h
  unfold propAllDiffLCG propAllDiff
  rw [hA, hB, hhc, hf]
  by_cases hc : (inRangeSlots (st'.domains.map Dom.enum) is).length >
      (distinctUnionVals (st'.domains.map Dom.enum) is).length
  · simp [hc]
  · simp [hc]

end LeanFzn.Solver.Propagation
