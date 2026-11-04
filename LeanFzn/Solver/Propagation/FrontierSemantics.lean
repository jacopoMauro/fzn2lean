/-
Purpose: assignment coverage of pending frames and branch splitting, for both
representations: the sparse scheduled `BranchFrame` (S0 §3.1) and the
positional `PrefixFrame` the chronological/reference cone keeps.

Dependencies: Frontier supplies frames; LeanFzn.Solver.Core.Enumerate
specifies finite assignments.

DAG: Frontier + Search -> FrontierSemantics -> pruned and reference search proofs.
-/
import LeanFzn.Solver.Propagation.Frontier
import LeanFzn.Solver.Core.Enumerate
open LeanFzn.Semantics LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-! ## Sparse coverage (the scheduled cone, S0 §3.1) -/

/-- Coverage of a sparse frame: the assignments enumerated by its full
per-slot box. This is S0's frozen membership form (the prefix form is gone). -/
def FrameCovers (f : BranchFrame) (a : Assignment) : Prop :=
  a ∈ allAssigns f.doms

/-- Coverage of a pending sparse stack: some frame covers the assignment. -/
def FrontierCovers (pending : List BranchFrame) (a : Assignment) : Prop :=
  ∃ f ∈ pending, FrameCovers f a

/-- Membership decomposition of `allAssigns` at the head. -/
theorem mem_allAssigns_cons_iff {d : Domain} {rest : List Domain}
    {a : Assignment} :
    a ∈ allAssigns (d :: rest) ↔
      ∃ v ∈ d, ∃ a' ∈ allAssigns rest, a = v :: a' := by
  cases hd : DomainElems.elems d with
  | nil =>
      simp only [allAssigns, hd]
      constructor
      · intro h; cases h
      · rintro ⟨v, hv, a', ha', heq⟩
        rw [DomainLike.mem_iff, hd] at hv
        exact absurd hv (by simp)
  | cons v vs =>
      rw [mem_allAssigns_cons hd]
      constructor
      · rintro ⟨w, hw, a', ha', rfl⟩
        refine ⟨w, ?_, a', ha', rfl⟩
        rw [DomainLike.mem_iff, hd]
        exact hw
      · rintro ⟨w, hw, a', ha', rfl⟩
        refine ⟨w, ?_, a', ha', rfl⟩
        have hw' : w ∈ v :: vs := by
          have := (DomainLike.mem_iff d w).mp hw
          rwa [hd] at this
        exact hw'

/-- A covered assignment reads the recorded singleton of a decided slot. -/
theorem allAssigns_read {ds : List Domain} {a : Assignment} {k : Nat}
    {v : Value} (ha : a ∈ allAssigns ds) (hk : ds[k]? = some (Dom.ofList [v])) :
    a[k]? = some v := by
  induction ds generalizing a k with
  | nil => simp at hk
  | cons d rest ih =>
      obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
      cases k with
      | zero =>
          rw [List.getElem?_cons_zero] at hk
          have hd : d = Dom.ofList [v] := Option.some.inj hk
          rw [hd] at hw
          have hw' : w ∈ [v] := by
            rwa [DomainLike.mem_iff, domElems_eq_enum, Dom.enum_ofList] at hw
          rw [List.getElem?_cons_zero]
          rcases List.mem_singleton.mp hw' with rfl
          rfl
      | succ j =>
          rw [List.getElem?_cons_succ] at hk ⊢
          exact ih ha' hk

/-- A covered assignment reads the frame's singleton at a decided slot. -/
theorem covers_read {f : BranchFrame} {a : Assignment} {k : Nat} {v : Value}
    (ha : FrameCovers f a) (hk : f.doms[k]? = some (Dom.ofList [v])) :
    a[k]? = some v :=
  allAssigns_read ha hk

private theorem allAssigns_set_split_aux :
    ∀ (ds : List Domain) (k : Nat) (v : Value) (vs : Domain),
      ds[k]?.map Dom.enum = some (v :: vs.enum) →
      ∀ a : Assignment,
        a ∈ allAssigns ds ↔
          a ∈ allAssigns (ds.set k (Dom.ofList [v])) ∨
            a ∈ allAssigns (ds.set k vs) := by
  intro ds
  induction ds with
  | nil => intro k v vs h a; simp at h
  | cons d rest ih =>
      intro k
      cases k with
      | zero =>
          intro v vs h a
          have hd : d.enum = v :: vs.enum := by simpa using h
          rw [List.set_cons_zero, List.set_cons_zero]
          constructor
          · intro ha
            obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
            have hw' : w ∈ v :: vs.enum := by
              have := (DomainLike.mem_iff d w).mp hw
              rwa [domElems_eq_enum, hd] at this
            rcases List.mem_cons.mp hw' with rfl | hw''
            · left
              rw [mem_allAssigns_cons_iff]
              refine ⟨w, ?_, a', ha', rfl⟩
              rw [DomainLike.mem_iff, domElems_eq_enum, Dom.enum_ofList]
              exact List.mem_singleton_self w
            · right
              rw [mem_allAssigns_cons_iff]
              exact ⟨w, (DomainLike.mem_iff vs w).mpr hw'', a', ha', rfl⟩
          · intro h
            rcases h with h1 | h2
            · obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp h1
              have hw' : w ∈ [v] := by
                rwa [DomainLike.mem_iff, domElems_eq_enum, Dom.enum_ofList] at hw
              have hwv : w = v := List.mem_singleton.mp hw'
              subst hwv
              rw [mem_allAssigns_cons_iff]
              refine ⟨w, ?_, a', ha', rfl⟩
              rw [DomainLike.mem_iff, domElems_eq_enum]
              exact hd ▸ List.mem_cons_self ..
            · obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp h2
              rw [mem_allAssigns_cons_iff]
              refine ⟨w, ?_, a', ha', rfl⟩
              rw [DomainLike.mem_iff, domElems_eq_enum]
              exact hd ▸ List.mem_cons_of_mem _ ((DomainLike.mem_iff vs w).mp hw)
      | succ k =>
          intro v vs h a
          simp only [List.getElem?_cons_succ] at h
          rw [List.set_cons_succ, List.set_cons_succ]
          simp only [mem_allAssigns_cons_iff]
          constructor
          · rintro ⟨w, hw, a', ha', heq⟩
            rw [heq]
            rcases (ih k v vs h a').mp ha' with h1 | h1
            · exact Or.inl ⟨w, hw, a', h1, rfl⟩
            · exact Or.inr ⟨w, hw, a', h1, rfl⟩
          · rintro (h1 | h2)
            · obtain ⟨w, hw, a', ha', heq⟩ := h1
              exact ⟨w, hw, a', (ih k v vs h a').mpr (Or.inl ha'), heq⟩
            · obtain ⟨w, hw, a', ha', heq⟩ := h2
              exact ⟨w, hw, a', (ih k v vs h a').mpr (Or.inr ha'), heq⟩

/-- THE ARBITRARY-SLOT SPLIT (enumeration view): the selected slot's
denotation is `v :: vs.enum`; the parent's assignments split into the pinned
child (`Dom.ofList [v]` at `k`) and the retired sibling (`vs` at `k`). -/
theorem allAssigns_set_split {ds : List Domain} {k : Nat} {v : Value}
    {vs : Domain} (h : ds[k]?.map Dom.enum = some (v :: vs.enum))
    (a : Assignment) :
    a ∈ allAssigns ds ↔
      a ∈ allAssigns (ds.set k (Dom.ofList [v])) ∨
        a ∈ allAssigns (ds.set k vs) :=
  allAssigns_set_split_aux ds k v vs h a

/-- The `Dom.cons`-shaped form of the arbitrary-slot split. -/
theorem allAssigns_set_split_cons {ds : List Domain} {k : Nat} {v : Value}
    {vs : Domain} (h : ds[k]? = some (Dom.cons v vs)) (a : Assignment) :
    a ∈ allAssigns ds ↔
      a ∈ allAssigns (ds.set k (Dom.ofList [v])) ∨
        a ∈ allAssigns (ds.set k vs) :=
  allAssigns_set_split (ds := ds) (k := k) (v := v) (vs := vs)
    (by rw [h]; simp) a

/-- THE ARBITRARY-SLOT SPLIT (S0 §3.5 `covers_split_at`): the parent's
coverage is exactly the union of the pinned child's coverage and the retired
sibling's coverage, at an ARBITRARY slot. -/
theorem covers_split_at {f : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (a : Assignment) :
    FrameCovers f a ↔ FrameCovers (f.pin k v) a ∨ FrameCovers (f.retire k vs) a := by
  rw [FrameCovers, FrameCovers, FrameCovers, BranchFrame.pin_doms,
    BranchFrame.retire_doms]
  exact allAssigns_set_split h a

/-- The `Dom.cons`-shaped form of the arbitrary-slot coverage split. -/
theorem covers_split_at_cons {f : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]? = some (Dom.cons v vs)) (a : Assignment) :
    FrameCovers f a ↔ FrameCovers (f.pin k v) a ∨ FrameCovers (f.retire k vs) a := by
  rw [FrameCovers, FrameCovers, FrameCovers, BranchFrame.pin_doms,
    BranchFrame.retire_doms]
  exact allAssigns_set_split_cons h a

/-- Search-completeness shape: a leaf solution of the parent survives in one
of the two sparse children. -/
theorem exists_solution_child {f : BranchFrame} {k : Nat} {v : Value}
    {vs : Domain} (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    {leaf : Assignment → Bool}
    (hfind : ∃ a, FrameCovers f a ∧ leaf a = true) :
    (∃ a, FrameCovers (f.pin k v) a ∧ leaf a = true) ∨
      (∃ a, FrameCovers (f.retire k vs) a ∧ leaf a = true) := by
  obtain ⟨a, hc, hl⟩ := hfind
  rcases (covers_split_at h a).mp hc with h' | h'
  · exact Or.inl ⟨a, h', hl⟩
  · exact Or.inr ⟨a, h', hl⟩

/-! ## Positional coverage (the chronological/reference cone) -/

/-- Coverage of a positional frame: the chosen prefix extended by any
remaining assignment. -/
def PrefixCovers (f : PrefixFrame) (a : Assignment) : Prop :=
  ∃ tail ∈ allAssigns f.1, a = f.2 ++ tail

/-- Coverage of a pending positional stack: some frame covers the assignment. -/
def PrefixFrontierCovers (pending : List PrefixFrame) (a : Assignment) : Prop :=
  ∃ f ∈ pending, PrefixCovers f a

/-- The positional head split: the parent's coverage is the union of the
selected value's child and the sibling. This is the positional `covers_split`
the chronological cone keeps. -/
theorem prefix_covers_split {d : Domain} {v : Value} {vs : Domain}
    (hd : d.enum = v :: vs.enum) (rest : List Domain) (chosen a : Assignment) :
    PrefixCovers (d :: rest, chosen) a ↔
      PrefixCovers (rest, chosen ++ [v]) a ∨ PrefixCovers (vs :: rest, chosen) a := by
  have hd' : DomainElems.elems d = v :: vs.enum := by
    simpa [domElems_eq_enum] using hd
  constructor
  · rintro ⟨tail, htail, rfl⟩
    obtain ⟨w, hw, suffix, hs, rfl⟩ := (mem_allAssigns_cons hd' rest tail).mp htail
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl ⟨suffix, hs, by simp [List.append_assoc]⟩
    · apply Or.inr
      refine ⟨w :: suffix, ?_, rfl⟩
      cases hvs : vs.enum with
      | nil =>
          rw [hvs] at hw
          cases hw
      | cons u us =>
          have hvs' : DomainElems.elems vs = u :: us := by
            simpa [domElems_eq_enum] using hvs
          exact (mem_allAssigns_cons hvs' rest (w :: suffix)).mpr
            ⟨w, by rwa [hvs] at hw, suffix, hs, rfl⟩
  · rintro (⟨tail, ht, rfl⟩ | ⟨tail, ht, rfl⟩)
    · refine ⟨v :: tail, (mem_allAssigns_cons hd' rest (v :: tail)).mpr
        ⟨v, List.mem_cons_self, tail, ht, rfl⟩, ?_⟩
      simp [List.append_assoc]
    · refine ⟨tail, allAssigns_subset_cons_of_elems
        (d := vs) (d' := d) ?_ hd' rest tail ht, rfl⟩
      simp [domElems_eq_enum]

/-- The positional split in list-enumeration form: this is the shape the
runtime traversal's `match d.enum with` produces (the sibling is the
compact domain `Dom.ofList vs`). -/
theorem prefix_covers_split_list {d : Domain} {v : Value} {vs : List Value}
    (hd : d.enum = v :: vs) (rest : List Domain) (chosen a : Assignment) :
    PrefixCovers (d :: rest, chosen) a ↔
      PrefixCovers (rest, chosen ++ [v]) a ∨
        PrefixCovers (Dom.ofList vs :: rest, chosen) a :=
  prefix_covers_split (vs := Dom.ofList vs) (by simpa using hd) rest chosen a

end LeanFzn.Solver.Propagation
