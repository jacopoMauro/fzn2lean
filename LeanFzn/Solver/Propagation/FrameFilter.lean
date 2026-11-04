/-
Purpose: Filter a finite-domain branch by a literal. Two representations:

  * the sparse scheduled `BranchFrame` (S0 §4.2): `filterSlot`/`filterFrame`
    filter the literal's own ABSOLUTE slot directly (`none` exactly when the
    target domain becomes empty);
  * the positional `PrefixFrame` the chronological/reference cone keeps:
    `filterSlots`/`prefixFilterFrame` filter at the offset given by the
    chosen prefix length.

Dependencies: FrontierSemantics supplies assignment coverage; Operations and
Encoding supply literal evaluation and slot indices.
DAG: frontier semantics -> FrameFilter -> pruned search.
-/
import LeanFzn.Solver.Propagation.FrontierSemantics
import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Solver.Propagation.LiteralEval
import LeanFzn.Solver.Propagation.CompactDomain
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver


theorem valueHolds_read {l : Literal} {a : Assignment} {v : Value}
    (hv : a[l.atom.slot]? = some v) :
    l.valueHolds v = true ↔ l.eval a = some true := by
  cases l with
  | mk atom positive =>
    cases atom <;> simp only [Atom.slot] at hv
    · cases v <;> simp [Literal.eval, Atom.eval, hv, Literal.valueHolds]
    · simp [Literal.eval, Atom.eval, slotInt, hv, Literal.valueHolds]
    · simp [Literal.eval, Atom.eval, slotInt, hv, Literal.valueHolds]

theorem eval_prefix {l : Literal} {chosen tail : Assignment}
    (hlt : l.atom.slot < chosen.length) : l.eval (chosen ++ tail) = l.eval chosen := by
  have hg : (chosen ++ tail)[l.atom.slot]? = chosen[l.atom.slot]? :=
    List.getElem?_append_left hlt
  cases l with
  | mk atom positive =>
    cases atom <;> simp only [Atom.slot] at hg
    · simp [Literal.eval, Atom.eval, hg]
    · simp [Literal.eval, Atom.eval, slotInt, hg]
    · simp [Literal.eval, Atom.eval, slotInt, hg]

/-! ## Positional filtering (chronological/reference cone) -/

/-- Filter exactly the referenced remaining slot at the given offset: offset
`0` is the first remaining domain. -/
def filterSlots (l : Literal) (offset : Nat) : List Domain → List Domain
  | [] => []
  | d :: rest =>
      (if offset = l.atom.slot then Dom.filterLitKeep l d else d) ::
        filterSlots l (offset + 1) rest

/-- The positional frame filter: a literal referring to the chosen prefix
either accepts or rejects the frame; a literal referring to a remaining
domain filters that domain in place. -/
def prefixFilterFrame (l : Literal) (f : PrefixFrame) : Option PrefixFrame :=
  if l.atom.slot < f.2.length then
    if l.eval f.2 == some true then some f else none
  else some (filterSlots l f.2.length f.1, f.2)

theorem filterSlots_length (l : Literal) (offset : Nat) (slots : List Domain) :
    (filterSlots l offset slots).length = slots.length := by
  induction slots generalizing offset with
  | nil => rfl
  | cons d rest ih => simp [filterSlots, ih]

theorem filterSlots_cost_le (l : Literal) (offset : Nat) (slots : List Domain) :
    branchCost (filterSlots l offset slots) ≤ branchCost slots := by
  induction slots generalizing offset with
  | nil => exact Nat.le_refl _
  | cons d rest ih =>
    have hc := ih (offset + 1)
    have hd : (if offset = l.atom.slot then Dom.filterLitKeep l d else d).length ≤ d.length := by
      split
      · exact Dom.card_filterLitKeep_le l d
      · exact Nat.le_refl _
    simpa only [filterSlots, branchCost] using
      Nat.add_le_add_left (Nat.mul_le_mul hd (Nat.add_le_add_right hc 1)) 1

theorem prefixFilterFrame_cost_le {l : Literal} {f g : PrefixFrame}
    (h : prefixFilterFrame l f = some g) : branchCost g.1 ≤ branchCost f.1 := by
  unfold prefixFilterFrame at h
  split at h
  · split at h
    · cases h; exact Nat.le_refl _
    · cases h
  · cases h; exact filterSlots_cost_le _ _ _

private theorem allAssigns_cons (d : Domain) (rest : List Domain) (tail : Assignment) :
    tail ∈ allAssigns (d :: rest) ↔
      ∃ v ∈ d, ∃ suffix ∈ allAssigns rest, tail = v :: suffix :=
  mem_allAssigns_cons_iff

private theorem filterSlots_preserves (l : Literal) :
    ∀ slots offset tail, tail ∈ allAssigns slots →
    (∀ i v, tail[i]? = some v → offset + i = l.atom.slot → l.valueHolds v = true) →
    tail ∈ allAssigns (filterSlots l offset slots) := by
  intro slots
  induction slots with
  | nil => intro offset tail ht _; exact ht
  | cons d rest ih =>
    intro offset tail ht hv
    obtain ⟨v, hmem, suffix, hs, rfl⟩ := (allAssigns_cons d rest tail).mp ht
    apply (allAssigns_cons _ _ _).mpr
    refine ⟨v, ?_, suffix, ?_, rfl⟩
    · split
      · exact Dom.mem_filterLitKeep_iff.mpr ⟨hmem, hv 0 v (by simp) (by omega)⟩
      · exact hmem
    · apply ih (offset + 1) suffix hs
      intro i w hget heq
      exact hv (i + 1) w (by simpa using hget) (by omega)

theorem prefixFilterFrame_preserves {l : Literal} {f : PrefixFrame} {a : Assignment}
    (hcover : PrefixCovers f a) (he : l.eval a = some true) :
    ∃ g, prefixFilterFrame l f = some g ∧ PrefixCovers g a := by
  obtain ⟨tail, ht, rfl⟩ := hcover
  unfold prefixFilterFrame
  split
  · rename_i hlt
    have hp : l.eval f.2 = some true := by rw [← eval_prefix hlt]; exact he
    simp only [hp, BEq.rfl, if_true]
    exact ⟨f, rfl, tail, ht, rfl⟩
  · refine ⟨(filterSlots l f.2.length f.1, f.2), rfl, tail, ?_, rfl⟩
    apply filterSlots_preserves l f.1 f.2.length tail ht
    intro i v hv heq
    apply (valueHolds_read ?_).mpr he
    rw [← heq]
    simpa using List.getElem?_append_right (l₁ := f.2) (l₂ := tail) (by omega : f.2.length ≤ f.2.length + i) |>.trans (by simpa using hv)

/-- Full box represented by a positional frame, including singleton chosen slots. -/
def PrefixFrame.domains (f : PrefixFrame) : List Domain :=
  f.2.map (fun v => Dom.ofList [v]) ++ f.1

/-- Remaining-domain cardinality of a positional frame. -/
def PrefixFrame.mass (f : PrefixFrame) : Nat := (f.1.map fun d => d.length).sum

theorem filterSlots_mass_le (l : Literal) (offset : Nat) (slots : List Domain) :
    ((filterSlots l offset slots).map fun d => d.length).sum ≤
      (slots.map fun d => d.length).sum := by
  induction slots generalizing offset with
  | nil => exact Nat.le_refl _
  | cons d rest ih =>
    have hd : (if offset = l.atom.slot then Dom.filterLitKeep l d else d).length ≤ d.length := by
      split
      · exact Dom.card_filterLitKeep_le l d
      · exact Nat.le_refl _
    simpa only [filterSlots, List.map_cons, List.sum_cons] using
      Nat.add_le_add hd (ih (offset + 1))

theorem prefixFilterFrame_mass_le {l : Literal} {f g : PrefixFrame}
    (h : prefixFilterFrame l f = some g) : g.mass ≤ f.mass := by
  unfold prefixFilterFrame at h
  split at h
  · split at h
    · cases h; exact Nat.le_refl _
    · cases h
  · cases h; exact filterSlots_mass_le _ _ _

theorem prefixFilterFrame_prefix {l : Literal} {f g : PrefixFrame}
    (h : prefixFilterFrame l f = some g) : g.2 = f.2 := by
  unfold prefixFilterFrame at h
  split at h
  · split at h <;> cases h
    rfl
  · cases h; rfl

theorem allAssigns_fits : ∀ (slots : List Domain) (tail : Assignment),
    tail ∈ allAssigns slots → tail.Fits slots := by
  intro slots
  induction slots with
  | nil =>
    intro tail ht
    have he : tail = [] := by simpa [allAssigns] using ht
    subst tail
    exact ⟨rfl, by simp⟩
  | cons d rest ih =>
    intro tail ht
    obtain ⟨v, hv, suffix, hs, rfl⟩ := (allAssigns_cons d rest tail).mp ht
    obtain ⟨hlen, hmem⟩ := ih suffix hs
    refine ⟨by simp [hlen], ?_⟩
    intro i w hw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
      simpa only [List.getD_cons_zero, ← hw] using hv
    | succ i => exact hmem i w (by simpa using hw)

private theorem fits_prefix_singletons (chosen tail : Assignment) (slots : List Domain)
    (hfit : tail.Fits slots) :
    (chosen ++ tail).Fits (chosen.map (fun v => Dom.ofList [v]) ++ slots) := by
  induction chosen with
  | nil => exact hfit
  | cons v chosen ih =>
    obtain ⟨hlen, hmem⟩ := ih
    refine ⟨by simpa using congrArg Nat.succ hlen, ?_⟩
    intro i w hw
    cases i with
    | zero => simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hw; simp [hw]
    | succ i => exact hmem i w (by simpa using hw)

theorem PrefixCovers.fits {f : PrefixFrame} {a : Assignment}
    (h : PrefixCovers f a) : a.Fits f.domains := by
  obtain ⟨tail, ht, rfl⟩ := h
  exact fits_prefix_singletons f.2 tail f.1 (allAssigns_fits _ _ ht)

/-- Filtering introduces no values in any remaining domain. -/
theorem filterSlots_subsets (l : Literal) : ∀ slots offset i v,
    v ∈ (filterSlots l offset slots).getD i Dom.empty → v ∈ slots.getD i Dom.empty := by
  intro slots
  induction slots with
  | nil => intro offset i v h; simp [filterSlots] at h
  | cons d rest ih =>
    intro offset i v h
    cases i with
    | zero =>
      simp only [filterSlots, List.getD_cons_zero] at h ⊢
      split at h
      · exact (Dom.mem_filterLitKeep_iff.mp h).1
      · exact h
    | succ i =>
      apply ih (offset + 1) i v
      simpa only [filterSlots, List.getD_cons_succ] using h

theorem prefixFilterFrame_subsets {l : Literal} {f g : PrefixFrame}
    (h : prefixFilterFrame l f = some g) :
    ∀ i v, v ∈ g.1.getD i Dom.empty → v ∈ f.1.getD i Dom.empty := by
  unfold prefixFilterFrame at h
  split at h
  · split at h
    · cases h; exact fun _ _ hm => hm
    · cases h
  · cases h; exact filterSlots_subsets _ _ _

private theorem filterSlots_refines (l : Literal) :
    ∀ slots offset tail, tail ∈ allAssigns (filterSlots l offset slots) →
      tail ∈ allAssigns slots := by
  intro slots
  induction slots with
  | nil => intro offset tail ht; exact ht
  | cons d rest ih =>
    intro offset tail ht
    obtain ⟨v, hv, suffix, hs, rfl⟩ := (allAssigns_cons _ _ tail).mp ht
    apply (allAssigns_cons _ _ _).mpr
    refine ⟨v, ?_, suffix, ih (offset + 1) suffix hs, rfl⟩
    split at hv
    · exact (Dom.mem_filterLitKeep_iff.mp hv).1
    · exact hv

theorem prefixFilterFrame_refines {l : Literal} {f g : PrefixFrame} {a : Assignment}
    (h : prefixFilterFrame l f = some g) (hc : PrefixCovers g a) : PrefixCovers f a := by
  unfold prefixFilterFrame at h
  split at h
  · split at h
    · cases h; exact hc
    · cases h
  · cases h
    obtain ⟨tail, ht, rfl⟩ := hc
    exact ⟨tail, filterSlots_refines _ _ _ _ ht, rfl⟩

/-! ## Sparse filtering (scheduled cone, S0 §4.2) -/

/-- The sparse slot filter: filter the domain at the literal's slot directly,
by absolute slot index (no positional offset). -/
def filterSlot (l : Literal) (ds : List Domain) : List Domain :=
  ds.set l.atom.slot (Dom.filterLitKeep l (ds.getD l.atom.slot Dom.empty))

/-- The sparse frame filter: filter slot `l.atom.slot` directly; `none`
exactly when the target domain becomes empty (the assigned-singleton
rejection is the positional prefix-rejection `none` case). Out-of-range
literals are a no-op, matching the positional `filterSlots` behaviour at an
out-of-range offset. -/
def filterFrame (l : Literal) (f : BranchFrame) : Option BranchFrame :=
  match f.doms[l.atom.slot]? with
  | none => some f
  | some d =>
      match Dom.enum (Dom.filterLitKeep l d) with
      | [] => none
      | _ => some { f with doms := f.doms.set l.atom.slot (Dom.filterLitKeep l d) }

/-- Compiled twin of `filterFrame`: compute the filtered slot once and test
    emptiness through the O(1) cardinality rather than expanding its
    enumeration. -/
def filterFrameFast (l : Literal) (f : BranchFrame) : Option BranchFrame :=
  match f.doms[l.atom.slot]? with
  | none => some f
  | some d =>
      let d' := Dom.filterLitKeep l d
      if d'.isEmpty then none
      else some { f with doms := f.doms.set l.atom.slot d' }

/-- The fast filter selects exactly the same frame. -/
theorem filterFrameFast_eq (l : Literal) (f : BranchFrame) :
    filterFrameFast l f = filterFrame l f := by
  unfold filterFrameFast filterFrame
  dsimp only
  split
  · rfl
  · rename_i d hd
    by_cases hem : (Dom.filterLitKeep l d).isEmpty = true
    · rw [if_pos hem]
      have hnil : Dom.enum (Dom.filterLitKeep l d) = [] :=
        (Dom.isEmpty_eq_true_iff _).mp hem
      rw [hnil]
    · rw [if_neg hem]
      have hnil : Dom.enum (Dom.filterLitKeep l d) ≠ [] := by
        intro h
        exact hem ((Dom.isEmpty_eq_true_iff _).mpr h)
      split
      · rename_i h
        exact absurd h hnil
      · rfl

attribute [implemented_by filterFrameFast] filterFrame

/-- Reading the slot a set operation wrote. -/
theorem getD_set_self {ds : List Domain} {k : Nat} {x : Domain}
    (hk : k < ds.length) : (ds.set k x).getD k Dom.empty = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk]
  rfl

/-- A fitting assignment reads a box value at an in-range slot. -/
theorem read_of_fits {ds : List Domain} {a : Assignment} (hfit : a.Fits ds)
    {k : Nat} (hk : k < ds.length) : ∃ w ∈ ds.getD k Dom.empty, a[k]? = some w := by
  have hk' : k < a.length := by rw [hfit.1]; exact hk
  refine ⟨a[k], ?_, List.getElem?_eq_getElem hk'⟩
  exact hfit.2 k a[k] (List.getElem?_eq_getElem hk')

/-- Reading a covered assignment at an in-range slot. -/
theorem exists_read_of_covers {f : BranchFrame} {a : Assignment}
    (h : FrameCovers f a) {k : Nat} (hk : k < f.doms.length) :
    ∃ v ∈ f.doms.getD k Dom.empty, a[k]? = some v :=
  read_of_fits (allAssigns_fits f.doms a h) hk

/-- Membership in `allAssigns` is preserved by writing a domain containing
the covered value at a slot. -/
theorem mem_allAssigns_set_of_mem {ds : List Domain} {a : Assignment} {k : Nat}
    {x : Domain} {v : Value} (ha : a ∈ allAssigns ds) (hk : a[k]? = some v)
    (hv : v ∈ x) : a ∈ allAssigns (ds.set k x) := by
  induction ds generalizing k a with
  | nil =>
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      simp at hk
  | cons d rest ih =>
      obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          rw [List.set_cons_zero]
          exact mem_allAssigns_cons_iff.mpr ⟨w, hk.symm ▸ hv, a', ha', rfl⟩
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          rw [List.set_cons_succ]
          exact mem_allAssigns_cons_iff.mpr ⟨w, hw, a', ih ha' hk, rfl⟩

/-- Membership in `allAssigns` is refined by writing a sub-domain at a slot. -/
theorem mem_allAssigns_of_mem_set {ds : List Domain} {a : Assignment} {k : Nat}
    {x : Domain} (hsub : ∀ v ∈ x, v ∈ ds.getD k Dom.empty)
    (ha : a ∈ allAssigns (ds.set k x)) : a ∈ allAssigns ds := by
  induction ds generalizing k a with
  | nil =>
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      exact List.mem_singleton.mpr rfl
  | cons d rest ih =>
      cases k with
      | zero =>
          rw [List.set_cons_zero] at ha
          obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
          have hwd : w ∈ d := by simpa using hsub w hw
          exact mem_allAssigns_cons_iff.mpr ⟨w, hwd, a', ha', rfl⟩
      | succ k =>
          rw [List.set_cons_succ] at ha
          obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
          have hsub' : ∀ v ∈ x, v ∈ rest.getD k Dom.empty := by
            intro v hv
            have := hsub v hv
            simpa only [List.getD_cons_succ] using this
          exact mem_allAssigns_cons_iff.mpr ⟨w, hw, a', ih hsub' ha', rfl⟩

/-- The sparse frame's full box (S0 §3.1): already the full per-slot box. -/
def Frame.domains (f : BranchFrame) : List Domain := f.doms

/-- The sparse frame mass: the sum of the domain lengths of the full box. -/
def Frame.mass (f : BranchFrame) : Nat := (f.doms.map fun d => d.length).sum

/-! ## The D0 frame denotation bridge

`Frame.domains` is the slot projection (the full per-slot box) and
`Dom.enum` is the denotation of one compact domain.  D0 names their
composition: a frame denotes the legacy list-of-value-lists box.  The sparse
frame keeps the chosen prefix as singleton entries of the same box, so its
bridge is the projection equation; the positional cone keeps the prefix
separately and has the displayed prefix-then-remaining form. -/

/-- The D0 frame denotation of a sparse frame. -/
def Frame.denote (f : BranchFrame) : List (List Value) :=
  (Frame.domains f).map Dom.enum

/-- D0 `Frame.denote_eq` (sparse form): the denotation is exactly the
    slot-wise enumeration of the frame's box. -/
theorem Frame.denote_eq (f : BranchFrame) :
    Frame.denote f = f.doms.map Dom.enum := rfl

/-- The positional frame's denotation: the chosen prefix as singletons
    followed by the remaining domains' enumerations (D0's displayed
    equation). -/
def PrefixFrame.denote (f : PrefixFrame) : List (List Value) :=
  f.2.map (fun v => [v]) ++ f.1.map Dom.enum

/-- D0 `Frame.denote_eq` (positional form). -/
theorem PrefixFrame.denote_eq (f : PrefixFrame) :
    PrefixFrame.denote f = f.2.map (fun v => [v]) ++ f.1.map Dom.enum := rfl

/-- The denotation has one entry per slot. -/
theorem Frame.denote_length (f : BranchFrame) :
    (Frame.denote f).length = f.doms.length := by
  simp [Frame.denote, Frame.domains]

/-- Reading a slot of the denotation is enumerating that slot's domain. -/
theorem Frame.denote_getD (f : BranchFrame) (i : Nat) :
    (Frame.denote f).getD i [] = (f.doms.getD i Dom.empty).enum := by
  simp only [Frame.denote, Frame.domains, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases h : f.doms[i]? with
  | none => simp [Dom.enum_empty]
  | some d => rfl

/-- The denotation's mass is the frame mass. -/
theorem Frame.denote_mass (f : BranchFrame) :
    ((Frame.denote f).map List.length).sum = Frame.mass f := by
  simp only [Frame.denote, Frame.domains, Frame.mass, List.map_map,
    Dom.length_eq_enum]
  rfl

/-- `allAssigns` depends only on the slot enumerations: the compact frame
    box and its slot-wise enumeration list have exactly the same
    assignments.  This is the bridge that makes the sparse
    `Frame.denote` agree with the frozen `allAssigns` vocabulary. -/
theorem allAssigns_dom_eq_enum (doms : List Domain) :
    allAssigns doms = allAssigns (doms.map Dom.enum) := by
  induction doms with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, allAssigns, domElems_eq_enum,
        DomainElems.elems_list, ih]

/-- Coverage is membership in the denotation's box. -/
theorem FrameCovers.denote_iff (f : BranchFrame) (a : Assignment) :
    FrameCovers f a ↔ a ∈ allAssigns (Frame.denote f) := by
  unfold FrameCovers
  rw [Frame.denote_eq, allAssigns_dom_eq_enum]

/-- Pinning denotes to writing the singleton at the selected slot. -/
theorem Frame.denote_pin (f : BranchFrame) (k : Nat) (v : Value) :
    Frame.denote (f.pin k v) = (Frame.denote f).set k [v] := by
  simp [Frame.denote, Frame.domains, BranchFrame.pin_doms, List.map_set]

/-- Retiring denotes to writing the sibling enumeration at the selected
    slot (the split's coverage transport). -/
theorem Frame.denote_retire (f : BranchFrame) (k : Nat) (vs : Domain) :
    Frame.denote (f.retire k vs) = (Frame.denote f).set k vs.enum := by
  simp [Frame.denote, Frame.domains, BranchFrame.retire_doms, List.map_set]

/-- A covered assignment fits the frame's box. -/
theorem FrameCovers.fits {f : BranchFrame} {a : Assignment}
    (h : FrameCovers f a) : a.Fits (Frame.domains f) :=
  allAssigns_fits f.doms a h

/-- Filtering narrows the box pointwise: every value of the filtered slot
was already present. -/
theorem filterFrame_subsets {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) :
    ∀ i v, v ∈ g.doms.getD i Dom.empty → v ∈ f.doms.getD i Dom.empty := by
  unfold filterFrame at h
  split at h
  · cases h; exact fun _ _ hm => hm
  · rename_i d hd
    split at h
    · cases h
    · cases h
      intro i v hv
      rw [List.getD_eq_getElem?_getD] at hv
      rw [List.getElem?_set] at hv
      split at hv
      · rename_i hik
        split at hv
        · rename_i hk
          rw [Option.getD_some] at hv
          rw [Dom.mem_filterLitKeep_iff] at hv
          rw [← hik, List.getD_eq_getElem?_getD, hd, Option.getD_some]
          exact hv.1
        · simp at hv
      · rw [List.getD_eq_getElem?_getD]
        exact hv

/-- Writing a sub-domain at a slot refines the box pointwise. -/
theorem getD_set_subset {ds : List Domain} {k : Nat} {x : Domain}
    (hsub : ∀ w ∈ x, w ∈ ds.getD k Dom.empty) :
    ∀ i w, w ∈ (ds.set k x).getD i Dom.empty → w ∈ ds.getD i Dom.empty := by
  intro i w hw
  rw [List.getD_eq_getElem?_getD] at hw
  rw [List.getElem?_set] at hw
  split at hw
  · rename_i hik
    split at hw
    · rename_i hk
      rw [Option.getD_some] at hw
      rw [← hik]
      exact hsub w hw
    · simp at hw
  · rw [List.getD_eq_getElem?_getD]
    exact hw

/-- Membership in `allAssigns` is preserved by overwriting a covered
assignment's coordinate with another value of the box at that slot. -/
theorem mem_allAssigns_set_coord {ds : List Domain} {a : Assignment} {k : Nat}
    {w : Value} (ha : a ∈ allAssigns ds) (hk : k < ds.length)
    (hw : w ∈ ds.getD k Dom.empty) : a.set k w ∈ allAssigns ds := by
  have hfits := allAssigns_fits ds a ha
  refine mem_allAssigns_of_getElem? ds (a.set k w) ?_ ?_
  · rw [List.length_set, hfits.1]
  · intro j v hv
    rw [List.getElem?_set] at hv
    by_cases hjk : k = j
    · rw [if_pos hjk] at hv
      split at hv
      · rename_i hk'
        rw [Option.some.injEq] at hv
        subst hv
        rw [← hjk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some]
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some] at hw
      · cases hv
    · rw [if_neg hjk] at hv
      exact hfits.2 j v hv

/-- The sparse filter preserves exactly the assignments satisfying the
literal: enum-level coverage equivalence. -/
theorem Frame.covers_filterFrame_iff {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) (hsl : l.atom.slot < f.doms.length)
    (a : Assignment) :
    FrameCovers g a ↔ FrameCovers f a ∧ l.eval a = some true := by
  unfold filterFrame at h
  split at h
  · rename_i _ hd
    rw [List.getElem?_eq_none_iff] at hd
    omega
  · rename_i _ d hd
    split at h
    · rename_i _ hfil
      cases h
    · cases h
      constructor
      · intro hc
        have hfit : a.Fits (f.doms.set l.atom.slot (Dom.filterLitKeep l d)) :=
          allAssigns_fits _ _ hc
        have hklt' : l.atom.slot <
            (f.doms.set l.atom.slot (Dom.filterLitKeep l d)).length := by
          rwa [List.length_set]
        obtain ⟨w, hw, hread⟩ := read_of_fits hfit hklt'
        rw [getD_set_self hsl] at hw
        have hvw : l.valueHolds w = true := (Dom.mem_filterLitKeep_iff.mp hw).2
        refine ⟨mem_allAssigns_of_mem_set ?_ hc, (valueHolds_read hread).mp hvw⟩
        intro u hu
        have hud : u ∈ d := (Dom.mem_filterLitKeep_iff.mp hu).1
        rwa [List.getD_eq_getElem?_getD, hd]
      · rintro ⟨hc, hev⟩
        obtain ⟨w, hwd, hread⟩ := exists_read_of_covers hc hsl
        have hvw : l.valueHolds w = true := (valueHolds_read hread).mpr hev
        have hwd' : w ∈ d := by rwa [List.getD_eq_getElem?_getD, hd] at hwd
        exact mem_allAssigns_set_of_mem hc hread (Dom.mem_filterLitKeep_iff.mpr ⟨hwd', hvw⟩)

/-- When the sparse filter rejects, no covered assignment satisfies the
literal. -/
theorem Frame.covers_filterFrame_none {l : Literal} {f : BranchFrame}
    (h : filterFrame l f = none) :
    ∀ a, FrameCovers f a → l.eval a ≠ some true := by
  intro a hc hev
  unfold filterFrame at h
  split at h
  · cases h
  · rename_i _ d hd
    split at h
    · rename_i _ hfil
      have hklt : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      obtain ⟨w, hwd, hread⟩ := exists_read_of_covers hc hklt
      have hwd' : w ∈ d := by
        rwa [List.getD_eq_getElem?_getD, hd] at hwd
      have hfilter : (Dom.filter l.valueHolds d).enum = [] := by
        rw [Dom.enum_filter, ← Dom.enum_filterLitKeep]
        exact hfil
      have hfalse : ¬ l.valueHolds w = true :=
        (enum_filter_eq_nil_iff.mp hfilter) w hwd'
      have : l.valueHolds w = true := (valueHolds_read hread).mpr hev
      exact hfalse this
    · cases h

/-- Narrowing never changes the decision order: the sparse filter is a
narrowing of the box, not a decision. -/
theorem Frame.filterFrame_order {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : g.order = f.order := by
  unfold filterFrame at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- Exact rejection criterion for the sparse filter. -/
theorem Frame.filterFrame_eq_none_iff (l : Literal) (f : BranchFrame) :
    filterFrame l f = none ↔
      ∃ d : Domain, f.doms[l.atom.slot]? = some d ∧
        Dom.enum (Dom.filterLitKeep l d) = [] := by
  constructor
  · intro h
    unfold filterFrame at h
    split at h
    · cases h
    · rename_i _ d hd
      split at h
      · rename_i _ hfil
        exact ⟨d, hd, hfil⟩
      · cases h
  · rintro ⟨d, hd, hfil⟩
    simp only [filterFrame, hd, hfil]

/-- Filtering an out-of-range slot is a no-op. -/
theorem filterSlot_eq_self_of_le_length (l : Literal) (ds : List Domain)
    (h : ds.length ≤ l.atom.slot) : filterSlot l ds = ds := by
  unfold filterSlot
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  exact List.set_eq_of_length_le h

/-- Reading a set at a different index. -/
theorem getElem?_set_of_ne {α : Type} {ds : List α} {k i : Nat} {x : α}
    (h : i ≠ k) : (ds.set k x)[i]? = ds[i]? := by
  rw [List.getElem?_set, if_neg (fun hki => h hki.symm)]

/-- The sparse filter never empties an already-singleton slot. -/
theorem filterFrame_singleton {l : Literal} {f g : BranchFrame} {k : Nat}
    {v : Value} (hg : filterFrame l f = some g)
    (hk : f.doms[k]?.map Dom.enum = some [v]) :
    g.doms[k]?.map Dom.enum = some [v] := by
  obtain ⟨d₀, hd₀, hden₀⟩ : ∃ d, f.doms[k]? = some d ∧ d.enum = [v] := by
    cases h : f.doms[k]? with
    | none => rw [h] at hk; cases hk
    | some d => exact ⟨d, rfl, by simpa [h] using hk⟩
  unfold filterFrame at hg
  split at hg
  · cases hg
    rw [hd₀]
    simp [hden₀]
  · rename_i d hd
    split at hg
    · cases hg
    · rename_i hfil
      cases hg
      by_cases hkd : l.atom.slot = k
      · subst hkd
        have hsame : d = d₀ := Option.some.inj (hd.symm.trans hd₀)
        have hden : d.enum = [v] := by rw [hsame, hden₀]
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd).1]
        have hflt : (Dom.filterLitKeep l d).enum = [v] := by
          by_cases hp : l.valueHolds v = true
          · rw [Dom.enum_filterLitKeep, hden, List.filter_cons_of_pos hp]
            rfl
          · exfalso
            apply hfil
            rw [Dom.enum_filterLitKeep, hden, List.filter_cons_of_neg hp]
            rfl
        simp [hflt]
      · rw [getElem?_set_of_ne (fun hki => hkd hki.symm), hd₀]
        simp [hden₀]

/-- A sparse filter only narrows a singleton slot by keeping its value:
agreement with the filtered frame's singletons implies agreement with the
original frame's singletons. -/
theorem pinsAgree_of_filterFrame {l : Literal} {f g : BranchFrame} {a : Assignment}
    (hg : filterFrame l f = some g) (h : Frame.PinsAgree g a) : Frame.PinsAgree f a := by
  intro k v hk
  exact h k v (filterFrame_singleton hg hk)

/-- Writing the structural literal filter of a slot's own domain never
    increases `branchCost`. -/
private theorem branchCost_set_filterKeep_le : ∀ (ds : List Domain) (s : Nat)
    (l : Literal),
    branchCost (ds.set s (Dom.filterLitKeep l (ds.getD s Dom.empty))) ≤ branchCost ds := by
  intro ds
  induction ds with
  | nil => intro s l; simp only [List.set_nil, branchCost]; exact Nat.le_refl 1
  | cons d rest ih =>
      intro s l
      cases s with
      | zero =>
          simp only [List.getD_cons_zero, List.set_cons_zero, branchCost]
          have hlen : (Dom.filterLitKeep l d).length ≤ d.length := Dom.card_filterLitKeep_le l d
          have h1 : (Dom.filterLitKeep l d).length * (branchCost rest + 1) ≤
              d.length * (branchCost rest + 1) :=
            Nat.mul_le_mul hlen (Nat.le_refl _)
          omega
      | succ j =>
          simp only [List.getD_cons_succ, List.set_cons_succ, branchCost]
          have ih' := ih j l
          have h1 : d.length * (branchCost (rest.set j (Dom.filterLitKeep l (rest.getD j Dom.empty))) + 1) ≤
              d.length * (branchCost rest + 1) :=
            Nat.mul_le_mul (Nat.le_refl _) (Nat.add_le_add_right ih' 1)
          omega

/-- Writing the structural literal filter of a slot's own domain never
    increases the box mass (sum of domain lengths). -/
private theorem mass_set_filterKeep_le : ∀ (ds : List Domain) (s : Nat)
    (l : Literal),
    ((ds.set s (Dom.filterLitKeep l (ds.getD s Dom.empty))).map fun d => d.length).sum ≤
      (ds.map fun d => d.length).sum := by
  intro ds
  induction ds with
  | nil => intro s l; simp only [List.set_nil, List.map_nil, List.sum_nil]; exact Nat.le_refl 0
  | cons d rest ih =>
      intro s l
      cases s with
      | zero =>
          simp only [List.getD_cons_zero, List.set_cons_zero, List.map_cons,
            List.sum_cons]
          exact Nat.add_le_add (Dom.card_filterLitKeep_le l d) (Nat.le_refl _)
      | succ j =>
          simp only [List.getD_cons_succ, List.set_cons_succ, List.map_cons,
            List.sum_cons]
          exact Nat.add_le_add (Nat.le_refl _) (ih j l)

/-- The sparse filter never increases the frame mass. -/
theorem filterFrame_mass_le {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : Frame.mass g ≤ Frame.mass f := by
  unfold filterFrame at h
  split at h
  · cases h; exact Nat.le_refl _
  · rename_i d hd
    split at h
    · cases h
    · cases h
      have hdget : f.doms.getD l.atom.slot Dom.empty = d := by
        rw [List.getD_eq_getElem?_getD, hd]
        rfl
      show ((f.doms.set l.atom.slot (Dom.filterLitKeep l d)).map fun d => d.length).sum ≤
        (f.doms.map fun d => d.length).sum
      rw [← hdget]
      exact mass_set_filterKeep_le f.doms l.atom.slot l

/-- Overwriting a coordinate with the value it already reads leaves the
assignment unchanged (in-range reads only). -/
theorem list_set_eq_self_of_read {a : Assignment} {k : Nat} {v : Value}
    (hk : k < a.length) (hread : a[k]? = some v) : a.set k v = a := by
  apply List.ext_getElem?
  intro j
  by_cases hjk : k = j
  · subst hjk
    rw [List.getElem?_set_self hk, hread]
  · exact getElem?_set_of_ne (fun h => hjk h.symm)

/-- A covered assignment that reads the pinned value at slot `k` is
covered by the pinned child's box (`doms.set k [v]`): the pin writes the
value the assignment already carries there. -/
theorem mem_allAssigns_set_of_read {ds : List Domain} {a : Assignment}
    {k : Nat} {v : Value} (ha : a ∈ allAssigns ds)
    (hk : k < ds.length) (hv : v ∈ ds.getD k Dom.empty)
    (hread : a[k]? = some v) :
    a ∈ allAssigns (ds.set k (Dom.ofList [v])) := by
  have hkset : k < (ds.set k (Dom.ofList [v])).length := by
    rw [List.length_set]; exact hk
  refine mem_allAssigns_of_getElem? _ _ ?_ ?_
  · rw [List.length_set, (allAssigns_fits _ _ ha).1]
  · intro j w hw
    by_cases hjk : j = k
    · rw [hjk] at hw ⊢
      rw [hread] at hw
      have hwv : w = v := (Option.some.inj hw).symm
      subst hwv
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk,
        Option.getD_some]
      simp
    · have hget : (ds.set k (Dom.ofList [v]))[j]? = ds[j]? :=
        getElem?_set_of_ne (fun h => hjk h)
      have hset : (ds.set k (Dom.ofList [v])).getD j DomainLike.empty =
          ds.getD j DomainLike.empty := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hget]
      rw [hset]
      exact (allAssigns_fits _ _ ha).2 j w hw

/-- The sparse filter never increases the frame cost. -/
theorem filterFrame_cost_le {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : branchCost g.doms ≤ branchCost f.doms := by
  unfold filterFrame at h
  split at h
  · cases h; exact Nat.le_refl _
  · rename_i d hd
    split at h
    · cases h
    · cases h
      have hdget : f.doms.getD l.atom.slot Dom.empty = d := by
        rw [List.getD_eq_getElem?_getD, hd]
        rfl
      rw [← hdget]
      exact branchCost_set_filterKeep_le f.doms l.atom.slot l

/-- The sparse filter preserves the slot count. -/
theorem filterFrame_rem_length {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) : g.doms.length = f.doms.length := by
  unfold filterFrame at hg
  split at hg
  · cases hg; rfl
  · rename_i d hd
    split at hg
    · cases hg
    · cases hg; rw [List.length_set]

/-- The sparse filter preserves every covered assignment satisfying the
literal: the filtered frame still covers it. -/
theorem filterFrame_preserves {l : Literal} {f : BranchFrame} {a : Assignment}
    (hcover : FrameCovers f a) (he : l.eval a = some true) :
    ∃ g, filterFrame l f = some g ∧ FrameCovers g a := by
  unfold filterFrame
  split
  · exact ⟨f, rfl, hcover⟩
  · rename_i d hd
    split
    · rename_i hfil
      exfalso
      have hsl : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      obtain ⟨w, hw, hread⟩ := exists_read_of_covers hcover hsl
      have hwd : w ∈ d := by rwa [List.getD_eq_getElem?_getD, hd] at hw
      have hvw : l.valueHolds w = true := (valueHolds_read hread).mpr he
      have hfilter : (Dom.filter l.valueHolds d).enum = [] := by
        rw [Dom.enum_filter, ← Dom.enum_filterLitKeep]
        exact hfil
      exact (enum_filter_eq_nil_iff.mp hfilter) w hwd hvw
    · refine ⟨{ f with doms := f.doms.set l.atom.slot (Dom.filterLitKeep l d) },
        rfl, ?_⟩
      have hsl : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      obtain ⟨w, hw, hread⟩ := exists_read_of_covers hcover hsl
      have hwd : w ∈ d := by rwa [List.getD_eq_getElem?_getD, hd] at hw
      have hvw : l.valueHolds w = true := (valueHolds_read hread).mpr he
      have hwd' : w ∈ Dom.filterLitKeep l d := Dom.mem_filterLitKeep_iff.mpr ⟨hwd, hvw⟩
      exact mem_allAssigns_set_of_mem hcover hread hwd'

/-- The sparse filter refines coverage: every assignment covered by the
narrowed frame was already covered by the original frame. -/
theorem filterFrame_refines {l : Literal} {f g : BranchFrame} {a : Assignment}
    (h : filterFrame l f = some g) (hc : FrameCovers g a) : FrameCovers f a := by
  unfold filterFrame at h
  split at h
  · cases h; exact hc
  · rename_i d hd
    split at h
    · cases h
    · cases h
      have hc' : a ∈ allAssigns
          (f.doms.set l.atom.slot (Dom.filterLitKeep l d)) := hc
      exact mem_allAssigns_of_mem_set
        (ds := f.doms) (k := l.atom.slot) (x := Dom.filterLitKeep l d)
        (fun u hu => by
          rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
          exact (Dom.mem_filterLitKeep_iff.mp hu).1) hc'

/-- A value dropped by the sparse filter at slot `i` is falsified by the
filtering literal at that same slot. -/
theorem filterFrame_removal_witness {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) {i : Nat} {w : Value}
    (hmem : w ∈ f.doms.getD i Dom.empty) (hnot : w ∉ g.doms.getD i Dom.empty) :
    l.atom.slot = i ∧ l.valueHolds w = false := by
  unfold filterFrame at hg
  split at hg
  · cases hg
    exact absurd hmem hnot
  · rename_i d hd
    split at hg
    · cases hg
    · cases hg
      have hnot' : w ∉ (f.doms.set l.atom.slot (Dom.filterLitKeep l d)).getD i Dom.empty :=
        hnot
      by_cases hik : l.atom.slot = i
      · refine ⟨hik, ?_⟩
        have hgetD : (f.doms.set l.atom.slot (Dom.filterLitKeep l d)).getD i Dom.empty
            = Dom.filterLitKeep l d := by
          rw [← hik, List.getD_eq_getElem?_getD,
            List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd).1]
          rfl
        rw [hgetD] at hnot'
        by_cases hv : l.valueHolds w
        · exfalso
          apply hnot'
          refine Dom.mem_filterLitKeep_iff.mpr ⟨?_, hv⟩
          rwa [hik.symm, List.getD_eq_getElem?_getD, hd, Option.getD_some] at hmem
        · simpa [hv] using hv
      · exfalso
        apply hnot'
        rw [List.getD_eq_getElem?_getD] at hmem ⊢
        rw [getElem?_set_of_ne (fun hki => hik hki.symm)]
        exact hmem

/-- An assignment covered by the NARROWED sparse frame satisfies the
narrowing literal (normalized), provided the literal names an in-range
slot. Derived from the filter, not assumed. -/
theorem filterFrame_literal_holds {l : Literal} {f g : BranchFrame}
    {a : Assignment}
    (hg : filterFrame l f = some g) (hcov : FrameCovers g a)
    (hin : l.atom.slot < (Frame.domains g).length) :
    l.norm.eval a = some true := by
  rw [Literal.norm_eval]
  unfold filterFrame at hg
  split at hg
  · rename_i hd
    cases hg
    exfalso
    rw [Frame.domains] at hin
    have := List.getElem?_eq_none_iff.mp hd
    omega
  · rename_i d hd
    split at hg
    · cases hg
    · cases hg
      have hk : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      obtain ⟨w, hw, hread⟩ := exists_read_of_covers hcov (by
        simpa [Frame.domains, List.length_set] using hin)
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk] at hw
      have hvw : l.valueHolds w = true := (Dom.mem_filterLitKeep_iff.mp hw).2
      exact (valueHolds_read hread).mp hvw

end LeanFzn.Solver.Propagation
