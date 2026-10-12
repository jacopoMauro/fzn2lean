/-
Purpose: Filter a finite-domain branch by a literal without changing its chosen prefix.
Dependencies: FrontierSemantics supplies assignment coverage; Operations and Encoding
supply literal evaluation and slot indices. DAG: frontier semantics -> FrameFilter -> pruned search.
-/
import LeanFzn.Solver.Propagation.FrontierSemantics
import LeanFzn.Solver.Propagation.Encoding
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-- Evaluate a literal on the value of its referenced slot. -/
def Literal.valueHolds (l : Literal) (v : Value) : Bool :=
  let b := match l.atom with
    | .boolEq _ expected => match v with
      | .bool actual => some (actual == expected)
      | _ => none
    | .intLe _ upper => v.intView.map fun actual => decide (actual ≤ upper)
    | .intNe _ forbidden => v.intView.map fun actual => decide (actual ≠ forbidden)
  (b.map fun x => if l.positive then x else !x) == some true

/-- Filter exactly the referenced remaining slot; offset is the prefix length. -/
def filterSlots (l : Literal) (offset : Nat) : List Domain → List Domain
  | [] => []
  | d :: rest =>
      (if offset = l.atom.slot then d.filter l.valueHolds else d) ::
        filterSlots l (offset + 1) rest

/-- A literal referring to the chosen prefix either accepts or rejects the frame.
A literal referring to a remaining domain filters that domain in place. -/
def filterFrame (l : Literal) (f : BranchFrame) : Option BranchFrame :=
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
    have hd : (if offset = l.atom.slot then d.filter l.valueHolds else d).length ≤ d.length := by
      split
      · exact List.length_filter_le _ _
      · exact Nat.le_refl _
    simpa only [filterSlots, branchCost] using
      Nat.add_le_add_left (Nat.mul_le_mul hd (Nat.add_le_add_right hc 1)) 1

theorem filterFrame_cost_le {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : branchCost g.1 ≤ branchCost f.1 := by
  unfold filterFrame at h
  split at h
  · split at h
    · cases h; exact Nat.le_refl _
    · cases h
  · cases h; exact filterSlots_cost_le _ _ _

private theorem allAssigns_cons (d : Domain) (rest : List Domain) (tail : Assignment) :
    tail ∈ allAssigns (d :: rest) ↔
      ∃ v ∈ d, ∃ suffix ∈ allAssigns rest, tail = v :: suffix := by
  cases d with
  | nil => simp [allAssigns]
  | cons v vs => exact mem_allAssigns_singleton v vs rest tail

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
      · exact List.mem_filter.mpr ⟨hmem, hv 0 v (by simp) (by omega)⟩
      · exact hmem
    · apply ih (offset + 1) suffix hs
      intro i w hget heq
      exact hv (i + 1) w (by simpa using hget) (by omega)

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

theorem filterFrame_preserves {l : Literal} {f : BranchFrame} {a : Assignment}
    (hcover : FrameCovers f a) (he : l.eval a = some true) :
    ∃ g, filterFrame l f = some g ∧ FrameCovers g a := by
  obtain ⟨tail, ht, rfl⟩ := hcover
  unfold filterFrame
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

/-- Full box represented by a frame, including singleton chosen slots. -/
def Frame.domains (f : BranchFrame) : List Domain :=
  f.2.map (fun v => [v]) ++ f.1

/-- Remaining-domain cardinality used to detect strictly effective propagation. -/
def Frame.mass (f : BranchFrame) : Nat := (f.1.map List.length).sum

theorem filterSlots_mass_le (l : Literal) (offset : Nat) (slots : List Domain) :
    ((filterSlots l offset slots).map List.length).sum ≤ (slots.map List.length).sum := by
  induction slots generalizing offset with
  | nil => exact Nat.le_refl _
  | cons d rest ih =>
    have hd : (if offset = l.atom.slot then d.filter l.valueHolds else d).length ≤ d.length := by
      split
      · exact List.length_filter_le _ _
      · exact Nat.le_refl _
    simpa only [filterSlots, List.map_cons, List.sum_cons] using
      Nat.add_le_add hd (ih (offset + 1))

theorem filterFrame_mass_le {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : Frame.mass g ≤ Frame.mass f := by
  unfold filterFrame at h
  split at h
  · split at h
    · cases h; exact Nat.le_refl _
    · cases h
  · cases h; exact filterSlots_mass_le _ _ _

theorem filterFrame_prefix {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) : g.2 = f.2 := by
  unfold filterFrame at h
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
    (chosen ++ tail).Fits (chosen.map (fun v => [v]) ++ slots) := by
  induction chosen with
  | nil => exact hfit
  | cons v chosen ih =>
    obtain ⟨hlen, hmem⟩ := ih
    refine ⟨by simpa using congrArg Nat.succ hlen, ?_⟩
    intro i w hw
    cases i with
    | zero => simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hw; simp [hw]
    | succ i => exact hmem i w (by simpa using hw)

theorem FrameCovers.fits {f : BranchFrame} {a : Assignment}
    (h : FrameCovers f a) : a.Fits (Frame.domains f) := by
  obtain ⟨tail, ht, rfl⟩ := h
  exact fits_prefix_singletons f.2 tail f.1 (allAssigns_fits _ _ ht)

/-- Filtering introduces no values in any remaining domain. -/
theorem filterSlots_subsets (l : Literal) : ∀ slots offset i v,
    v ∈ (filterSlots l offset slots).getD i [] → v ∈ slots.getD i [] := by
  intro slots
  induction slots with
  | nil => intro offset i v h; simp [filterSlots] at h
  | cons d rest ih =>
    intro offset i v h
    cases i with
    | zero =>
      simp only [filterSlots, List.getD_cons_zero] at h ⊢
      split at h
      · exact (List.mem_filter.mp h).1
      · exact h
    | succ i =>
      apply ih (offset + 1) i v
      simpa only [filterSlots, List.getD_cons_succ] using h

theorem filterFrame_subsets {l : Literal} {f g : BranchFrame}
    (h : filterFrame l f = some g) :
    ∀ i v, v ∈ g.1.getD i [] → v ∈ f.1.getD i [] := by
  unfold filterFrame at h
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
    · exact (List.mem_filter.mp hv).1
    · exact hv

theorem filterFrame_refines {l : Literal} {f g : BranchFrame} {a : Assignment}
    (h : filterFrame l f = some g) (hc : FrameCovers g a) : FrameCovers f a := by
  unfold filterFrame at h
  split at h
  · split at h
    · cases h; exact hc
    · cases h
  · cases h
    obtain ⟨tail, ht, rfl⟩ := hc
    exact ⟨tail, filterSlots_refines _ _ _ _ ht, rfl⟩

end LeanFzn.Solver.Propagation
