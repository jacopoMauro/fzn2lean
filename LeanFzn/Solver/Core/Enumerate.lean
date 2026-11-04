import LeanFzn.Semantics.ValueEquality

/-! Finite Cartesian-product assignment semantics and membership lemmas.
Shared by compiler proofs, propagation and both search strategies.

The carrier of a slot is abstracted by `DomainElems`: the legacy source
slots (`List Value`) are their own enumeration, while the compact `Dom`
carrier enumerates through its denotation `Dom.enum`.  This keeps every
`allAssigns` statement valid both for compiler source slots and for the
runtime frame domains after the D2 S1 type switch. -/

namespace LeanFzn.Solver.Core
open LeanFzn.Semantics

/-- The element enumeration of a domain carrier.  `List Value` uses itself;
    the compact `Dom` uses `Dom.enum` (instance in `Core.CompactDomain`). -/
class DomainElems (α : Type) where
  elems : α → List Value

/-- A domain carrier with its empty element, and the membership law that
    connects the `Membership` instance to the enumeration.  This is the
    single abstraction used by `allAssigns`, `Assignment.Fits` and the
    coverage lemmas, so compiler source slots and runtime `Dom` frames
    share one set of statements. -/
class DomainLike (α : Type) extends Membership Value α, DomainElems α where
  empty : α
  mem_iff : ∀ (d : α) (v : Value), (v ∈ d) ↔ v ∈ elems d

/-- The legacy list carrier enumerates itself and has list membership. -/
instance : DomainLike (List Value) where
  mem := fun d v => List.Mem v d
  elems := fun xs => xs
  empty := []
  mem_iff := fun _ _ => Iff.rfl

/-- Unfolding the list carrier's enumeration for `simp`. -/
@[simp] theorem DomainElems.elems_list (xs : List Value) :
    DomainElems.elems xs = xs := rfl

/-- Unfolding the list carrier's empty slot for `simp`. -/
@[simp] theorem DomainLike.empty_list :
    DomainLike.empty (α := List Value) = [] := rfl

/-- **The specification**: every complete assignment of the slots —
    one value per slot, in slot order.  A slot with an empty domain
    contributes no assignments. -/
def allAssigns {α : Type} [DomainElems α] : List α → List (List Value)
  | [] => [[]]
  | d :: rest =>
      match DomainElems.elems d with
      | [] => []
      | v :: vs =>
          (allAssigns rest).flatMap (fun a => (v :: vs).map (fun w => w :: a))

/-! ## Basic facts about `allAssigns` -/

/-- Single-slot assignments of a non-empty compact/list domain, stated
    through the enumeration hypothesis `hs`. -/
theorem mem_allAssigns_cons {α : Type} [DomainElems α] {d : α} {v : Value}
    {vs : List Value} (hs : DomainElems.elems d = v :: vs)
    (rest : List α) (a : List Value) :
    a ∈ allAssigns (d :: rest) ↔
      ∃ w ∈ (v :: vs), ∃ a' ∈ allAssigns rest, a = w :: a' := by
  simp only [allAssigns, hs, List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨a', ha', w, hw, heq⟩ => ⟨w, hw, a', ha', heq.symm⟩,
    fun ⟨w, hw, a', ha', heq⟩ => ⟨a', ha', w, hw, heq.symm⟩⟩

/-- An empty slot enumeration makes the whole assignment list empty. -/
theorem allAssigns_cons_eq_nil {α : Type} [DomainElems α] {d : α} {rest : List α}
    (hd : DomainElems.elems d = []) : allAssigns (d :: rest) = [] := by
  simp only [allAssigns, hd]

/-- Single-slot assignments of a non-empty source slot (the legacy form). -/
theorem mem_allAssigns_singleton (v : Value) (vs : List Value)
    (rest : List (List Value)) (a : List Value) :
    a ∈ allAssigns ((v :: vs) :: rest) ↔
      ∃ w ∈ (v :: vs), ∃ a' ∈ allAssigns rest, a = w :: a' :=
  mem_allAssigns_cons (d := (v :: vs)) rfl rest a

/-- Extending a domain cannot remove assignments: `allAssigns` is
    monotone in the first slot's domain. -/
theorem allAssigns_subset_cons_of_elems {α : Type} [DomainElems α]
    {d d' : α} {v : Value} {vs : List Value}
    (hd : DomainElems.elems d = vs) (hd' : DomainElems.elems d' = v :: vs)
    (rest : List α) (a : List Value) :
    a ∈ allAssigns (d :: rest) → a ∈ allAssigns (d' :: rest) := by
  intro ha
  cases vs with
  | nil =>
      simp only [allAssigns, hd] at ha
      cases ha
  | cons w ws =>
      simp only [allAssigns, hd, hd', List.mem_flatMap, List.mem_map] at ha ⊢
      obtain ⟨a', ha', w', hw', rfl⟩ := ha
      exact ⟨a', ha', w', List.mem_cons_of_mem _ hw', rfl⟩

/-- The legacy source-slot form of monotonicity. -/
theorem allAssigns_subset_cons (v : Value) (vs : List Value)
    (rest : List (List Value)) (a : List Value) :
    a ∈ allAssigns (vs :: rest) → a ∈ allAssigns ((v :: vs) :: rest) :=
  allAssigns_subset_cons_of_elems (d := vs) (d' := v :: vs) rfl rfl rest a

/-- Splitting the slots splits the assignments: an assignment of
    `s₁ ++ s₂` is an assignment of `s₁` followed by one of `s₂`. -/
theorem allAssigns_append_of_elems {α : Type} [DomainElems α]
    (a : List Value) (s₁ s₂ : List α) :
    a ∈ allAssigns (s₁ ++ s₂) ↔
      ∃ a₁ ∈ allAssigns s₁, ∃ a₂ ∈ allAssigns s₂, a = a₁ ++ a₂ := by
  induction s₁ generalizing a with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h
        exact ⟨[], by simp [allAssigns], a, h, rfl⟩
      · rintro ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        have h1 : a₁ = [] := List.mem_singleton.mp ha₁
        subst h1
        exact ha₂
  | cons d ds ih =>
      cases hd : DomainElems.elems d with
      | nil =>
          constructor
          · intro h
            have h2 : allAssigns ((d :: ds) ++ s₂) = [] := by
              simp only [List.cons_append, allAssigns, hd]
            rw [h2] at h
            exact absurd h (by simp)
          · rintro ⟨a₁, ha₁, _, _, _⟩
            have h2 : allAssigns (d :: ds) = [] := by
              simp only [allAssigns, hd]
            rw [h2] at ha₁
            exact absurd ha₁ (by simp)
      | cons v vs =>
          constructor
          · intro h
            obtain ⟨w, hw, a', ha', rfl⟩ :=
              (mem_allAssigns_cons hd (ds ++ s₂) a).mp h
            obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (ih a').mp ha'
            refine ⟨w :: b₁, ?_, b₂, hb₂, rfl⟩
            rw [mem_allAssigns_cons hd]
            exact ⟨w, hw, b₁, hb₁, rfl⟩
          · rintro ⟨a₁, ha₁, a₂, ha₂, rfl⟩
            obtain ⟨w, hw, b₁, hb₁, rfl⟩ :=
              (mem_allAssigns_cons hd ds a₁).mp ha₁
            have hjoin : b₁ ++ a₂ ∈ allAssigns (ds ++ s₂) :=
              (ih _).mpr ⟨b₁, hb₁, a₂, ha₂, rfl⟩
            exact (mem_allAssigns_cons hd (ds ++ s₂) _).mpr
              ⟨w, hw, _, hjoin, rfl⟩

/-- The legacy source-slot form of the append split. -/
theorem allAssigns_append (a : List Value) (s₁ s₂ : List (List Value)) :
    a ∈ allAssigns (s₁ ++ s₂) ↔
      ∃ a₁ ∈ allAssigns s₁, ∃ a₂ ∈ allAssigns s₂, a = a₁ ++ a₂ :=
  allAssigns_append_of_elems a s₁ s₂

/-- Membership in `allAssigns` from one-value-per-domain plus pointwise
domain membership, uniformly for list slots and compact `Dom` slots. -/
theorem mem_allAssigns_of_getElem? {α : Type} [DomainLike α] :
    ∀ (ds : List α) (tail : List Value),
      tail.length = ds.length →
      (∀ j v, tail[j]? = some v → v ∈ ds.getD j DomainLike.empty) →
      tail ∈ allAssigns ds := by
  intro ds
  induction ds with
  | nil =>
      intro tail hlen _
      cases tail with
      | nil => simp [allAssigns]
      | cons w ws => simp at hlen
  | cons d rest ih =>
      intro tail hlen hmem
      cases hd : DomainElems.elems d with
      | nil =>
          cases tail with
          | nil => simp at hlen
          | cons w ws =>
              have hw : w ∈ d := hmem 0 w (by simp)
              rw [DomainLike.mem_iff, hd] at hw
              exact absurd hw (by simp)
      | cons v vs =>
          cases tail with
          | nil => simp at hlen
          | cons w ws =>
              rw [mem_allAssigns_cons hd]
              refine ⟨w, ?_, ws, ih ws (by simpa using hlen) ?_, rfl⟩
              · have hw : w ∈ d := hmem 0 w (by simp)
                rwa [DomainLike.mem_iff, hd] at hw
              · intro j v' hv
                have := hmem (j + 1) v' (by simpa using hv)
                simpa [List.getD_cons_succ] using this

end LeanFzn.Solver.Core
