import Lean

/-! Finite Cartesian-product assignment semantics and membership lemmas.
Shared by compiler proofs, propagation and both search strategies. -/

namespace LeanFzn.Solver.Core
/-- **The specification**: every complete assignment of the slots —
    one value per slot, in slot order.  A slot with an empty domain
    contributes no assignments. -/
def allAssigns {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | [] :: _ => []
  | (v :: vs) :: rest =>
      (allAssigns rest).flatMap (fun a => (v :: vs).map (fun w => w :: a))

/-! ## Basic facts about `allAssigns` -/

/-- Single-slot assignments of a non-empty domain. -/
theorem mem_allAssigns_singleton {α : Type} (v : α) (vs : List α)
    (rest : List (List α)) (a : List α) :
    a ∈ allAssigns ((v :: vs) :: rest) ↔
      ∃ w ∈ (v :: vs), ∃ a' ∈ allAssigns rest, a = w :: a' := by
  simp only [allAssigns, List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨a', ha', w, hw, heq⟩ => ⟨w, hw, a', ha', heq.symm⟩,
    fun ⟨w, hw, a', ha', heq⟩ => ⟨a', ha', w, hw, heq.symm⟩⟩

/-- Extending a domain cannot remove assignments: `allAssigns` is
    monotone in the first slot's domain. -/
theorem allAssigns_subset_cons {α : Type} (v : α) (vs : List α)
    (rest : List (List α)) (a : List α) :
    a ∈ allAssigns (vs :: rest) → a ∈ allAssigns ((v :: vs) :: rest) := by
  cases vs with
  | nil => simp [allAssigns]
  | cons w ws =>
      simp only [allAssigns, List.mem_flatMap, List.mem_map] at *
      rintro ⟨a', ha', w', hw', rfl⟩
      exact ⟨a', ha', w', List.mem_cons_of_mem _ hw', rfl⟩

/-- Splitting the slots splits the assignments: an assignment of
    `s₁ ++ s₂` is an assignment of `s₁` followed by one of `s₂`. -/
theorem allAssigns_append {α : Type} (a : List α) (s₁ s₂ : List (List α)) :
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
      cases d with
      | nil =>
          constructor
          · intro h
            have h2 : allAssigns (([] : List α) :: ds ++ s₂) = [] := rfl
            rw [h2] at h
            exact absurd h (by simp)
          · rintro ⟨a₁, ha₁, _, _, _⟩
            have h2 : allAssigns (([] : List α) :: ds) = [] := rfl
            rw [h2] at ha₁
            exact absurd ha₁ (by simp)
      | cons v vs =>
          constructor
          · intro h
            obtain ⟨w, hw, a', ha', rfl⟩ :=
              (mem_allAssigns_singleton v vs (ds ++ s₂) a).mp h
            obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (ih a').mp ha'
            refine ⟨w :: b₁, ?_, b₂, hb₂, rfl⟩
            rw [mem_allAssigns_singleton]
            exact ⟨w, hw, b₁, hb₁, rfl⟩
          · rintro ⟨a₁, ha₁, a₂, ha₂, rfl⟩
            obtain ⟨w, hw, b₁, hb₁, rfl⟩ :=
              (mem_allAssigns_singleton v vs ds a₁).mp ha₁
            have hjoin : b₁ ++ a₂ ∈ allAssigns (ds ++ s₂) :=
              (ih _).mpr ⟨b₁, hb₁, a₂, ha₂, rfl⟩
            exact (mem_allAssigns_singleton v vs (ds ++ s₂) _).mpr
              ⟨w, hw, _, hjoin, rfl⟩


end LeanFzn.Solver.Core
