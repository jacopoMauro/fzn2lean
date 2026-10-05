import Lean

/-!
# Exhaustive reference search (PLAN.md 6.1, 6.2)

The smallest complete reference solver needs an exhaustive search:
branch on the values of one variable at a time, recurse, and test the
leaf predicate on complete assignments.  This module is *generic* —
it knows nothing about FlatZinc; the solver instantiates it with a
finite list of candidate values per search position.

## Design

* A search *state* is a list of *slots*, each slot a finite list of
  candidate values, plus an accumulator of already-fixed values.
* `search` processes the first slot: it fixes its first value and
  moves on to the remaining slots; when that fails, it retries the
  remaining values of the first slot.  A slot with an empty domain
  makes the whole subtree unsatisfiable (no total assignment exists
  below it).
* `allAssigns` is the declarative specification: the list of all
  total assignments picking one value per slot.  The two master
  theorems connect the executable search to it:

  - `search_some`: a returned assignment comes from `allAssigns` and
    passes the leaf predicate;
  - `search_none`: `none` means *every* assignment of `allAssigns`
    fails the leaf predicate.

  Together they make the search sound and complete for any leaf
  predicate, so later phases can swap in propagators (PLAN 6.3) as
  long as the leaf test stays the same.

* Termination (PLAN 6.1): the measure is the sum over slots of
  `(domain cardinality + 1)`; each recursive call strictly decreases
  it (moving on consumes a slot, retrying shrinks a domain).
-/

namespace LeanFzn.Solver

/-- The exhaustive reference search.  `leaf` is the leaf predicate on
    complete assignments; `slots` the remaining (first component) and
    `acc` the already-fixed values, in slot order.  Returns the first
    complete assignment (an extension of `acc`) that satisfies `leaf`,
    or `none` when every complete assignment fails. -/
def search {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → Option (List α)
  | [], acc => if leaf acc then some acc else none
  | [] :: _, _ => none
  | (v :: vs) :: rest, acc =>
      match search leaf rest (acc ++ [v]) with
      | some a => some a
      | none => search leaf (vs :: rest) acc
termination_by slots _ =>
  slots.foldr (fun vs acc => vs.length + 1 + acc) 0
decreasing_by
  all_goals
    simp only [List.foldr_cons, List.length_cons]
    omega

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

/-! ## The master theorems -/

/-- **Soundness of a successful search**: the returned assignment is a
    complete assignment of the slots and passes the leaf predicate. -/
theorem search_some {α : Type} (leaf : List α → Bool) :
    ∀ (slots : List (List α)) (acc : List α) (r : List α),
      search leaf slots acc = some r →
        ∃ a, a ∈ allAssigns slots ∧ r = acc ++ a ∧ leaf (acc ++ a) = true := by
  intro slots acc
  induction slots, acc using search.induct (leaf := leaf) with
  | case1 acc hleaf =>
      intro r h
      simp only [search, if_pos hleaf] at h
      have hra : r = acc := by simpa using h.symm
      subst hra
      refine ⟨[], by simp [allAssigns], ?_, ?_⟩
      · rw [List.append_nil]
      · simpa using hleaf
  | case2 acc hleaf =>
      intro r h
      simp only [search] at h
      rw [if_neg hleaf] at h
      exact absurd h (by simp)
  | case3 tail x =>
      intro r h
      exact absurd h (by simp [search])
  | case4 v vs rest acc a hs ih1 =>
      intro r h
      simp only [search] at h
      rw [hs] at h
      have hra : a = r := by simpa using h
      obtain ⟨a', ha', rfl, hleaf⟩ := ih1 a hs
      refine ⟨v :: a', ?_, ?_, ?_⟩
      · rw [mem_allAssigns_singleton]
        exact ⟨v, List.mem_cons_self, a', ha', rfl⟩
      · simpa [List.append_assoc, List.cons_append] using hra.symm
      · simpa [List.append_assoc, List.cons_append] using hleaf
  | case5 v vs rest acc hnone _ih1 ih2 =>
      intro r h
      simp only [search] at h
      rw [hnone] at h
      obtain ⟨a', ha', rfl, hleaf⟩ := ih2 r h
      exact ⟨a', allAssigns_subset_cons v vs rest a' ha', rfl, hleaf⟩

/-- **Soundness of an unsuccessful search**: `none` means every
    complete assignment of the slots fails the leaf predicate. -/
theorem search_none {α : Type} (leaf : List α → Bool) :
    ∀ (slots : List (List α)) (acc : List α),
      search leaf slots acc = none →
        ∀ a ∈ allAssigns slots, leaf (acc ++ a) = false := by
  intro slots acc
  induction slots, acc using search.induct (leaf := leaf) with
  | case1 acc hleaf =>
      intro h a ha
      have haNil : a = [] := by simpa [allAssigns] using ha
      subst haNil
      simp only [List.append_nil]
      simp only [search, if_pos hleaf] at h
      exact absurd h (by simp)
  | case2 acc hleaf =>
      intro h a ha
      have haNil : a = [] := by simpa [allAssigns] using ha
      subst haNil
      simp only [List.append_nil]
      simp only [search, if_neg hleaf] at h
      simpa using hleaf
  | case3 tail x =>
      intro _ a ha
      exact absurd ha (by simp [allAssigns])
  | case4 v vs rest acc a hs _ih1 =>
      intro h a ha
      simp only [search] at h
      rw [hs] at h
      exact absurd h (by simp)
  | case5 v vs rest acc hnone ih1 ih2 =>
      intro h a ha
      rw [mem_allAssigns_singleton] at ha
      obtain ⟨w, hw, a', ha', rfl⟩ := ha
      by_cases hw' : w = v
      · subst hw'
        have hleaf := ih1 hnone a' ha'
        simpa [List.append_assoc, List.cons_append] using hleaf
      · have hsearch : search leaf (vs :: rest) acc = none := by
          simp only [search, hnone] at h
          simpa using h
        have ha2 : w :: a' ∈ allAssigns (vs :: rest) := by
          have hwvs : w ∈ vs := by
            rcases List.mem_cons.mp hw with heq | hin
            · exact absurd heq hw'
            · exact hin
          have hgen : ∀ (xs : List α) (b : α),
              b ∈ xs → ∀ (r : List (List α)) (t : List α),
                t ∈ allAssigns r → b :: t ∈ allAssigns (xs :: r) := by
            intro xs b hmem r t ht
            induction xs generalizing t with
            | nil => exact absurd hmem (by simp)
            | cons u us ih =>
                by_cases hmemu : u = b
                · subst hmemu
                  rw [allAssigns, List.mem_flatMap]
                  exact ⟨t, ht, by
                    have := List.mem_map_of_mem
                      (a := u) (f := fun w => w :: t) (l := u :: us)
                      List.mem_cons_self
                    exact this⟩
                · have hbus : b ∈ us := by
                    rcases List.mem_cons.mp hmem with heq | hin
                    · exact absurd heq.symm hmemu
                    · exact hin
                  have hrec : b :: t ∈ allAssigns (us :: r) := ih hbus t ht
                  exact allAssigns_subset_cons u us r _ hrec
          exact hgen vs w hwvs rest a' ha'
        exact ih2 hsearch (w :: a') ha2

end LeanFzn.Solver
