import LeanFzn.Solver.Core.Enumerate
import Lean

namespace LeanFzn.Solver.Reference
open LeanFzn.Solver.Core LeanFzn.Semantics

/-- The exhaustive reference search.  `leaf` is the leaf predicate on
    complete assignments; `slots` the remaining (first component) and
    `acc` the already-fixed values, in slot order.  Returns the first
    complete assignment (an extension of `acc`) that satisfies `leaf`,
    or `none` when every complete assignment fails. -/
def search (leaf : List Value → Bool) :
    List (List Value) → List Value → Option (List Value)
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

/-- **Soundness of a successful search**: the returned assignment is a
    complete assignment of the slots and passes the leaf predicate. -/
theorem search_some (leaf : List Value → Bool) :
    ∀ (slots : List (List Value)) (acc : List Value) (r : List Value),
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
theorem search_none (leaf : List Value → Bool) :
    ∀ (slots : List (List Value)) (acc : List Value),
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
          have hgen : ∀ (xs : List Value) (b : Value),
              b ∈ xs → ∀ (r : List (List Value)) (t : List Value),
                t ∈ allAssigns r → b :: t ∈ allAssigns (xs :: r) := by
            intro xs b hmem r t ht
            induction xs generalizing t with
            | nil => exact absurd hmem (by simp)
            | cons u us ih =>
                by_cases hmemu : u = b
                · subst hmemu
                  simp only [allAssigns, DomainElems.elems_list, List.mem_flatMap]
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


end LeanFzn.Solver.Reference
