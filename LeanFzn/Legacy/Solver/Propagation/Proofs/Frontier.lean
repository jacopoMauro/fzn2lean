/-
Purpose: prove pending-branch coverage, SAT/UNSAT soundness and sufficient fuel.
Dependencies: LeanFzn.Solver.UIP.Frontier is the driver; LeanFzn.Solver.Core.Enumerate specifies finite assignments.
DAG: Frontier + Search -> Proofs.Frontier -> Proofs.Search (public contracts).
-/
import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Invariants
import LeanFzn.Solver.Propagation.FrontierSemantics
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

theorem frontier_sat_leaf (leaf : Assignment → Bool) (fuel : Nat)
    (pending : List PrefixFrame) (a : Assignment)
    (h : frontierSearch leaf fuel pending = .sat a) : leaf a = true := by
  induction fuel generalizing pending with
  | zero => cases pending <;> simp [frontierSearch] at h
  | succ fuel ih =>
      cases pending with
      | nil => simp [frontierSearch] at h
      | cons f pending =>
          rcases f with ⟨slots, chosen⟩
          cases slots with
          | nil =>
              simp only [frontierSearch] at h
              split at h
              · cases h; assumption
              · exact ih pending h
          | cons d rest =>
              cases hd : d.enum with
              | nil =>
                  simp only [frontierSearch, hd] at h
                  exact ih pending h
              | cons v vs =>
                  simp only [frontierSearch, hd] at h
                  exact ih _ h

theorem frontier_unsat_excludes (leaf : Assignment → Bool) (fuel : Nat)
    (pending : List PrefixFrame)
    (h : frontierSearch leaf fuel pending = .unsat) :
    ∀ a, PrefixFrontierCovers pending a → leaf a = false := by
  induction fuel generalizing pending with
  | zero =>
      cases pending with
      | nil => intro a hc; obtain ⟨f,hf,_⟩ := hc; cases hf
      | cons f rest => simp [frontierSearch] at h
  | succ fuel ih =>
      cases pending with
      | nil => intro a hc; obtain ⟨f,hf,_⟩ := hc; cases hf
      | cons f pending =>
          rcases f with ⟨slots,chosen⟩
          cases slots with
          | nil =>
              simp only [frontierSearch] at h
              split at h
              · cases h
              · rename_i hleaf
                intro a hc
                obtain ⟨f, hf, ht⟩ := hc
                rcases List.mem_cons.mp hf with rfl | hf
                · obtain ⟨tail, ht, rfl⟩ := ht
                  have heq : tail = [] := List.mem_singleton.mp ht
                  subst tail
                  simpa using hleaf
                · exact ih pending h a ⟨f,hf,ht⟩
          | cons d rest =>
              cases hd : d.enum with
              | nil =>
                  simp only [frontierSearch, hd] at h
                  intro a hc
                  obtain ⟨f,hf,ht⟩ := hc
                  rcases List.mem_cons.mp hf with rfl | hf
                  · obtain ⟨tail, ht, _⟩ := ht
                    rw [allAssigns_cons_eq_nil (by rw [domElems_eq_enum, hd])] at ht
                    cases ht
                  · exact ih pending h a ⟨f,hf,ht⟩
              | cons v vs =>
                  simp only [frontierSearch, hd] at h
                  intro a hc
                  apply ih _ h a
                  obtain ⟨f,hf,ht⟩ := hc
                  rcases List.mem_cons.mp hf with rfl | hf
                  · rcases (prefix_covers_split_list hd rest chosen a).mp ht with ht | ht
                    · exact ⟨_, List.mem_cons_self, ht⟩
                    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ht⟩
                  · exact ⟨f,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf),ht⟩

/-! ## The fuel-free traversal (`frontierSolve`)

The total, kernel-checked chronological traversal. Its verdicts carry
the same coverage/soundness contracts as the bounded reference, with
no budget: SAT passes the leaf predicate and comes from a represented
pending assignment; UNSAT excludes every represented assignment
satisfying the leaf; a represented satisfying assignment implies SAT. -/

/-- One definitional step of `frontierSolve` at an exhausted domain: the
    named dependent match does not reduce by rewriting alone, so the
    empty-enumeration branch is exposed explicitly. -/
private theorem frontierSolve_cons_nil_eq {leaf : Assignment → Bool}
    {chosen : Assignment} {rest : List PrefixFrame} {d : Domain}
    {rest₁ : List Domain} (hd : d.enum = []) :
    frontierSolve leaf ((d :: rest₁, chosen) :: rest) = frontierSolve leaf rest := by
  rw [frontierSolve.eq_3]
  split
  · rfl
  · rename_i v vs heq
    rw [hd] at heq
    cases heq

/-- One definitional step of `frontierSolve` at a live domain: both
    branch terms are exposed explicitly. -/
private theorem frontierSolve_cons_cons_eq {leaf : Assignment → Bool}
    {chosen : Assignment} {rest : List PrefixFrame} {d : Domain}
    {rest₁ : List Domain} {v : Value} {vs : List Value}
    (hd : d.enum = v :: vs) :
    frontierSolve leaf ((d :: rest₁, chosen) :: rest) =
      frontierSolve leaf ((rest₁, chosen ++ [v]) ::
        (Dom.ofList vs :: rest₁, chosen) :: rest) := by
  rw [frontierSolve.eq_3]
  split
  · rename_i heq
    rw [hd] at heq
    cases heq
  · rename_i v' vs' heq
    rw [hd] at heq
    cases heq
    rfl

/-- SAT soundness: a witness returned by the fuel-free traversal
    passes the leaf predicate. -/
theorem frontierSolve_sat_leaf (leaf : Assignment → Bool)
    (pending : List PrefixFrame) (a : Assignment)
    (h : frontierSolve leaf pending = .sat a) : leaf a = true := by
  induction pending using frontierSolve.induct (leaf := leaf) with
  | case1 => simp [frontierSolve] at h
  | case2 chosen rest hleaf =>
      simp only [frontierSolve, if_pos hleaf] at h
      cases h; assumption
  | case3 chosen rest hleaf ih =>
      simp only [frontierSolve, if_neg hleaf] at h
      exact ih h
  | case4 chosen rest d rest₁ hd ih =>
      rw [frontierSolve_cons_nil_eq hd] at h
      exact ih h
  | case5 chosen rest d rest₁ v vs hd ih =>
      rw [frontierSolve_cons_cons_eq hd] at h
      exact ih h

/-- SAT soundness: a witness returned by the fuel-free traversal is
    represented by the pending stack it was returned from. -/
theorem frontierSolve_sat_mem (leaf : Assignment → Bool)
    (pending : List PrefixFrame) (a : Assignment)
    (h : frontierSolve leaf pending = .sat a) : PrefixFrontierCovers pending a := by
  induction pending using frontierSolve.induct (leaf := leaf) with
  | case1 => simp [frontierSolve] at h
  | case2 chosen rest hleaf =>
      simp only [frontierSolve, if_pos hleaf] at h
      cases h
      exact ⟨([], a), List.mem_cons_self, [],
        (List.mem_singleton_self ([] : List Value)), by simp⟩
  | case3 chosen rest hleaf ih =>
      simp only [frontierSolve, if_neg hleaf] at h
      obtain ⟨f, hf, hcov⟩ := ih h
      exact ⟨f, List.mem_cons_of_mem _ hf, hcov⟩
  | case4 chosen rest d rest₁ hd ih =>
      rw [frontierSolve_cons_nil_eq hd] at h
      obtain ⟨f, hf, hcov⟩ := ih h
      exact ⟨f, List.mem_cons_of_mem _ hf, hcov⟩
  | case5 chosen rest d rest₁ v vs hd ih =>
      rw [frontierSolve_cons_cons_eq hd] at h
      obtain ⟨f, hf, hcov⟩ := ih h
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨_, List.mem_cons_self,
          (prefix_covers_split_list hd rest₁ chosen a).mpr (Or.inl hcov)⟩
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨_, List.mem_cons_self,
            (prefix_covers_split_list hd rest₁ chosen a).mpr (Or.inr hcov)⟩
        · exact ⟨f, List.mem_cons_of_mem _ hf, hcov⟩

/-- UNSAT soundness: an `unsat` verdict excludes every represented
    assignment satisfying the leaf predicate. -/
theorem frontierSolve_unsat_excludes (leaf : Assignment → Bool)
    (pending : List PrefixFrame)
    (h : frontierSolve leaf pending = .unsat) :
    ∀ a, PrefixFrontierCovers pending a → leaf a = false := by
  induction pending using frontierSolve.induct (leaf := leaf) with
  | case1 => intro a hcov; obtain ⟨f, hf, _⟩ := hcov; cases hf
  | case2 chosen rest hleaf =>
      simp only [frontierSolve, if_pos hleaf] at h
      cases h
  | case3 chosen rest hleaf ih =>
      simp only [frontierSolve, if_neg hleaf] at h
      intro a hcov
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨tail, htail, rfl⟩ := ht
        have heq : tail = [] := List.mem_singleton.mp htail
        subst heq
        simpa using hleaf
      · exact ih h a ⟨f, hf, ht⟩
  | case4 chosen rest d rest₁ hd ih =>
      rw [frontierSolve_cons_nil_eq hd] at h
      intro a hcov
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨tail, ht, _⟩ := ht
        rw [allAssigns_cons_eq_nil (by rw [domElems_eq_enum, hd])] at ht
        cases ht
      · exact ih h a ⟨f, hf, ht⟩
  | case5 chosen rest d rest₁ v vs hd ih =>
      rw [frontierSolve_cons_cons_eq hd] at h
      intro a hcov
      apply ih h a
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases (prefix_covers_split_list hd rest₁ chosen a).mp ht with ht | ht
        · exact ⟨_, List.mem_cons_self, ht⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ht⟩
      · exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), ht⟩

/-- Completeness: if any assignment represented by the pending stack
    satisfies the leaf predicate, the fuel-free traversal returns SAT
    (with a possibly different valid witness). -/
theorem frontierSolve_complete (leaf : Assignment → Bool)
    (pending : List PrefixFrame)
    (hsat : ∃ a, PrefixFrontierCovers pending a ∧ leaf a = true) :
    ∃ a, frontierSolve leaf pending = .sat a := by
  induction pending using frontierSolve.induct (leaf := leaf) with
  | case1 => exact absurd hsat (by rintro ⟨a, ⟨f, hf, _⟩, _⟩; cases hf)
  | case2 chosen rest hleaf => exact ⟨chosen, by simp [frontierSolve, hleaf]⟩
  | case3 chosen rest hleaf ih =>
      simp only [frontierSolve, if_neg hleaf]
      obtain ⟨a, hcov, haleaf⟩ := hsat
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨tail, htail, rfl⟩ := ht
        have heq : tail = [] := List.mem_singleton.mp htail
        subst heq
        simp only [List.append_nil] at haleaf
        exact absurd haleaf hleaf
      · exact ih ⟨a, ⟨f, hf, ht⟩, haleaf⟩
  | case4 chosen rest d rest₁ hd ih =>
      rw [frontierSolve_cons_nil_eq hd]
      obtain ⟨a, hcov, hleaf⟩ := hsat
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · obtain ⟨tail, htail, _⟩ := ht
        rw [allAssigns_cons_eq_nil (by rw [domElems_eq_enum, hd])] at htail
        cases htail
      · exact ih ⟨a, ⟨f, hf, ht⟩, hleaf⟩
  | case5 chosen rest d rest₁ v vs hd ih =>
      rw [frontierSolve_cons_cons_eq hd]
      obtain ⟨a, hcov, hleaf⟩ := hsat
      obtain ⟨f, hf, ht⟩ := hcov
      rcases List.mem_cons.mp hf with rfl | hf
      · rcases (prefix_covers_split_list hd rest₁ chosen a).mp ht with ht | ht
        · exact ih ⟨a, ⟨_, List.mem_cons_self, ht⟩, hleaf⟩
        · exact ih ⟨a, ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ht⟩, hleaf⟩
      · exact ih ⟨a, ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), ht⟩, hleaf⟩

theorem frontier_sufficient (leaf : Assignment → Bool) (fuel : Nat)
    (pending : List PrefixFrame) (hbudget : frontierCost pending ≤ fuel) :
    frontierSearch leaf fuel pending ≠ .unknown := by
  induction fuel generalizing pending with
  | zero =>
      cases pending with
      | nil => simp [frontierSearch]
      | cons f pending =>
          have hp := branchCost_pos f.1
          simp only [frontierCost, List.map_cons, List.sum_cons] at hbudget
          omega
  | succ fuel ih =>
      cases pending with
      | nil => simp [frontierSearch]
      | cons f pending =>
          rcases f with ⟨slots,chosen⟩
          cases slots with
          | nil =>
              simp only [frontierSearch]
              split
              · simp
              · apply ih
                simp [frontierCost, branchCost] at hbudget ⊢
                omega
          | cons d rest =>
              cases hd : d.enum with
              | nil =>
                  simp only [frontierSearch, hd]
                  apply ih
                  have hlen : d.length = 0 := by
                    rw [Dom.length_eq_enum, hd]
                    rfl
                  simp [frontierCost, branchCost, hlen] at hbudget ⊢
                  omega
              | cons v vs =>
                  simp only [frontierSearch, hd]
                  apply ih
                  have hlen : d.length = vs.length + 1 := by
                    rw [Dom.length_eq_enum, hd]
                    simp
                  simp [frontierCost, branchCost, Nat.succ_mul, hlen] at hbudget ⊢
                  omega
/-- Domain membership places every semantic solution in the initial frontier. -/
theorem frontier_fits_mem_allAssigns : ∀ (doms : List Domain)
    (a : List Value), Assignment.Fits doms a →
    a ∈ allAssigns doms := by
  intro doms
  induction doms with
  | nil =>
      intro a h
      obtain ⟨hlen, _⟩ := h
      cases a with
      | nil => exact List.mem_singleton_self []
      | cons x xs =>
          have : (x :: xs).length = [].length := hlen
          simp at this
  | cons d rest ih =>
      intro a h
      obtain ⟨hlen, hmem⟩ := h
      cases ha : a with
      | nil =>
          rw [ha] at hlen
          simp at hlen
      | cons x xs =>
          have hxmem : x ∈ d := by
            have := hmem 0 x (by rw [ha]; rfl)
            exact this
          have hxenum : x ∈ d.enum := by
            rw [← domElems_eq_enum, ← DomainLike.mem_iff]
            exact hxmem
          have hrest : Assignment.Fits rest xs := by
            refine ⟨?_, ?_⟩
            · rw [ha] at hlen
              simp only [List.length_cons] at hlen
              omega
            · intro slot value hval
              have hread : a[slot + 1]? = some value := by
                rw [ha]
                exact hval
              have hval2 := hmem (slot + 1) value hread
              rw [show (d :: rest).getD (slot + 1) DomainLike.empty =
                rest.getD slot DomainLike.empty from rfl] at hval2
              exact hval2
          have hrec : xs ∈ allAssigns rest := ih xs hrest
          cases hd : d.enum with
          | nil =>
              rw [hd] at hxenum
              cases hxenum
          | cons v vs =>
              have heq : x ∈ (v :: vs) := by rwa [hd] at hxenum
              have hs : DomainElems.elems d = v :: vs := by
                rw [domElems_eq_enum, hd]
              rw [mem_allAssigns_cons hs rest (x :: xs)]
              exact ⟨x, heq, xs, hrec, rfl⟩

/-- Soundness of a chronological SAT verdict, with the original leaf contract. -/
theorem chronological_sat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    (hagrees : ∀ c a, constraintHoldsB c a = true ↔ constraintHolds c a)
    {a : Assignment}
    (h : chronologicalSearch problem constraintHoldsB = .sat a) :
    ProblemSolution problem constraintHolds a := by
  unfold chronologicalSearch at h
  cases hsolve : frontierSolve (chronologicalLeaf problem constraintHoldsB)
      [(problem.domains, [])] with
  | sat b =>
      rw [hsolve] at h
      cases h
      have hl := frontierSolve_sat_leaf _ _ a hsolve
      -- the leaf contract directly carries fit + every constraint
      rw [chronologicalLeaf, Bool.and_eq_true] at hl
      obtain ⟨hfitB, hcons⟩ := hl
      rw [Bool.and_eq_true] at hcons
      exact ⟨fitsB_iff.mp hfitB, fun c hcmem =>
        (hagrees c a).mp (List.all_eq_true.mp hcons.1 c hcmem)⟩
  | unsat => rw [hsolve] at h; simp at h

/-- Emptying the frontier excludes every solution, without any explanation
    or propagator-safety premise. The fuel-free traversal empties the
    frontier exactly when it returns `unsat`. -/
theorem chronological_unsat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    (hagrees : ∀ c a, constraintHoldsB c a = true ↔ constraintHolds c a)
    (hdb : ∀ c ∈ problem.clauses, ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l ∈ c, l.eval a = some true)
    (h : chronologicalSearch problem constraintHoldsB = .unsat) :
    ¬ ∃ a, ProblemSolution problem constraintHolds a := by
  rintro ⟨a, hf, hc⟩
  unfold chronologicalSearch at h
  cases hsolve : frontierSolve (chronologicalLeaf problem constraintHoldsB)
      [(problem.domains, [])] with
  | sat b => rw [hsolve] at h; simp at h
  | unsat =>
      rw [hsolve] at h
      cases h
      have hfalse := frontierSolve_unsat_excludes _ _ (by rw [hsolve]) a
        ⟨(problem.domains, []), List.mem_singleton_self _,
          a, frontier_fits_mem_allAssigns _ _ hf, by simp⟩
      have htrue : (chronologicalLeaf problem constraintHoldsB a) = true := by
        rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨fitsB_iff.mpr hf, ?_, ?_⟩
        · apply List.all_eq_true.mpr
          intro c hcmem
          exact (hagrees c a).mpr (hc c hcmem)
        · apply List.all_eq_true.mpr
          intro c hcmem
          obtain ⟨l, hl, he⟩ := hdb c hcmem a ⟨hf,hc⟩
          exact List.any_eq_true.mpr ⟨l, hl, decide_eq_true he⟩
      rw [htrue] at hfalse
      cases hfalse

/-- The fuel-free driver always returns a verdict: never `unknown`.
    This is the total-verdict theorem for the internal entry point. -/
theorem chronological_total
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool) :
    chronologicalSearch problem constraintHoldsB ≠ .unknown := by
  unfold chronologicalSearch
  cases frontierSolve (chronologicalLeaf problem constraintHoldsB)
    [(problem.domains, [])] <;> simp

/-- The historical bounded driver's budget theorem, retained for the
    diagnostic reference only. -/
theorem chronological_sufficient
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (fuel : Nat) (h : branchCost problem.domains ≤ fuel) :
    chronologicalSearchBounded fuel problem constraintHoldsB ≠ .unknown := by
  unfold chronologicalSearchBounded
  apply frontier_sufficient
  simpa [frontierCost] using h
end LeanFzn.Solver.Propagation
