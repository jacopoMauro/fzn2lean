/- s29: the last two Phase 1 proofs. -/

import solver.LCG.Proofs.Search

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- The root-fact fold's invariant helper: stated over the FOLD
    RESULT directly to keep the syntax projection-free. -/
def RootFoldInv (problem : Problem Constraint Objective)
    (st : State) : Prop :=
  st.domains = problem.domains ∧
    st.domains = (List.foldl (fun acc e => domOfLit acc e.literal)
      problem.domains st.trail)

/-- THE TRAIL-OF-ROOT-FACTS FOLD IS THE PROBLEM'S DOMAINS: each root
    fact's domOfLit step is the identity on `problem.domains`, so any
    trail of root facts folds back to `problem.domains`. -/
theorem rootFact_trail_fold (problem : Problem Constraint Objective) :
    ∀ (tr : List TrailEntry),
    (∀ e ∈ tr, e.literal ∈ rootFacts problem.domains) →
    (List.foldl (fun acc e => domOfLit acc e.literal) problem.domains tr)
      = problem.domains := by
  intro tr
  induction tr with
  | nil => intro _; rfl
  | cons e rest ih =>
      intro hall
      -- the head's step is the identity; apply it FIRST so the IH's
      -- fold starts from problem.domains again
      have hid : domOfLit problem.domains e.literal = problem.domains :=
        domOfLit_rootFact_id (doms := problem.domains)
          (ds := problem.domains) (s := 0) (l := e.literal)
          (fun i => by
            show problem.domains.getD i [] =
              problem.domains.getD (0 + i) []
            rw [Nat.zero_add])
          (by
            show e.literal ∈ rootFacts problem.domains
            exact hall e (List.mem_cons_self))
      rw [List.foldl_cons, hid,
        ih (fun e2 he2 => hall e2 (List.mem_cons_of_mem _ he2))]

/-- Enqueue-folds never change the domains: `enqueue` only touches the
    trail and the skip arm returns the state unchanged. -/
theorem fold_enqueue_domains :
    ∀ (rs : List Literal) (st : State),
      (List.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st rs).domains
        = st.domains := by
  intro rs
  induction rs with
  | nil => intro st; rfl
  | cons l rest ih =>
      intro st
      rw [List.foldl_cons]
      cases hb : st.litOnTrail l with
      | true =>
          simp only [hb, if_true]
          exact ih st
      | false =>
          simp only [hb, Bool.false_eq_true, if_false]
          rw [ih (enqueue st l none)]
          rfl

/-- Every entry of an enqueue-fold's trail either was already on the
    accumulator's trail or carries one of the folded literals. -/
theorem fold_enqueue_trail_mem :
    ∀ (rs : List Literal) (st : State) (e : TrailEntry),
      e ∈ (List.foldl (fun st l =>
        if st.litOnTrail l then st else enqueue st l none) st rs).trail →
      e ∈ st.trail ∨ e.literal ∈ rs := by
  intro rs
  induction rs with
  | nil => intro st e he; exact Or.inl he
  | cons l rest ih =>
      intro st e he
      rw [List.foldl_cons] at he
      cases hb : st.litOnTrail l with
      | true =>
          simp only [hb, if_true] at he
          rcases ih st e he with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      | false =>
          simp only [hb, Bool.false_eq_true, if_false] at he
          -- the rest-fold starts from (enqueue st l none), whose trail
          -- is st.trail ++ [fresh]; split the IH's membership on it
          have heq : (enqueue st l none).trail
              = st.trail ++ [TrailEntry.mk l st.decisionLevel none] := rfl
          rcases ih (enqueue st l none) e he with h | h
          · rw [heq, List.mem_append] at h
            rcases h with h | h
            · exact Or.inl h
            · rw [List.mem_singleton] at h
              cases h
              exact Or.inr (List.mem_cons_self)
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- THE INITIAL FOLD: the initial state's trail carries only root
    facts, so the trail-fold is the problem's domains. -/
theorem initial_domFold (problem : Problem Constraint Objective) :
    DomFold problem (initialStateWithRoots problem) := by
  unfold DomFold initialStateWithRoots initialState
  rw [fold_enqueue_domains (rootFacts problem.domains)
    { domains := problem.domains, trail := [], decisionLevel := 0,
      clauses := problem.clauses, learned := [], queue := [],
      conflict := none }]
  -- ⊢ problem.domains = fold over the enqueue-fold's trail
  symm
  apply rootFact_trail_fold problem
  intro e he
  rcases fold_enqueue_trail_mem (rootFacts problem.domains)
    { domains := problem.domains, trail := [], decisionLevel := 0,
      clauses := problem.clauses, learned := [], queue := [],
      conflict := none } e he with h | h
  · exact absurd h (by simp)
  · exact h

#print axioms LeanFzn.Solver.LCG.initial_domFold
#print axioms LeanFzn.Solver.LCG.rootFact_trail_fold

end LeanFzn.Solver.LCG
