/- probe -/ 
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

/-! ## The go-level fragment discipline -/

/-- The trail-fold keeps the ≤ 1-per-slot discipline when the problem's
    domains have it: each fold step is a domOfLit narrowing, and the
    per-slot lemma closes each one. -/
theorem fold_domOfLt_getD_le_one :
    ∀ (doms : List (List Value)) (tr : List TrailEntry),
    (∀ s : Nat, (doms.getD s []).length ≤ 1) →
    (∀ s : Nat, ((tr.foldl (fun acc e => domOfLit acc e.literal)
      doms).getD s []).length ≤ 1) := by
  intro doms tr
  induction tr generalizing doms with
  | nil => intro hall; exact hall
  | cons e rest ih =>
      intro hall
      rw [List.foldl_cons]
      exact ih (domOfLit doms e.literal)
        (domOfLt_getD_le_one doms e.literal hall)

/-- The trail-fold identity behind DomFold: a state satisfying DomFold
    inherits the problem's per-slot discipline as the fold's. -/
theorem domFold_le_one {problem : Problem Constraint Objective}
    {st : State} (hf : DomFold problem st)
    (hfrag : ∀ s : Nat, (problem.domains.getD s []).length ≤ 1) :
    ∀ s : Nat, (st.domains.getD s []).length ≤ 1 := by
  intro s
  rw [hf]
  exact fold_domOfLt_getD_le_one problem.domains st.trail hfrag s

/-! ## The ≤ 1 discipline at the fragment -/

/-- getD splits: in range it is the member, out of range the default. -/
theorem getD_split {L : List (List Value)} (s : Nat) :
    L.getD s [] = (if h : s < L.length then L[s] else []) := by
  simp only [List.getD]
  split
  · rename_i h
    rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-- The fragment's problem slot discipline: every getD slot has length
    ≤ 1 (in range a singleton member; out of range the empty default) -/
theorem problem_fragment_le_one {problem : Problem Constraint Objective}
    (hfrag : PropFragment problem) :
    ∀ s : Nat, (problem.domains.getD s []).length ≤ 1 := by
  intro s
  rw [getD_split]
  split
  · rename_i h
    have hd : problem.domains[s].length = 1 :=
      hfrag problem.domains[s] (List.getElem_mem h)
    rw [hd]
    exact Nat.le_refl 1
  · simp

/-- The post-propagation state's discipline inside the fragment: the
    entry satisfies DomFold, so the propagateLoop-from-entry state has
    the ≤1 discipline via propagateLoop_le_one. -/
theorem fragment_entry_le_one {problem : Problem Constraint Objective}
    {props : List Propagator} {st : State}
    (hf : DomFold problem st)
    (hfrag : PropFragment problem) :
    ∀ s : Nat, (List.getD (propagateLoop (engineFuel st) props st).domains
      s []).length ≤ 1 :=
  fun s => propagateLoop_le_one (props := props) (engineFuel st) st
    (domFold_le_one hf (problem_fragment_le_one hfrag)) s

/-! ## The decision-free fragment theorem -/

/-- THE DECISION-FREE FRAGMENT THEOREM: at a level-0, slot-disciplined
    entry, `go` NEVER decides and NEVER recurses — every `.unsat`
    outcome arises at THIS state directly, in one of the two
    root-terminal shapes. The three recursion arms are impossible:
    conflicts above 0 and the level->0 retreat need a positive
    post-propagation level (contradicting level preservation from the
    entry's 0), and the decision arm needs `decideLiteral st1 = some l`
    (contradicting the bisection-free discipline at the post state).
    Hence the entry IS the generating state UnsatRun must exhibit. -/
theorem go_fragment_no_decide {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      st.decisionLevel = 0 →
      (∀ s : Nat, (st.domains.getD s []).length ≤ 1) →
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ((propagateLoop (engineFuel st) props st).conflict.isSome = true
          ∨
        ((propagateLoop (engineFuel st) props st).conflict = none ∧
          allSingleton (propagateLoop (engineFuel st) props st) = true ∧
          ∃ a, singletonAssignment (propagateLoop (engineFuel st) props st)
            = some a ∧
            ¬ (fitsB problem a &&
                problem.constraints.all (fun c => constraintHoldsB c a)))) := by
  intro fuel
  cases fuel with
  | zero => intro st hlev hdisc h; simp only [lcgSearch.go] at h; cases h
  | succ fuel =>
      intro st hlev hdisc h
      simp only [lcgSearch.go] at h
      -- the discipline at the post-propagation state
      have hdisc1 : ∀ s : Nat, (List.getD
          (propagateLoop (32 + 8 * st.domains.length + 4 * st.trail.length)
            props st).domains s []).length ≤ 1 :=
        fun s => propagateLoop_le_one
          (32 + 8 * st.domains.length + 4 * st.trail.length) st hdisc s
      -- the level stays 0 through propagation
      have hlev1 : (propagateLoop (32 + 8 * st.domains.length
          + 4 * st.trail.length) props st).decisionLevel = 0 := by
        rw [propagateLoop_decisionLevel props
          (32 + 8 * st.domains.length + 4 * st.trail.length) st]
        exact hlev
      split at h
      · -- conflict at level 0: TERMINAL, the conflict arm
        next w hw hlev0 =>
          exact Or.inl (by simp only [Option.isSome_iff_exists]; exact ⟨w, hw⟩)
      · -- conflict above 0: IMPOSSIBLE (the level stays 0)
        exfalso
        trace_state
        sorry
      · -- no conflict: leaf or decision
        next hnone =>
        split at h
        · next hsingle =>
          split at h
          · split at h
            · cases h
            · split at h
              · next a0 hassign hfail hlev0 =>
                  exact Or.inr ⟨hnone, hsingle, a0, hassign, hfail⟩
              · -- retreat above 0: IMPOSSIBLE
                exfalso
                sorry
          · cases h
        · split at h
          · cases h
          · -- decision arm: IMPOSSIBLE (no bisection at disciplined state)
            next l hl =>
              exfalso
              sorry

end LeanFzn.Solver.LCG

