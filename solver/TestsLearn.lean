import solver.Solver

/-!
# NoGood learning tests (PLAN.md 6.6, learning half)

Unit and integration tests for `solver/Learning.lean`:

* `Violated`/`violatedB` on matching and non-matching assignments
  (the declarative clause semantics and its executable twin);
* `EntailedOn` checks: an entailed NoGood leaves the composed leaf
  unchanged; the agreement theorem `nogoodSearch_agrees` instantiated
  on small examples (entailed NoGoods do not change outcomes);
* a NON-entailed NoGood prunes a leaf-passing assignment
  (`ngLeaf_prunes_of_violated`) — demonstrating why the entailment
  discipline matters;
* the subtree entailment theorem `failedSubtree_entailed` instantiated
  on a genuinely failed subtree;
* the learning loop `learnSearch` agreeing with the plain reference
  `search` on small models (SAT and UNSAT, several fuels), with fuel 0
  being the plain search;
* the master theorems re-verified by brute force on the actual
  outcomes;
* pruning observed with an instrumented leaf: a counting twin of the
  reference search (evaluates 9 leaves on the 3×3 UNSAT model) versus
  the NoGood-guarded leaf (which skips the model leaf exactly on the
  assignments matching an entailed learned NoGood — every assignment
  of the model, so the guarded search consults the model leaf zero
  times while returning the same `none` verdict).
-/

open LeanFzn LeanFzn.Solution LeanFzn.Solver LeanFzn.Check LeanFzn.Globals

private def vi (i : Int) : Value := .int i

/-- A mutable failure flag with a counted check helper (the style of
    `solver/Tests.lean`). -/
private structure TestState where
  passed : Nat
  failed : Nat

private def TestState.check (st : TestState) (name : String) (ok : Bool) :
    IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

/-- The leaf of the SAT model `x + y = 4` over two 1..3 slots. -/
private def leafCalls : List Value → Bool :=
  fun l => match l with
    | [Value.int a, Value.int b] => a + b == 4
    | _ => false

/-- The leaf of an UNSAT model (`x + y = 7` over two 1..3 slots). -/
private def leaf7 : List Value → Bool :=
  fun l => match l with
    | [Value.int a, Value.int b] => a + b == 7
    | _ => false

/-- The leaf of an UNSAT model (`x + y = 5` over two 1..3 slots). -/
private def leaf5 : List Value → Bool :=
  fun l => match l with
    | [Value.int a, Value.int b] => a + b == 5
    | _ => false

/-- The instrumented counting twin of the reference `search` (mirrors
    its structure exactly, threading a leaf-call count; test-only). -/
private def searchCount {α : Type} (leaf : List α → Bool) :
    List (List α) → List α → Nat × Option (List α)
  | [], acc => (1, if leaf acc then some acc else none)
  | [] :: _, _ => (0, none)
  | (v :: vs) :: rest, acc =>
      let (c1, r1) := searchCount leaf rest (acc ++ [v])
      match r1 with
      | some a => (c1, some a)
      | none =>
          let (c2, r2) := searchCount leaf (vs :: rest) acc
          (c1 + c2, r2)
termination_by slots _ => slotsMeasure slots
decreasing_by
  all_goals
    simp only [slotsMeasure, List.foldr_cons, List.length_cons]
    omega

/-- The NoGood-guarded leaf: consults the model leaf only when no
    learned NoGood fires (extensionally `ngLeaf`, but lazy in the
    model leaf — the instrument that makes pruning observable). -/
private def guardLeaf (leaf : List Value → Bool) (ngs : List NoGood)
    (asg : List Value) : Bool :=
  if (ngs.any (fun ng => ng.violatedB asg)) then false else leaf asg

/-- The two slot family 1..3 × 1..3. -/
private def slots93 : List (List Value) :=
  [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]]

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Violated / violatedB unit tests

  -- a matching assignment violates the NoGood
  st ← st.check "violated: matching assignment"
    (NoGood.violatedB [(0, vi 1), (1, vi 3)] [vi 1, vi 3] == true)
  -- a non-matching assignment does not (slot 1 differs)
  st ← st.check "violated: non-matching (slot differs)"
    (NoGood.violatedB [(0, vi 1), (1, vi 3)] [vi 1, vi 4] == false)
  -- a too-short assignment does not (slot 1 out of range)
  st ← st.check "violated: non-matching (too short)"
    (NoGood.violatedB [(0, vi 1), (1, vi 3)] [vi 1] == false)
  -- the empty NoGood is violated by every assignment
  st ← st.check "violated: empty NoGood"
    (NoGood.violatedB [] [vi 1, vi 3] == true)
  -- mixed slot values: a bool value never matches an int pair
  st ← st.check "violated: type-mismatched pair"
    (NoGood.violatedB [(0, vi 1)] [Value.bool true] == false)
  -- the Prop twin agrees (violatedB_iff, on a matching case)
  st ← st.check "violatedB_iff: matching case decides"
    (NoGood.violatedB [(0, vi 1)] [vi 1] == true)
  -- pairsOf builds the decision trail
  st ← st.check "pairsOf: decision trail of a prefix"
    (pairsOf [vi 1, vi 3] == [(0, vi 1), (1, vi 3)])
  st ← st.check "pairsOf: empty prefix"
    (pairsOf [] == ([] : NoGood))

  -- ## EntailedOn and the composed leaf

  -- leaf: x + y = 4 over 1..3 × 1..3.  The NoGood [(0,2),(1,9)] is
  -- entailed (slot 1 never holds 9): the composed leaf equals the
  -- leaf on every complete assignment.
  let ngent : NoGood := [(0, vi 2), (1, vi 9)]
  have hent : NoGood.EntailedOn [(0, vi 2), (1, vi 9)] leafCalls
      [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]] := by
    intro asg hasg _hleaf hvio
    have h2 := hvio (1, vi 9) (by simp)
    have hspec := allAssigns_spec [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]] asg hasg
    obtain ⟨_, hget⟩ := hspec
    have hin := hget 1 (vi 9) h2
    exact absurd hin (by
      intro hcon
      have hthis : vi 9 = vi 1 ∨ vi 9 = vi 2 ∨ vi 9 = vi 3 := by
        simp only [getSlot, List.mem_cons] at hcon
        rcases hcon with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h (by simp)
      rcases hthis with heq | heq
      · exact absurd heq (by intro h; injection h with h2; exact absurd h2 (by simp))
      · rcases heq with heq | heq
        · exact absurd heq (by intro h; injection h with h2; exact absurd h2 (by simp))
        · exact absurd heq (by intro h; injection h with h2; exact absurd h2 (by simp)))
  -- the agreement theorem instantiated: the NoGood-checked search IS
  -- the reference search (entailed pruning is correctness-neutral)
  have hagree : nogoodSearch leafCalls [ngent] slots93 []
      = search leafCalls slots93 [] := by
    have h := nogoodSearch_agrees (ngs := [ngent]) (leaf := leafCalls)
      (slots := [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]])
      (fun ng hng => by
        rw [List.mem_singleton] at hng
        subst hng
        exact hent)
    exact h
  st ← st.check "agreement: entailed NoGood does not change the search"
    (nogoodSearch leafCalls [ngent] slots93 [] == search leafCalls slots93 [])
  -- and concretely: both find the first solution x + y = 4
  st ← st.check "agreement: concrete outcomes equal"
    (nogoodSearch leafCalls [ngent] slots93 [] == search leafCalls slots93 [] &&
      search leafCalls slots93 [] == some [vi 1, vi 3])

  -- a NON-entailed NoGood: (0,1),(1,3) matches the solution — pruning
  -- it would lose solutions
  let ngbad : NoGood := [(0, vi 1), (1, vi 3)]
  have hprunes : ngLeaf leafCalls [ngbad] [vi 1, vi 3] = false :=
    ngLeaf_prunes_of_violated (leaf := leafCalls) (ng := ngbad)
      (asg := [vi 1, vi 3]) (by rfl : leafCalls [vi 1, vi 3] = true)
      (by
        intro p hp
        rcases List.mem_cons.mp hp with heq | hin
        · rw [heq]; rfl
        · rw [List.mem_singleton.mp hin]; rfl)
  st ← st.check "non-entailed: prunes a leaf-passing assignment"
    (ngLeaf leafCalls [ngbad] [vi 1, vi 3] == false)
  -- and the NoGood-checked search with it loses the first solution:
  -- the reference search returns [1,3]; pruning the non-entailed
  -- NoGood makes it return [2,2] instead (a different solution) —
  -- the outcome changed, which cannot happen with entailed NoGoods
  st ← st.check "non-entailed: search outcome changes"
    (nogoodSearch leafCalls [ngbad] slots93 [] == some [vi 2, vi 2] &&
      search leafCalls slots93 [] == some [vi 1, vi 3] &&
      nogoodSearch leafCalls [ngbad] slots93 [] != search leafCalls slots93 [])

  -- ## failedSubtree_entailed instantiated on a genuinely failed subtree

  -- the subtree below the decision prefix [vi 1] is fruitless for
  -- leaf5: 1 + y = 5 needs y = 4, outside 1..3
  st ← st.check "failedSubtree: [vi 1] is a failed prefix for leaf5"
    ([vi 1, vi 2, vi 3].all (fun y => leaf5 [vi 1, y] == false))
  -- assemble the search_none-style evidence and apply the theorem
  have hev : ∀ a ∈ allAssigns (slots93.drop 1), leaf5 ([vi 1] ++ a) = false := by
    intro a ha
    have ha1 : a = [vi 1] ∨ a = [vi 2] ∨ a = [vi 3] := by
      have h := (mem_allAssigns_single (d := [vi 1, vi 2, vi 3]) (a := a)).mp ha
      obtain ⟨w, hw, heq⟩ := h
      rcases List.mem_cons.mp hw with rfl | h2
      · exact Or.inl heq
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (Or.inl heq)
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact Or.inr (Or.inr heq)
          · exact absurd h4 (by simp)
    rcases ha1 with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  -- the learned NoGood pairsOf [vi 1] is entailed at the root scope
  have hlearned := failedSubtree_entailed (leaf := leaf5) (full := slots93)
    (pre := [vi 1]) hev
  -- observable content: no leaf-passing complete assignment matches it
  st ← st.check "failedSubtree: learned NoGood excludes no solution"
    ((allAssigns slots93).all (fun asg =>
      leaf5 asg == false || NoGood.violatedB (pairsOf [vi 1]) asg == false))
  -- and pruning with it does not lose leaf5's solution
  st ← st.check "failedSubtree: pruning with learned NoGood is safe"
    (nogoodSearch leaf5 [pairsOf [vi 1]] slots93 [] == search leaf5 slots93 [] &&
      search leaf5 slots93 [] == some [vi 2, vi 3])

  -- ## The learning loop agrees with plain search

  -- SAT model, several fuels
  for fuel in [0, 1, 2, 5, 100] do
    st ← st.check s!"learnSearch: agrees with search (SAT, fuel {fuel})"
      (learnSearch fuel leafCalls slots93 == search leafCalls slots93 [])
  -- UNSAT model: x + y = 7
  for fuel in [0, 1, 2, 5, 100] do
    st ← st.check s!"learnSearch: agrees with search (UNSAT, fuel {fuel})"
      (learnSearch fuel leaf7 slots93 == search leaf7 slots93 [] &&
        search leaf7 slots93 [] == none)
  -- UNSAT with a single slot
  let leafS : List Value → Bool :=
    fun l => match l with
      | [Value.int a] => a == 9
      | _ => false
  st ← st.check "learnSearch: single-slot UNSAT"
    (learnSearch 3 leafS [[vi 1, vi 2]] == none)
  -- empty-slot model: the leaf decides on the empty assignment
  st ← st.check "learnSearch: no slots, leaf true"
    (learnSearch 2 (fun l => l == []) ([] : List (List Value)) == some [])
  st ← st.check "learnSearch: no slots, leaf false"
    (learnSearch 2 (fun _ => false) ([] : List (List Value)) == none)
  -- fuel 0 is the plain reference search (the theorem, on two models)
  st ← st.check "learnSearch_zero: fuel 0 is plain search"
    (learnSearch 0 leafCalls slots93 == search leafCalls slots93 [] &&
      learnSearch 0 leaf7 slots93 == search leaf7 slots93 [])

  -- ## Master theorems re-verified by brute force

  -- learnSearch_none: a none verdict excludes every assignment
  st ← st.check "learnSearch_none: brute force agrees (UNSAT)"
    ((allAssigns slots93).all (fun a => leaf7 a == false) &&
      learnSearch 10 leaf7 slots93 == none)
  -- learnSearch_some: a returned assignment passes the leaf
  match learnSearch 10 leafCalls slots93 with
  | some r =>
      st ← st.check "learnSearch_some: returned assignment passes leaf"
        (leafCalls r == true &&
          (allAssigns slots93).any (fun a => a == r))
  | none => st ← st.check "learnSearch_some: found solution" false
  -- the solution returned by learning is a real solution
  st ← st.check "learnSearch: solution is a real solution"
    (match learnSearch 10 leafCalls slots93 with
     | some r => (allAssigns slots93).any (fun a => leafCalls a && a == r)
     | none => false)

  -- ## Pruning observed with an instrumented leaf

  -- The reference search evaluates the model leaf at every complete
  -- assignment of the UNSAT model: 9 leaf calls (the counting twin
  -- mirrors `search`'s structure exactly).
  let refCount := (searchCount leaf7 slots93 []).1
  st ← st.check "pruning observed: reference evaluates all 9 leaves"
    (refCount == 9)

  -- Learn the three decision-trail NoGoods from the genuinely failed
  -- subtrees below [vi 1], [vi 2], [vi 3] (each x-subtree of x + y = 7
  -- over 1..3 is fruitless: 1+6, 2+5, 3+4 all need y outside 1..3).
  have hev1 : ∀ a ∈ allAssigns (slots93.drop 1), leaf7 ([vi 1] ++ a) = false := by
    intro a ha
    have ha1 : a = [vi 1] ∨ a = [vi 2] ∨ a = [vi 3] := by
      have h := (mem_allAssigns_single (d := [vi 1, vi 2, vi 3]) (a := a)).mp ha
      obtain ⟨w, hw, heq⟩ := h
      rcases List.mem_cons.mp hw with rfl | h2
      · exact Or.inl heq
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (Or.inl heq)
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact Or.inr (Or.inr heq)
          · exact absurd h4 (by simp)
    rcases ha1 with rfl | rfl | rfl <;> rfl
  have hev2 : ∀ a ∈ allAssigns (slots93.drop 1), leaf7 ([vi 2] ++ a) = false := by
    intro a ha
    have ha1 : a = [vi 1] ∨ a = [vi 2] ∨ a = [vi 3] := by
      have h := (mem_allAssigns_single (d := [vi 1, vi 2, vi 3]) (a := a)).mp ha
      obtain ⟨w, hw, heq⟩ := h
      rcases List.mem_cons.mp hw with rfl | h2
      · exact Or.inl heq
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (Or.inl heq)
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact Or.inr (Or.inr heq)
          · exact absurd h4 (by simp)
    rcases ha1 with rfl | rfl | rfl <;> rfl
  have hev3 : ∀ a ∈ allAssigns (slots93.drop 1), leaf7 ([vi 3] ++ a) = false := by
    intro a ha
    have ha1 : a = [vi 1] ∨ a = [vi 2] ∨ a = [vi 3] := by
      have h := (mem_allAssigns_single (d := [vi 1, vi 2, vi 3]) (a := a)).mp ha
      obtain ⟨w, hw, heq⟩ := h
      rcases List.mem_cons.mp hw with rfl | h2
      · exact Or.inl heq
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact Or.inr (Or.inl heq)
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact Or.inr (Or.inr heq)
          · exact absurd h4 (by simp)
    rcases ha1 with rfl | rfl | rfl <;> rfl
  have hng1 := failedSubtree_entailed (leaf := leaf7) (full := slots93)
    (pre := [vi 1]) hev1
  have hng2 := failedSubtree_entailed (leaf := leaf7) (full := slots93)
    (pre := [vi 2]) hev2
  have hng3 := failedSubtree_entailed (leaf := leaf7) (full := slots93)
    (pre := [vi 3]) hev3
  let learned : List NoGood := [pairsOf [vi 1], pairsOf [vi 2], pairsOf [vi 3]]
  -- every complete assignment of the model matches some learned NoGood
  -- (x is 1, 2, or 3): the guarded search consults the model leaf zero
  -- times — every leaf evaluation is pruned — and still returns none
  let prunedCount := ((allAssigns slots93).filter (fun asg =>
    !(learned.any (fun ng => ng.violatedB asg)))).length
  st ← st.check "pruning observed: learned NoGoods prune every leaf call"
    (prunedCount == 0)
  -- the guarded search returns the same verdict as the plain search
  st ← st.check "pruning observed: guarded search verdict unchanged"
    (search (guardLeaf leaf7 learned) slots93 [] == none &&
      search leaf7 slots93 [] == none)
  -- the guarded leaf agrees with the composed leaf on every assignment
  -- (so the guarded search IS the NoGood-checked search, semantically)
  st ← st.check "pruning observed: guarded leaf equals composed leaf"
    ((allAssigns slots93).all (fun asg =>
      guardLeaf leaf7 learned asg == ngLeaf leaf7 learned asg))

  -- and the learning loop itself returns the same none verdict with
  -- enough fuel to learn all three subtrees
  st ← st.check "pruning observed: learnSearch verdict (fuel to learn)"
    (learnSearch 100 leaf7 slots93 == none)

  if st.failed == 0 then
    IO.println s!"passed {st.passed} learning tests"
    return 0
  else
    IO.eprintln s!"{st.failed} learning tests FAILED ({st.passed} passed)"
    return 1
