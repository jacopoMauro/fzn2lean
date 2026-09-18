import solver.Solver

/-!
# Heuristic search tests (PLAN.md 6.5)

Tests the correctness-neutral heuristics of `solver/Heuristic.lean`:

* the MRV selector really sorts by ascending domain size with stable
  index tie-breaking, and produces admissible orders (`IsPerm`,
  checked both via the count view and by direct evaluation);
* `heuristicSearch` is a genuine reordering: on a hand-written
  reversed order it returns the (unique) satisfying assignment, and
  its reported assignment differs from the reference search's first
  hit only up to the chosen branching order — both are members of
  `allAssigns` and both pass the leaf;
* agreement: `heuristicSearch`/`mrvSearch` and the reference `search`
  agree on outcome (both find some, or both none) over a battery of
  SAT and UNSAT instances with different MRV orders, including an
  empty-domain slot;
* the master theorems hold on every checked instance (the returned
  assignment is in `allAssigns` and passes the leaf; on `none`, every
  assignment fails the leaf).

No `solveModel` integration here: `Solve.lean` wiring is Round 3,
so the tests stay generic over slot lists.
-/

open LeanFzn LeanFzn.Solver

/-- A mutable failure flag with a counted check helper. -/
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

/-- Decidable check that an order is admissible in the count sense:
    right length, every index below `n` exactly once. -/
private def isPermCheck (order : List Nat) (n : Nat) : Bool :=
  order.length == n &&
    (List.range n).all (fun i => order.count i == 1)

/-- Agreement check for one instance: the heuristic search (with the
    given order) and the reference search must agree on outcome.  The
    master theorems are instantiated on the actual outcome, and their
    conclusions are re-verified by brute force. -/
private def agreeCheck {α : Type} [Inhabited α] [BEq α] (name : String)
    (leaf : List α → Bool) (order : List Nat) (slots : List (List α))
    (hperm : IsPerm order slots.length) (st : TestState) : IO TestState := do
  let st ← st.check s!"{name}: order admissible" (isPermCheck order slots.length)
  let heur := heuristicSearch leaf order slots
  let ref := search leaf slots []
  -- outcome agreement
  let st ← st.check s!"{name}: outcome agreement (some/none)"
    (heur.isSome == ref.isSome)
  match hh : heur with
  | some r =>
      -- heuristicSearch_some, instantiated on this outcome: r is a
      -- complete assignment of the slots and passes the leaf
      let ⟨hr_mem, hr_leaf⟩ := heuristicSearch_some leaf order slots hperm hh
      -- brute-force re-verification of both conclusions
      let st ← st.check s!"{name}: found assignment in allAssigns"
        ((allAssigns slots).contains r)
      let st ← st.check s!"{name}: found assignment passes leaf" (leaf r)
      -- the theorem guarantees the checked Booleans are true
      let _ : r ∈ allAssigns slots := hr_mem
      let _ : leaf r = true := hr_leaf
      return st
  | none =>
      -- heuristicSearch_none_iff, instantiated: the reference search
      -- is none too
      have href := (heuristicSearch_none_iff leaf order slots hperm).mp hh
      let st ← st.check s!"{name}: reference none too" (ref.isNone)
      let _ : ref.isNone = true := by
        have h1 : ref = none := href
        rw [h1]; rfl
      -- heuristicSearch_none, instantiated: every assignment fails
      let st ← st.check s!"{name}: all assignments fail leaf"
        ((allAssigns slots).all (fun a => !leaf a))
      return st

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Selector sanity: mrvOrder evaluation

  -- ascending domain size
  st ← st.check "mrvOrder: ascending sizes"
    (mrvOrder ([[1, 2, 3], [1], [1, 2]] : List (List Int)) == [1, 2, 0])
  -- ties broken by ascending index (stability)
  st ← st.check "mrvOrder: stable ties"
    (mrvOrder ([[1, 2], [1, 2], [1, 2]] : List (List Int)) == [0, 1, 2])
  -- an empty domain sorts first
  st ← st.check "mrvOrder: empty domain first"
    (mrvOrder ([[1], [], [1, 2]] : List (List Int)) == [1, 0, 2])
  -- no slots
  st ← st.check "mrvOrder: no slots"
    (mrvOrder ([] : List (List Int)) == [])
  -- one slot
  st ← st.check "mrvOrder: one slot"
    (mrvOrder ([[1, 2]] : List (List Int)) == [0])
  -- five slots of varied sizes
  st ← st.check "mrvOrder: five slots"
    (mrvOrder ([[1, 2, 3, 4], [1, 2], [1, 2, 3], [1, 2, 3, 4, 5], [1]] :
      List (List Int)) == [4, 1, 2, 0, 3])
  -- booleans are just values
  st ← st.check "mrvOrder: bool slots"
    (mrvOrder ([[true], [true, false], [true, false]] : List (List Bool))
      == [0, 1, 2])

  -- ## Selector admissibility: IsPerm via the count view

  let slotss : List (List (List Int)) :=
    [ [[1, 2, 3], [1], [1, 2]]
    , [[1, 2], [1, 2], [1, 2]]
    , [[1], [], [1, 2]]
    , []
    , [[1, 2, 3, 4], [1, 2], [1, 2, 3], [1, 2, 3, 4, 5], [1]] ]
  let mut idx := 0
  for slots in slotss do
    idx := idx + 1
    st ← st.check s!"isPerm: mrvOrder instance {idx}"
      (isPermCheck (mrvOrder slots) slots.length)
    st ← st.check s!"isPerm: lexOrder instance {idx}"
      (isPermCheck (lexOrder slots.length) slots.length)

  -- ## Pointwise behavior: the reordered slot list

  -- selectSlots reorders by index; out-of-range would be [] but
  -- admissible orders stay in range
  st ← st.check "selectSlots: identity order"
    (selectSlots (lexOrder 3) ([[1], [2], [3]] : List (List Int)) == [[1], [2], [3]])
  st ← st.check "selectSlots: reversed order"
    (selectSlots [2, 1, 0] ([[1], [2], [3]] : List (List Int)) == [[3], [2], [1]])
  let slotsMrv : List (List Int) := [[1, 2, 3], [1], [1, 2]]
  st ← st.check "selectSlots: mrv order"
    (selectSlots (mrvOrder slotsMrv) slotsMrv == [[1], [1, 2], [1, 2, 3]])

  -- ## Heuristic search returns valid assignments in original order

  -- a unique solution found under a hand-written reversed order: the
  -- assignment is reported in ORIGINAL slot order
  let leafRev : List Int → Bool := fun l => match l with
    | [a, b] => a == 3 && b == 1
    | _ => false
  st ← st.check "heuristic: reversed order finds the unique solution"
    (heuristicSearch leafRev [1, 0] ([[1, 2, 3], [1]] : List (List Int))
      == some [3, 1])
  -- and the reference search finds it too
  st ← st.check "heuristic: reference agrees on unique solution"
    (search leafRev ([[1, 2, 3], [1]] : List (List Int)) [] == some [3, 1])
  -- with MRV (slot 1 is smallest): still the same unique solution
  st ← st.check "heuristic: mrv order finds the unique solution"
    (mrvSearch leafRev ([[1, 2, 3], [1]] : List (List Int)) == some [3, 1])

  -- ## Agreement battery: SAT and UNSAT instances

  -- SAT: x + y == 5 on small domains (several satisfying solutions)
  let leafSum : List Int → Bool := fun l => match l with
    | [a, b] => a + b == 5
    | _ => false
  let satSlots : List (List Int) := [[1, 2, 3], [3, 4]]
  st ← agreeCheck "agree sat sum" leafSum (mrvOrder satSlots) satSlots
      (mrvOrder_isPerm satSlots) st
  -- with the identity order too
  st ← agreeCheck "agree sat sum lex" leafSum (lexOrder satSlots.length) satSlots
      (lexOrder_isPerm satSlots.length) st
  -- with a hand-written reversed order
  st ← agreeCheck "agree sat sum rev" leafSum [1, 0] satSlots
      (by
        show ([1, 0] : List Nat).Perm (List.range 2)
        decide) st

  -- SAT with three slots, all different: MRV order differs from lex
  let leafAllDiff : List Int → Bool := fun l => match l with
    | [a, b, c] => a != b && b != c && a != c
    | _ => false
  let adSlots : List (List Int) := [[1, 2, 3], [1, 2], [1, 2, 3]]
  st ← st.check "agree alldiff: mrv differs from lex"
    (mrvOrder adSlots != lexOrder adSlots.length)
  st ← agreeCheck "agree alldiff mrv" leafAllDiff (mrvOrder adSlots) adSlots
      (mrvOrder_isPerm adSlots) st
  st ← agreeCheck "agree alldiff lex" leafAllDiff (lexOrder adSlots.length) adSlots
      (lexOrder_isPerm adSlots.length) st

  -- UNSAT: x + y == 100 impossible on the domains
  let leafBig : List Int → Bool := fun l => match l with
    | [a, b] => a + b == 100
    | _ => false
  st ← agreeCheck "agree unsat sum" leafBig (mrvOrder satSlots) satSlots
      (mrvOrder_isPerm satSlots) st

  -- UNSAT: alldiff on two singletons with equal domains
  let leafEq : List Int → Bool := fun l => match l with
    | [a, b] => a == b
    | _ => false
  let eqSlots : List (List Int) := [[1], [1]]
  st ← agreeCheck "agree unsat alldiff" leafAllDiff (mrvOrder eqSlots) eqSlots
      (mrvOrder_isPerm eqSlots) st

  -- SAT unique with empty leaf: always-true leaf, any assignment
  st ← agreeCheck "agree sat true" (fun _ => true)
      (mrvOrder satSlots) satSlots (mrvOrder_isPerm satSlots) st

  -- UNSAT with always-false leaf
  st ← agreeCheck "agree unsat false" (fun _ => false)
      (mrvOrder satSlots) satSlots (mrvOrder_isPerm satSlots) st

  -- empty-domain slot: no assignment at all, both searches none
  let emptySlots : List (List Int) := [[1, 2], [], [1, 2, 3]]
  st ← st.check "agree empty domain: mrvOrder puts empty first"
    ((mrvOrder emptySlots).head? == some 1)
  st ← agreeCheck "agree empty domain" (fun _ => true)
      (mrvOrder emptySlots) emptySlots (mrvOrder_isPerm emptySlots) st

  -- no slots: the empty assignment, leaf decides
  st ← agreeCheck "agree no slots true" (fun l => l == [])
      [] ([] : List (List Int)) (lexOrder_isPerm 0) st
  st ← agreeCheck "agree no slots false" (fun _ => false)
      [] ([] : List (List Int)) (lexOrder_isPerm 0) st

  -- one slot, three values, leaf on the singleton assignment
  st ← agreeCheck "agree one slot" (fun l => l == [2])
      (mrvOrder [[1, 2, 3]]) ([[1, 2, 3]] : List (List Int))
      (mrvOrder_isPerm [[1, 2, 3]]) st

  -- booleans
  let leafBool : List Bool → Bool := fun l => match l with
    | [a, b] => a && b
    | _ => false
  let boolSlots : List (List Bool) := [[true, false], [true, false]]
  st ← agreeCheck "agree bool mrv" leafBool (mrvOrder boolSlots) boolSlots
      (mrvOrder_isPerm boolSlots) st

  -- a larger mixed battery: 4 slots, conjunction of conditions
  let leafBig4 : List Int → Bool := fun l => match l with
    | [a, b, c, d] => a + b == 3 && c * d == 6 && a <= d
    | _ => false
  let bigSlots : List (List Int) := [[1, 2, 3], [1, 2], [2, 3, 4], [1, 2, 3, 6]]
  st ← agreeCheck "agree big4 mrv" leafBig4 (mrvOrder bigSlots) bigSlots
      (mrvOrder_isPerm bigSlots) st
  st ← agreeCheck "agree big4 lex" leafBig4 (lexOrder bigSlots.length) bigSlots
      (lexOrder_isPerm bigSlots.length) st
  -- hand-written rotation order [2,3,0,1]
  st ← agreeCheck "agree big4 rot" leafBig4 [2, 3, 0, 1] bigSlots
      (by
        show ([2, 3, 0, 1] : List Nat).Perm (List.range 4)
        decide) st

  if st.failed == 0 then
    IO.println s!"passed {st.passed} heuristic tests"
    return 0
  else
    IO.eprintln s!"{st.failed} heuristic tests FAILED ({st.passed} passed)"
    return 1
