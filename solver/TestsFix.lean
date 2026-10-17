import solver.Solver

/-!
# Fixpoint and pruning-search tests (PLAN.md 6.3, part 2)

Unit tests for the propagation fixpoint and the pruning search of
`solver/Fixpoint.lean`:

* fixpoint unit tests: a list of propagators on small domains
  reaching a stable fixpoint (a `constEq` pins a slot, `eqSlot`
  narrows another, `leSlot` tightens both), contradiction detection
  (an out-of-domain constant, a chain `x = 5 ∧ x ≤ y ∧ y ≤ 3`), and
  idempotence-style behavior on already-stable domains;
* pruning-search tests: agreement with the reference `search` on the
  same leaf (both `some` and `none` outcomes) for several constraint
  sets, a case where propagation prunes dead branches before the
  search starts (observable as a smaller domain after the fixpoint),
  and an UNSAT case where the fixpoint hits a contradiction at the
  root (two `constEq` on the same slot with different values), so no
  leaf is ever evaluated.
-/

open LeanFzn LeanFzn.Solution LeanFzn.Solver

/-- A mutable failure flag with a counted check helper (the style of
    `solver/TestsProp.lean`). -/
structure TestState where
  passed : Nat
  failed : Nat

def TestState.check (st : TestState) (name : String) (ok : Bool) : IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def vi (i : Int) : Value := .int i

/-- Structural equality of domain lists (reuse the propagators'
    Boolean equality, which `domsEqB_iff` proves to be genuine
    equality). -/
def domEq (a b : List (List Value)) : Bool := domsEqB a b

/-- The result of a fixpoint run is a specific narrowed domain
    list. -/
def narrowedTo (r : PropResult) (d : List (List Value)) : Bool :=
  match r with
  | .narrowed d' => domEq d' d
  | .contradiction => false

/-- The result of a fixpoint run is a contradiction. -/
def isContradiction (r : PropResult) : Bool :=
  match r with
  | .contradiction => true
  | .narrowed _ => false

/-- Whether two option results agree (both none, or both some with
    equal values under `Value` equality). -/
def optEq (a b : Option (List Value)) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => x.length == y.length && (x.zip y).all (fun p => p.1.eqB p.2)
  | _, _ => false

/-- The leaf: slot 0 and slot 1 are equal AND both at most 3
    (satisfied by every assignment the constraint set below
    accepts — the pruning licence of `prunedSearch_none`). -/
def leafEqLe3 (a : List Value) : Bool :=
  match a[0]?, a[1]? with
  | some x, some y => x.eqB y && x.eqB (vi 3) == false && x.eqB (vi 4) == false
  | _, _ => false

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Fixpoint: reaching a stable fixpoint

  -- constEq pins slot 0 to 2; eqSlot narrows slot 1 to the
  -- intersection [2,3] ∩ [2,4] = [2]; leSlot keeps everything
  -- (2 ≤ 2).  After one pass the domains [[2],[2]] are stable.
  st ← st.check "fix: const, eq, le reach stable fixpoint"
    (narrowedTo (fixpointFuel [propConstEq 0 (vi 2), propEqSlot 0 1, propLeSlot 0 1] 10
      [[vi 2, vi 3], [vi 2, vi 3, vi 4]]) [[vi 2], [vi 2]])

  -- same chain, checked after the fixpoint is stable on the second
  -- pass (idempotence: the stable domains are returned unchanged)
  st ← st.check "fix: idempotent on stable domains"
    (narrowedTo (fixpointFuel [propConstEq 0 (vi 2), propEqSlot 0 1, propLeSlot 0 1] 10
      [[vi 2], [vi 2]]) [[vi 2], [vi 2]])

  -- with fuel 0 nothing is narrowed (the fuel exists for
  -- termination; soundness holds anyway)
  st ← st.check "fix: zero fuel returns input"
    (narrowedTo (fixpointFuel [propConstEq 0 (vi 2), propEqSlot 0 1] 0
      [[vi 2, vi 3], [vi 2, vi 3]]) [[vi 2, vi 3], [vi 2, vi 3]])

  -- a chain needs several rounds: constEq y=2 (slot 1) then eqSlot
  -- narrows slot 0 in the NEXT pass — the fixpoint iterates until
  -- stable
  st ← st.check "fix: narrowing across rounds"
    (narrowedTo (fixpointFuel [propEqSlot 0 1, propConstEq 1 (vi 2)] 10
      [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]]) [[vi 2], [vi 2]])

  -- propagation tightens bounds across a chain: x ≤ y, y ≤ 3
  -- (constEq), so x ≤ 3
  st ← st.check "fix: bound tightening across constraints"
    (narrowedTo (fixpointFuel [propLeSlot 0 1, propConstEq 1 (vi 3)] 10
      [[vi 1, vi 2, vi 3, vi 4], [vi 2, vi 3, vi 4]]) [[vi 1, vi 2, vi 3], [vi 3]])

  -- ## Fixpoint: contradiction detection

  -- constEq with an out-of-domain value: contradiction
  st ← st.check "fix: contradiction on absent constant"
    (isContradiction (fixpointFuel [propConstEq 0 (vi 9)] 10 [[vi 1, vi 2]]))

  -- two constEq on the same slot with different values
  st ← st.check "fix: contradiction on conflicting constants"
    (isContradiction (fixpointFuel [propConstEq 0 (vi 1), propConstEq 0 (vi 2)] 10
      [[vi 1, vi 2]]))

  -- eqSlot with disjoint domains
  st ← st.check "fix: contradiction on disjoint equality"
    (isContradiction (fixpointFuel [propEqSlot 0 1] 10 [[vi 1, vi 2], [vi 3, vi 4]]))

  -- the chain x = 5 ∧ x ≤ y ∧ y ≤ 3 (5 ≤ y ≤ 3 is empty)
  st ← st.check "fix: contradiction on crossed bounds chain"
    (isContradiction (fixpointFuel [propConstEq 0 (vi 5), propLeSlot 0 1,
      propConstEq 1 (vi 3)] 10 [[vi 1, vi 5], [vi 1, vi 3]]))

  -- contradiction found on the first pass (fuel 1 suffices)
  st ← st.check "fix: contradiction found early"
    (isContradiction (fixpointFuel [propConstEq 0 (vi 9)] 1 [[vi 1, vi 2]]))

  -- ## Pruning search: agreement with the reference search

  -- a satisfiable constraint set: x = y, x ∈ {2,3}, y ∈ {2,3,4}
  -- leaf: x = y (agrees with the constraints)
  let leafEq (a : List Value) : Bool :=
    match a[0]?, a[1]? with
    | some x, some y => x.eqB y
    | _, _ => false
  st ← st.check "pruned: agrees with search (sat)"
    (optEq (prunedSearch leafEq [propEqSlot 0 1] 10 [[vi 2, vi 3], [vi 2, vi 3, vi 4]] [])
      (search leafEq [[vi 2, vi 3], [vi 2, vi 3, vi 4]] []))

  -- an unsatisfiable constraint set: x = y with disjoint domains —
  -- the leaf implies the constraint (equal slots), so agreement is
  -- guaranteed by the master theorems
  st ← st.check "pruned: agrees with search (unsat)"
    (optEq (prunedSearch leafEq [propEqSlot 0 1] 10 [[vi 2], [vi 3]] [])
      (search leafEq [[vi 2], [vi 3]] []))

  -- x ≤ y with y ≤ x forced: only equal pairs survive the leaf
  let leafLe (a : List Value) : Bool :=
    DomConstraint.satisfiedB (.leSlot 0 1) a
  st ← st.check "pruned: agrees with search (order)"
    (optEq (prunedSearch leafLe [propLeSlot 0 1] 10
      [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]] [])
      (search leafLe [[vi 1, vi 2, vi 3], [vi 1, vi 2, vi 3]] []))

  -- combined leaf with several constraints (x = y, x ≠ 4 implied)
  st ← st.check "pruned: agrees with search (combined)"
    (optEq (prunedSearch leafEqLe3 [propEqSlot 0 1, propLeSlot 0 1] 10
      [[vi 2, vi 3, vi 4], [vi 2, vi 3, vi 4]] [])
      (search leafEqLe3 [[vi 2, vi 3, vi 4], [vi 2, vi 3, vi 4]] []))

  -- unsatisfiable combined: x = y and x ≤ y but domains crossed
  -- so no assignment satisfies the constraints (let alone the leaf,
  -- which implies them)
  st ← st.check "pruned: agrees with search (conflict)"
    (optEq (prunedSearch leafEqLe3 [propEqSlot 0 1, propLeSlot 0 1] 10
      [[vi 4, vi 5], [vi 1, vi 2]] [])
      (search leafEqLe3 [[vi 4, vi 5], [vi 1, vi 2]] []))

  -- zero fuel: the pruning search IS the reference search
  st ← st.check "pruned: zero fuel is reference search"
    (optEq (prunedSearch leafEq [propEqSlot 0 1] 0
      [[vi 2, vi 3], [vi 2, vi 3, vi 4]] [])
      (search leafEq [[vi 2, vi 3], [vi 2, vi 3, vi 4]] []))

  -- ## Pruning observably reduces the domains before branching

  -- after the fixpoint on x = y ∧ y = 3, both domains are [[3],[3]]
  -- (no branching is needed at all)
  st ← st.check "pruned: fixpoint collapses domains"
    (match fixpointFuel [propEqSlot 0 1, propConstEq 1 (vi 3)] 10
        [[vi 2, vi 3, vi 4], [vi 2, vi 3, vi 4]] with
      | .narrowed d => domEq d [[vi 3], [vi 3]]
      | .contradiction => false)

  -- the pruning search on those domains returns the pinned
  -- assignment
  st ← st.check "pruned: finds the pinned assignment"
    (optEq (prunedSearch leafEq [propEqSlot 0 1, propConstEq 1 (vi 3)] 10
      [[vi 2, vi 3, vi 4], [vi 2, vi 3, vi 4]] []) (some [vi 3, vi 3]))

  -- ## UNSAT pruned at the root

  -- two constEq on the same slot with different values: the fixpoint
  -- contradicts immediately, the search returns none without
  -- evaluating a single leaf
  st ← st.check "pruned: root contradiction returns none"
    ((prunedSearch leafEq [propConstEq 0 (vi 1), propConstEq 0 (vi 2)] 10
      [[vi 1, vi 2], [vi 1, vi 2]] []).isNone)

  -- same for a contradiction through a chain: x = 1, x = y, y = 2
  st ← st.check "pruned: chain contradiction returns none"
    ((prunedSearch leafEq [propConstEq 0 (vi 1), propEqSlot 0 1, propConstEq 1 (vi 2)] 10
      [[vi 1, vi 2], [vi 1, vi 2]] []).isNone)

  -- and the reference search agrees on that unsat instance (the
  -- leaf implies the full constraint set — equal slots pinned to
  -- the constants — which the constants 1 ≠ 2 contradict)
  let leafChain (a : List Value) : Bool :=
    DomConstraint.satisfiedB (.constEq 0 (vi 1)) a &&
      DomConstraint.satisfiedB (.eqSlot 0 1) a &&
      DomConstraint.satisfiedB (.constEq 1 (vi 2)) a
  st ← st.check "pruned: unsat agrees with search"
    (optEq (prunedSearch leafChain [propConstEq 0 (vi 1), propEqSlot 0 1,
      propConstEq 1 (vi 2)] 10 [[vi 1, vi 2], [vi 1, vi 2]] [])
      (search leafChain [[vi 1, vi 2], [vi 1, vi 2]] []))

  if st.failed == 0 then
    IO.println s!"passed {st.passed} fixpoint tests"
    return 0
  else
    IO.eprintln s!"{st.failed} fixpoint tests FAILED ({st.passed} passed)"
    return 1
