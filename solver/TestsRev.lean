import solver.Solver

/-!
# Reversible-state tests (PLAN.md 6.4)

Unit tests for the sparse-set reversible state of
`solver/RevState.lean`:

* membership and the refinement bridge: `sparseMem` vs the logical
  view (`sparseToList`), list-built domains round-trip;
* removal: swap-and-shrink drops exactly the removed position's
  value (checked against the spec characterization
  `sparseRemove_spec` on duplicate-free windows), prefix
  invariance, and restore-after-removal round trips (the trail
  guarantee, single and repeated);
* narrowing: filter spec (the narrowed view is exactly the old
  view's filter), subset + keeps, membership characterization;
* the state level: multi-slot states, repeated narrowings with a
  trail, backtrack-to-ancestor recovers every slot's view;
* propagation pass: one round of `propEqSlot`/`propConstEq`
  applied through `revPropPass` agrees with the direct
  list-level application per slot (`revPropPass_refines`
  exercised on real data);
* performance sanity (informational): narrow + restore cycles on
  a 100,000-value domain, printed with timing, no threshold.
-/

open LeanFzn LeanFzn.Solution LeanFzn.Solver

/-- A mutable failure flag with a counted check helper (the style of
    `solver/Tests.lean`). -/
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

/-- The values of a sparse domain's logical view, as a list of
    integers where applicable (for display and comparison). -/
def domInts (l : List Value) : List Int :=
  l.filterMap (fun v => match v with
    | .int p => some p
    | _ => none)

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Membership and the refinement bridge

  -- a list-built domain's view is the list
  let d1 := sparseOfList [vi 1, vi 2, vi 3]
  st ← st.check "view: list-built domain"
    (sparseToList d1 == [vi 1, vi 2, vi 3])
  -- membership agrees with the view (the refinement bridge)
  st ← st.check "bridge: membership scan"
    (sparseMem d1 (vi 2) == true && sparseMem d1 (vi 9) == false &&
      sparseMem d1 (vi 1) == true && sparseMem d1 (vi 3) == true)

  -- ## Removal: swap-and-shrink

  -- removing a middle position drops exactly that value
  let d2 := sparseOfList [vi 1, vi 2, vi 3, vi 4]
  let d2' := sparseRemove d2 1
  st ← st.check "remove: window shrinks by one"
    (d2'.size + 1 == d2.size && d2'.vals.size == d2.vals.size)
  st ← st.check "remove: dropped exactly the position's value"
    (sparseMem d2' (vi 2) == false &&
      sparseMem d2' (vi 1) && sparseMem d2' (vi 3) && sparseMem d2' (vi 4))
  -- the spec characterization: for every value, membership after
  -- removal = membership before AND not the removed value
  st ← st.check "remove: spec characterization on all probe values"
    (([vi 1, vi 2, vi 3, vi 4, vi 7].all (fun v =>
      sparseMem d2' v == (sparseMem d2 v && v != d2.vals.getD 1 default))))

  -- restore-after-removal round trip (the single-removal trail
  -- guarantee, checked both directions)
  let d2r := sparseRestore d2' d2.size
  st ← st.check "restore: single removal recovers the membership set"
    ([vi 1, vi 2, vi 3, vi 4, vi 7].all (fun v =>
      sparseMem d2r v == sparseMem d2 v))

  -- repeated removals from a common ancestor
  let d3 := sparseOfList [vi 1, vi 2, vi 3, vi 4, vi 5]
  let d3a := sparseRemove (sparseRemove d3 0) 1
  let d3r := sparseRestore d3a d3.size
  st ← st.check "restore: multi-removal recovers the membership set"
    ([vi 1, vi 2, vi 3, vi 4, vi 5, vi 9].all (fun v =>
      sparseMem d3r v == sparseMem d3 v))
  -- prefix invariance: removal permutes only the window
  st ← st.check "remove: prefix invariance at the window size"
    ([vi 1, vi 2, vi 3, vi 4, vi 5].all (fun v =>
      (v ∈ d3a.vals.toList.take d3.size) == (v ∈ d3.vals.toList.take d3.size)))

  -- ## Narrowing: the in-place compaction pass

  -- the narrowed view is exactly the filter (order preserved)
  let d4 := sparseOfList [vi 1, vi 2, vi 3, vi 4, vi 5, vi 6]
  let keepEven : Value → Bool := fun v => match v with
    | .int p => p % 2 == 0
    | _ => false
  let d4n := sparseNarrow keepEven d4
  st ← st.check "narrow: view is the filter"
    (sparseToList d4n == (sparseToList d4).filter keepEven)
  st ← st.check "narrow: window only shrinks, array preserved"
    (d4n.size ≤ d4.size && d4n.vals.size == d4.vals.size)
  st ← st.check "narrow: keeps the passing values"
    (sparseMem d4n (vi 2) && sparseMem d4n (vi 4) && sparseMem d4n (vi 6) &&
      !sparseMem d4n (vi 1) && !sparseMem d4n (vi 3))
  -- narrowing to everything keeps everything; to nothing empties
  st ← st.check "narrow: keep-all is identity on the view"
    (sparseToList (sparseNarrow (fun _ => true) d4) == sparseToList d4)
  st ← st.check "narrow: keep-nothing empties the view"
    (sparseToList (sparseNarrow (fun _ => false) d4) == [])

  -- ## The solver-level state

  -- build a state of three slots
  let mkState (doms : List (List Value)) : RevState :=
    ⟨(doms.map sparseOfList).toArray⟩
  let s1 := mkState [[vi 1, vi 2, vi 3], [vi 4, vi 5], [vi 6, vi 7, vi 8]]
  -- logical view per slot
  st ← st.check "state: slot views"
    (revGet s1 0 == [vi 1, vi 2, vi 3] && revGet s1 1 == [vi 4, vi 5] &&
      revGet s1 2 == [vi 6, vi 7, vi 8] && revGet s1 5 == [])
  st ← st.check "state: materialized logical view"
    (revDoms s1 == [[vi 1, vi 2, vi 3], [vi 4, vi 5], [vi 6, vi 7, vi 8]])

  -- narrowing one slot leaves others untouched
  let s2 := revNarrow s1 1 (fun v => v == vi 5)
  st ← st.check "state: narrow one slot"
    (revGet s2 1 == [vi 5] && revGet s2 0 == [vi 1, vi 2, vi 3] &&
      revGet s2 2 == [vi 6, vi 7, vi 8])

  -- subset and keeps (the membership characterization)
  st ← st.check "state: narrowing only removes"
    ([vi 4, vi 5, vi 1, vi 6].all (fun v =>
      (v ∈ revGet s2 1) → (v ∈ revGet s1 1)))
  st ← st.check "state: narrowing keeps passing values"
    (vi 5 ∈ revGet s2 1 && !((vi 4) ∈ revGet s2 1) && !((vi 6) ∈ revGet s2 1))

  -- ## The trail and backtracking

  -- a trail with multiple slots and repeated narrowings of one slot
  let s3 := mkState [[vi 1, vi 2, vi 3], [vi 4, vi 5, vi 6]]
  -- narrow slot 0 to {2,3}, then to {3}; narrow slot 1 to {5}
  let (s4, e1) := revNarrowStep s3 0 (fun v => v == vi 2 || v == vi 3)
  let (s5, e2) := revNarrowStep s4 0 (fun v => v == vi 3)
  let (s6, e3) := revNarrowStep s5 1 (fun v => v == vi 5)
  let trail : revTrail := [e3, e2, e1]
  -- backtracking to the ancestor recovers every slot's view (as a
  -- membership set — the guarantee is membership-level, the array
  -- stays a permutation of the ancestor's window)
  let sb := revBacktrack s6 trail
  st ← st.check "trail: backtrack recovers slot 0"
    ((revGet sb 0).all (fun v => [vi 1, vi 2, vi 3].any (fun u => u == v)) &&
      [vi 1, vi 2, vi 3].all (fun v => (revGet sb 0).any (fun u => u == v)))
  st ← st.check "trail: backtrack recovers slot 1"
    ((revGet sb 1).all (fun v => [vi 4, vi 5, vi 6].any (fun u => u == v)) &&
      [vi 4, vi 5, vi 6].all (fun v => (revGet sb 1).any (fun u => u == v)))
  -- the trail entries record pre-narrowing sizes
  st ← st.check "trail: entries record the narrowed slots"
    (e1.slot == 0 && e2.slot == 0 && e3.slot == 1)
  -- intermediate state before full backtrack: slot 0 is {3}
  st ← st.check "trail: intermediate narrowings take effect"
    (revGet s6 0 == [vi 3] && revGet s6 1 == [vi 5])

  -- ## A propagation round on the reversible state

  -- propEqSlot 0 1 on [[1,2,3],[2,3,4]]: both slots narrow to the
  -- intersection [2,3]
  let sp := mkState [[vi 1, vi 2, vi 3], [vi 2, vi 3, vi 4]]
  match revPropPass sp [propEqSlot 0 1] with
  | .narrowed sp' =>
      -- the refinement theorem's conclusion, checked directly: the
      -- state's views agree with the list-level pass's output
      match propEqSlot 0 1 (revDoms sp) with
      | .narrowed doms' =>
          let agree := ((revDoms sp').zip doms').all (fun p =>
            domInts p.1 == domInts p.2)
          st ← st.check "propPass: reversible state agrees with lists"
            (agree && doms' == [[vi 2, vi 3], [vi 2, vi 3]])
      | .contradiction =>
          st ← st.check "propPass: reversible state agrees with lists" (false)
  | .contradiction =>
      st ← st.check "propPass: eq pass narrows" (false)

  -- propConstEq 0 5 on [[5,6],[7]]: slot 0 pins to {5}
  let sc := mkState [[vi 5, vi 6], [vi 7]]
  match revPropPass sc [propConstEq 0 (vi 5)] with
  | .narrowed sc' =>
      match propConstEq 0 (vi 5) (revDoms sc) with
      | .narrowed doms' =>
          let agree2 := ((revDoms sc').zip doms').all (fun p =>
            domInts p.1 == domInts p.2)
          st ← st.check "propPass: constEq refinement agrees"
            (agree2 && doms' == [[vi 5], [vi 7]])
      | .contradiction =>
          st ← st.check "propPass: constEq refinement agrees" (false)
  | .contradiction =>
      st ← st.check "propPass: constEq pass narrows" (false)

  -- a contradiction on the reversible state mirrors the list level
  let sx := mkState [[vi 1], [vi 2]]
  st ← st.check "propPass: contradiction mirrors the list level"
    (match revPropPass sx [propEqSlot 0 1] with
      | .contradiction => true
      | .narrowed _ => false)

  -- ## Performance sanity (informational): 100k-value domain

  let bigN := 100000
  let bigDom := sparseOfList ((List.range bigN).map (fun k => vi (Int.ofNat k)))
  let t0 ← IO.monoMsNow
  let mut cur := bigDom
  for i in [0:20] do
    -- narrow to the multiples of (i+2), then restore the saved
    -- size — one narrow+restore cycle per iteration
    let savedSize := cur.size
    cur := sparseNarrow (fun v => match v with
      | .int p => p % (i + 2) == 0
      | _ => false) cur
    cur := sparseRestore cur savedSize
  let t1 ← IO.monoMsNow
  IO.println s!"perf: 20 narrow+restore cycles on {bigN} values: {t1 - t0} ms \
(last cycle kept {cur.size} of {bigN})"
  -- the restore chain should end back at the full window
  st ← st.check "perf: restore chain ends at the full window"
    (cur.size == bigN &&
      sparseMem cur (vi 0) && sparseMem cur (vi (bigN - 1)))

  if st.failed == 0 then
    IO.println s!"passed {st.passed} reversible-state tests"
    return 0
  else
    IO.eprintln s!"{st.failed} reversible-state tests FAILED ({st.passed} passed)"
    return 1
