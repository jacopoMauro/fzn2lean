import solver.Restarts

/-!
# Restart test executable (PLAN.md 6.6, restart half)

Tests the resource-bounded restart stack of `solver/Restarts.lean`:

* `searchBudget` — sufficient budgets reproduce the reference
  `search` exactly (found/exhausted agreement on several small
  cases, matching `searchBudget_search`); insufficient budgets
  produce `budgetOut` with no claim; a monotonicity instance
  matching `searchBudget_monotone` (the same claim at a larger
  budget);
* `restartSearch` — a schedule of growing budgets finds the
  solution once the budget suffices (`unknown` before); an
  all-`budgetOut` schedule returns `unknown`; a satisfiable
  instance is NEVER reported `unsat` (the safety theorem
  `restartSearch_never_falseUnsat`, instantiated on concrete
  cases); an UNSAT instance with a sufficient budget is certified
  `unsat`;
* `solveModelBounded` end to end — a small SAT model with a
  tiny-then-large budget schedule (unknown then sat, the emitted
  text checker-accepted) and an UNSAT model with a large budget
  (`unsat`).

Prints "passed N restart tests" and exits 0 on success; nonzero on
any failure.
-/

open LeanFzn LeanFzn.Solver LeanFzn.Check LeanFzn.Solution LeanFzn.Globals

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- A mutable failure flag with a counted check helper. -/
structure TestState where
  passed : Nat
  failed : Nat
  deriving Repr

def TestState.check (st : TestState) (name : String) (ok : Bool) : IO TestState := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Unit tests: searchBudget

  let leaf : List Int → Bool := fun l => match l with
    | [a, b] => a + b == 5
    | _ => false
  let slots : List (List Int) := [[1, 2, 3], [3, 4]]

  -- sufficient budget: same outcome as the reference search (found)
  st ← st.check "searchBudget: sufficient budget finds like search"
    (searchBudget leaf 100 slots [] == .found [1, 4] &&
      search leaf slots [] == some [1, 4])
  -- sufficient budget: exhausted agreement (none case)
  st ← st.check "searchBudget: sufficient budget exhausts like search"
    (searchBudget (fun _ => false) 100 slots [] == .exhausted &&
      search (fun _ => false) slots [] == none)
  -- zero budget: immediate budgetOut, no claim
  st ← st.check "searchBudget: zero budget is budgetOut"
    (searchBudget leaf 0 slots [] == .budgetOut)
  -- small budget: interrupted mid-search
  st ← st.check "searchBudget: tiny budget is budgetOut"
    (searchBudget leaf 1 slots [] == .budgetOut)
  -- monotonicity instance: a claim at budget b' persists at b ≥ b'
  st ← st.check "searchBudget: monotone claims (found)"
    (searchBudget leaf 5 slots [] == .found [1, 4] &&
      searchBudget leaf 50 slots [] == .found [1, 4])
  st ← st.check "searchBudget: monotone claims (exhausted)"
    (searchBudget (fun _ => false) 6 slots [] == .exhausted &&
      searchBudget (fun _ => false) 50 slots [] == .exhausted)
  -- more agreement cases: no slots, empty-domain slot
  st ← st.check "searchBudget: no slots, leaf true"
    (searchBudget (fun l => l == []) 10 ([] : List (List Int)) [] == .found [])
  st ← st.check "searchBudget: no slots, leaf false"
    (searchBudget (fun _ => false) 10 ([] : List (List Int)) [] == .exhausted)
  st ← st.check "searchBudget: empty domain slot exhausted"
    (searchBudget (fun _ => true) 10 ([[], [1]] : List (List Int)) [] == .exhausted)
  -- agreement with search on a larger instance, both outcomes
  let slots2 : List (List Nat) := [[1, 2], [10, 20], [100, 200]]
  st ← st.check "searchBudget: three-slot found agreement"
    (searchBudget (fun l => match l with
      | [a, b, c] => a + b + c == 222
      | _ => false) 100 slots2 [] == .found [2, 20, 200] &&
      search (fun l => match l with
        | [a, b, c] => a + b + c == 222
        | _ => false) slots2 [] == some [2, 20, 200])

  -- ## Unit tests: the reversed-accumulator fast twin (IDEAS 4.5)

  -- the twin is the reference searchBudget pointwise, on every case
  -- exercised above (both budgets already use the twin at runtime,
  -- so this compares the twin against itself *and* against enough
  -- leaf/slot/budget shapes to catch an accounting drift)
  st ← st.check "searchBudgetGo: twin equals reference on found cases"
    (searchBudgetImpl leaf 100 slots [] == searchBudget leaf 100 slots [] &&
      searchBudgetImpl leaf 5 slots [] == searchBudget leaf 5 slots [] &&
      searchBudgetImpl (fun l => l == []) 10 ([] : List (List Int)) [] ==
        searchBudget (fun l => l == []) 10 ([] : List (List Int)) [])
  st ← st.check "searchBudgetGo: twin equals reference on exhausted/budgetOut"
    (searchBudgetImpl (fun _ => false) 100 slots [] ==
        searchBudget (fun _ => false) 100 slots [] &&
      searchBudgetImpl (fun _ => false) 1 slots [] ==
        searchBudget (fun _ => false) 1 slots [] &&
      searchBudgetImpl leaf 0 slots [] == searchBudget leaf 0 slots [] &&
      searchBudgetImpl (fun _ => true) 10 ([[], [1]] : List (List Int)) [] ==
        searchBudget (fun _ => true) 10 ([[], [1]] : List (List Int)) [])
  -- the loop's leaf is tested on the slot-order accumulator: a
  -- leaf reading its input in slot order must agree with the twin
  -- on a budgeted walk (found, slot-order text)
  st ← st.check "searchBudgetGo: slot-order leaf and found value"
    (searchBudgetImpl leaf 100 slots [] == .found [1, 4] &&
      searchBudgetImpl leaf 4 slots [] == .found [1, 4])

  -- ## Unit tests: restartSearch

  -- schedule of growing budgets: unknown early, found once sufficient
  st ← st.check "restartSearch: tiny budgets give unknown"
    (restartSearch leaf [0, 1] slots == .unknown)
  st ← st.check "restartSearch: growing schedule finds the solution"
    (restartSearch leaf [0, 1, 2, 3, 4, 5, 100] slots == .sat [1, 4])
  -- all-budgetOut schedule: unknown
  st ← st.check "restartSearch: all-out schedule is unknown"
    (restartSearch leaf [0, 0, 0] slots == .unknown)
  -- empty schedule: unknown
  st ← st.check "restartSearch: empty schedule is unknown"
    (restartSearch leaf [] slots == .unknown)
  -- satisfiable instance: NEVER unsat, on every schedule tried
  -- (the safety theorem restartSearch_never_falseUnsat instantiated)
  st ← st.check "restartSearch: never false unsat with a solution"
    (restartSearch leaf [0, 1, 100] slots != .unsat &&
      restartSearch leaf [] slots != .unsat)
  -- unsatisfiable instance with a sufficient budget: certified unsat
  st ← st.check "restartSearch: unsat with sufficient budget"
    (restartSearch (fun _ => false) [100] slots == .unsat)
  -- unsatisfiable instance, tiny budgets: unknown (not unsat!)
  st ← st.check "restartSearch: interrupted unsat instance is unknown"
    (restartSearch (fun _ => false) [0, 1] slots == .unknown)
  -- exhaustion claims win as soon as the budget suffices
  st ← st.check "restartSearch: schedule decides after interruption"
    (restartSearch (fun _ => false) [0, 1, 2, 100] slots == .unsat)

  -- ## End-to-end: solveModelBounded

  -- a small SAT model
  let m1 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  -- tiny budgets: unknown (interrupted, no claim)
  st ← st.check "bounded solver: tiny budgets give unknown"
    (solveModelBounded m1 [0, 1] == .unknown)
  -- tiny-then-large: found, and the emitted text is checker-accepted
  match solveModelBounded m1 [0, 1, 2, 3, 100] with
  | .sat text =>
      st ← st.check "bounded solver: restart finds accepted solution"
        (checkModelSolution m1 text == .accepted)
  | _ => st ← st.check "bounded solver: restart finds accepted solution" (false)
  -- an UNSAT model: x in 1..2, y in 1..2, x > 3 is impossible
  let m2 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nconstraint int_le(x, y);\n\
     constraint int_le(y, x);\nconstraint int_plus(x, y, 6);\nsolve satisfy;"
  -- reference agreement first
  match solveModel m2 with
  | .unsat =>
      st ← st.check "bounded solver: unsat model is unsat with large budget"
        (solveModelBounded m2 [100] == .unsat)
      -- interrupted: unknown, never unsat
      st ← st.check "bounded solver: unsat model unknown when interrupted"
        (solveModelBounded m2 [0, 1] == .unknown &&
          solveModelBounded m2 [0, 1] != .unsat)
  | _ => st ← st.check "bounded solver: unsat model is unsat by reference" (false)
  -- a statically refused model (unbounded var int): unknown, no claim
  let m3 := parseOrPanic
    "var int: x;\nvar 1..3: y;\nconstraint int_le(x, 5);\nsolve satisfy;"
  st ← st.check "bounded solver: out-of-fragment model is unknown"
    (solveModelBounded m3 [100] == .unknown)

  if st.failed == 0 then
    IO.println s!"passed {st.passed} restart tests"
    return 0
  else
    IO.eprintln s!"{st.failed} restart tests FAILED ({st.passed} passed)"
    return 1
