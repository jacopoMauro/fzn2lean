import solver.Optimize

/-!
# Optimization tests (PLAN.md 6.7, optimization half)

Tests the two optimizers of `solver/Optimize.lean`:

* unit tests: `slotObjective` extraction (slot identifier, integer
  literal, non-slot identifier → unsupported, satisfy model →
  unsupported), `pickBest` minimality on small lists (minimize,
  maximize, ties, empty);
* end-to-end minimize/maximize models — the optimizers return
  `.optimal text v`, the text is re-checked with the verified
  checker (the conclusion of `optimizeModel_sat_sound`), and `v` is
  cross-checked against brute force over `allAssigns` (the
  conclusion of `optimizeModel_optimal`): the optimum of
  `minimize x` under `int_le(x, y)` is 1; the optimum of a sum
  objective through an auxiliary constrained variable
  (`int_plus(x, y, s); minimize s`) is 2; a maximization model; a
  model whose optimum is forced to a unique assignment;
* UNSAT optimization model (`.unsat`, brute-force cross-check);
* satisfy-model refusal; objective-scope refusals (boolean slot
  objective, initialized-variable objective);
* branch-and-bound agreement: `optimizeModelBb` and `optimizeModel`
  return the same optimal *value* on every solvable model above
  (the conclusion of `optimizeModelBb_agrees`) and the same verdict
  classification overall.
-/

open LeanFzn LeanFzn.Solver LeanFzn.Check LeanFzn.Solution LeanFzn.Globals

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

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- Brute-force optimum through the checker: fold over every complete
    assignment of the slot domains, keep the accepted ones' objective
    values, and take the best (minimize or maximize). -/
private def bruteForceOpt (m : Model) (min : Bool) : Option Int :=
  let vals := ((allAssigns (slotDomains m)).filter (fun asg =>
    checkModelSolution m (emitAssignment (slotNames m) asg) == .accepted)).filterMap
    (fun asg => slotObjective m (slotNames m) asg)
  match min with
  | true => vals.foldl (fun acc v => match acc with
      | none => some v
      | some b => some (if v < b then v else b)) none
  | false => vals.foldl (fun acc v => match acc with
      | none => some v
      | some b => some (if b < v then v else b)) none

/-- Do the two optimizers agree on the verdict classification? -/
private def sameVerdict (r1 r2 : OptResult) : Bool :=
  match r1, r2 with
  | .optimal _ _, .optimal _ _ => true
  | .unsat, .unsat => true
  | .unsupported _, .unsupported _ => true
  | _, _ => false

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Unit tests: objective extraction

  -- a slot identifier objective evaluates to the slot's value
  let mx := parseOrPanic "var 1..9: x;\nsolve minimize x;"
  st ← st.check "slotObjective: slot identifier"
    (slotObjective mx ["x"] [Value.int 3] == some 3)
  -- an integer literal objective is its own value
  let ml := parseOrPanic "solve minimize 7;"
  st ← st.check "slotObjective: integer literal"
    (slotObjective ml [] [] == some 7)
  -- a boolean slot objective is not an integer
  let mb := parseOrPanic "var bool: b;\nsolve minimize b;"
  st ← st.check "slotObjective: boolean slot is not an int"
    (slotObjective mb ["b"] [Value.bool true] == none)
  -- a satisfaction model has no objective
  let ms := parseOrPanic "var 1..3: x;\nsolve satisfy;"
  st ← st.check "slotObjective: satisfy model gives none"
    (slotObjective ms ["x"] [Value.int 2] == none)
  -- slot lookup by name: first occurrence wins
  st ← st.check "slotLookup: first occurrence wins"
    (slotLookup ["x", "y", "x"] [Value.int 4, Value.int 5, Value.int 6] "x" == some 4
      && slotLookup ["x", "y"] [Value.int 4, Value.int 5] "y" == some 5
      && slotLookup ["x"] [Value.int 4] "z" == none)
  -- the objective gate: slot objective sanctioned, boolean slot not,
  -- initialized variable not
  st ← st.check "slotObjFn: integer slot sanctioned"
    (match slotObjFn ["x"] [[.int 1, .int 2]] (.ident (Ident.mk "x")) with
     | some f => f [Value.int 2] == some 2
     | none => false)
  st ← st.check "slotObjFn: boolean slot refused"
    ((slotObjFn ["b"] [[.bool true, .bool false]] (BasicExpr.ident (Ident.mk "b"))).isNone)
  st ← st.check "slotObjFn: unknown name refused"
    ((slotObjFn ["x"] [[.int 1]] (BasicExpr.ident (Ident.mk "w"))).isNone)
  st ← st.check "slotObjFn: integer literal sanctioned"
    (match slotObjFn [] [] (.lit (.int 7)) with
     | some f => f [] == some 7
     | none => false)
  st ← st.check "slotObjFn: boolean literal refused"
    ((slotObjFn [] [] (BasicExpr.lit (BasicLiteral.bool true))).isNone)

  -- ## Unit tests: the best pick

  -- minimize: picks the smallest value
  st ← st.check "pickBest: minimize picks smallest"
    (pickBest true [("a", 5), ("b", 2), ("c", 9)] == some ("b", 2))
  -- maximize: picks the largest value
  st ← st.check "pickBest: maximize picks largest"
    (pickBest false [("a", 5), ("b", 2), ("c", 9)] == some ("c", 9))
  -- negative values
  st ← st.check "pickBest: negative values"
    (pickBest true [("a", -5), ("b", -2)] == some ("a", -5)
      && pickBest false [("a", -5), ("b", -2)] == some ("b", -2))
  -- ties keep the tail's winner
  st ← st.check "pickBest: tie keeps later pair"
    (pickBest true [("a", 2), ("b", 2)] == some ("b", 2))
  -- empty list: none
  st ← st.check "pickBest: empty gives none" (pickBest true [] == none)
  -- single pair
  st ← st.check "pickBest: singleton"
    (pickBest true [("a", 3)] == some ("a", 3))
  -- minimality re-verified by brute force on a battery of lists
  let mut okPick := true
  for min in [true, false] do
    for l in [[("a", 5), ("b", 2), ("c", 9)], [("a", 0), ("b", 0)],
              [("a", 4), ("b", 7), ("c", 1), ("d", 3)]] do
      match pickBest min l with
      | none => okPick := false
      | some p =>
          for q in l do
            if min && p.2 > q.2 then okPick := false
            if !min && q.2 > p.2 then okPick := false
  st ← st.check "pickBest: brute-force minimality battery" okPick

  -- ## End-to-end: minimize x under x ≤ y (optimum 1)

  let m1 := parseOrPanic
    "var 1..9: x;\nvar 1..9: y;\nconstraint int_le(x, y);\nsolve minimize x;"
  match optimizeModel m1 with
  | .optimal text v =>
      st ← st.check "opt: minimize x accepted by checker"
        (checkModelSolution m1 text == .accepted)
      st ← st.check "opt: minimize x optimum value" (v == 1)
      st ← st.check "opt: minimize x text assigns x = 1" (text.contains "x = 1;")
  | _ => st ← st.check "opt: minimize x solved" (false)
  -- the B&B entry point agrees
  match optimizeModelBb m1 with
  | .optimal text v =>
      st ← st.check "bb: minimize x accepted by checker"
        (checkModelSolution m1 text == .accepted)
      st ← st.check "bb: minimize x optimum value" (v == 1)
  | _ => st ← st.check "bb: minimize x solved" (false)
  -- brute-force cross-check (the optimality theorem's conclusion)
  st ← st.check "opt: minimize x matches brute force"
    (bruteForceOpt m1 true == some 1 && (bruteForceOpt m1 true).isSome)
  st ← st.check "bb agrees with reference: minimize x"
    (match optimizeModel m1, optimizeModelBb m1 with
     | .optimal _ v1, .optimal _ v2 => v1 == v2
     | _, _ => false)

  -- ## End-to-end: sum objective via an auxiliary constrained variable
  --    s = x + y, minimize s: every (x, y) with x, y ≥ 1 has s ≥ 2

  let m2 := parseOrPanic
    "var 1..9: x;\nvar 1..9: y;\nvar 0..18: s;\nconstraint int_plus(x, y, s);\n\
     solve minimize s;"
  match optimizeModel m2 with
  | .optimal text v =>
      st ← st.check "opt: minimize s accepted by checker"
        (checkModelSolution m2 text == .accepted)
      st ← st.check "opt: minimize s optimum value" (v == 2)
      st ← st.check "opt: minimize s text assigns x = 1 and y = 1"
        (text.contains "x = 1;" && text.contains "y = 1;" && text.contains "s = 2;")
  | _ => st ← st.check "opt: minimize s solved" (false)
  match optimizeModelBb m2 with
  | .optimal text v =>
      st ← st.check "bb: minimize s accepted by checker"
        (checkModelSolution m2 text == .accepted)
      st ← st.check "bb: minimize s optimum value" (v == 2)
  | _ => st ← st.check "bb: minimize s solved" (false)
  st ← st.check "opt: minimize s matches brute force"
    (bruteForceOpt m2 true == some 2)
  st ← st.check "bb agrees with reference: minimize s"
    (match optimizeModel m2, optimizeModelBb m2 with
     | .optimal _ v1, .optimal _ v2 => v1 == v2
     | _, _ => false)

  -- ## End-to-end: maximization

  let m3 := parseOrPanic
    "var 1..5: x;\nvar 1..5: y;\nconstraint int_le(x, y);\nsolve maximize x;"
  match optimizeModel m3 with
  | .optimal text v =>
      st ← st.check "opt: maximize x accepted by checker"
        (checkModelSolution m3 text == .accepted)
      st ← st.check "opt: maximize x optimum value" (v == 5)
  | _ => st ← st.check "opt: maximize x solved" (false)
  match optimizeModelBb m3 with
  | .optimal text v =>
      st ← st.check "bb: maximize x accepted by checker"
        (checkModelSolution m3 text == .accepted)
      st ← st.check "bb: maximize x optimum value" (v == 5)
  | _ => st ← st.check "bb: maximize x solved" (false)
  st ← st.check "opt: maximize x matches brute force"
    (bruteForceOpt m3 false == some 5)
  st ← st.check "bb agrees with reference: maximize x"
    (match optimizeModel m3, optimizeModelBb m3 with
     | .optimal _ v1, .optimal _ v2 => v1 == v2
     | _, _ => false)

  -- ## End-to-end: a forced optimum (unique accepted assignment)

  let m4 := parseOrPanic
    "var 1..5: x;\nconstraint int_eq(x, 3);\nsolve minimize x;"
  match optimizeModel m4 with
  | .optimal text v =>
      st ← st.check "opt: forced optimum accepted"
        (checkModelSolution m4 text == .accepted)
      st ← st.check "opt: forced optimum value" (v == 3)
  | _ => st ← st.check "opt: forced optimum solved" (false)
  st ← st.check "bb agrees with reference: forced optimum"
    (sameVerdict (optimizeModel m4) (optimizeModelBb m4)
      && match optimizeModel m4, optimizeModelBb m4 with
         | .optimal _ v1, .optimal _ v2 => v1 == v2
         | _, _ => false)

  -- ## End-to-end: maximizing the negative (optimum is negative)

  let m5 := parseOrPanic
    "var -5..-1: x;\nsolve maximize x;"
  match optimizeModel m5 with
  | .optimal text v =>
      st ← st.check "opt: negative domain accepted"
        (checkModelSolution m5 text == .accepted)
      st ← st.check "opt: negative domain optimum" (v == -1)
  | _ => st ← st.check "opt: negative domain solved" (false)
  match optimizeModelBb m5 with
  | .optimal _ v => st ← st.check "bb: negative domain optimum" (v == -1)
  | _ => st ← st.check "bb: negative domain solved" (false)

  -- ## UNSAT optimization model

  let u1 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve minimize x;"
  match optimizeModel u1 with
  | .unsat =>
      st ← st.check "opt: unsat optimization model" true
      -- brute-force cross-check: no accepted assignment at all
      let ok := (allAssigns (slotDomains u1)).all (fun asg =>
        checkModelSolution u1 (emitAssignment (slotNames u1) asg) != .accepted)
      st ← st.check "opt: unsat brute force agrees" ok
  | _ => st ← st.check "opt: unsat optimization model" (false)
  match optimizeModelBb u1 with
  | .unsat => st ← st.check "bb: unsat optimization model" true
  | _ => st ← st.check "bb: unsat optimization model" (false)

  -- UNSAT through the objective only being satisfiable vacuously:
  -- empty domain slot
  let u2 := parseOrPanic "var 11..10: x;\nsolve minimize x;"
  match optimizeModel u2 with
  | .unsat => st ← st.check "opt: empty domain optimization unsat" true
  | _ => st ← st.check "opt: empty domain optimization unsat" (false)
  match optimizeModelBb u2 with
  | .unsat => st ← st.check "bb: empty domain optimization unsat" true
  | _ => st ← st.check "bb: empty domain optimization unsat" (false)

  -- ## Satisfy models are refused

  let s1 := parseOrPanic "var 1..3: x;\nsolve satisfy;"
  match optimizeModel s1, optimizeModelBb s1 with
  | .unsupported r1, .unsupported r2 =>
      st ← st.check "opt: satisfy model refused"
        (r1.contains "satisfaction" && r2.contains "satisfaction")
  | _, _ => st ← st.check "opt: satisfy model refused" (false)

  -- ## Objective-scope refusals

  -- parameter objective: not a search slot (the objective-scope refusal)
  let s2 := parseOrPanic "int: c = 3;\nsolve minimize c;"
  match optimizeModel s2 with
  | .unsupported r =>
      st ← st.check "opt: parameter objective refused" (r.contains "objective")
  | _ => st ← st.check "opt: parameter objective refused" (false)
  match optimizeModelBb s2 with
  | .unsupported r =>
      st ← st.check "bb: parameter objective refused" (r.contains "objective")
  | _ => st ← st.check "bb: parameter objective refused" (false)

  -- boolean objective: ill-formed under R7 (the objective must be int),
  -- refused at the well-formedness gate
  let s2b := parseOrPanic "var bool: b;\nsolve minimize b;"
  match optimizeModel s2b with
  | .unsupported _ => st ← st.check "opt: boolean objective refused" true
  | _ => st ← st.check "opt: boolean objective refused" (false)
  match optimizeModelBb s2b with
  | .unsupported _ => st ← st.check "bb: boolean objective refused" true
  | _ => st ← st.check "bb: boolean objective refused" (false)

  -- initialized variable objective: not a search slot
  let s3 := parseOrPanic "var 1..3: x = 2;\nsolve minimize x;"
  match optimizeModel s3 with
  | .unsupported r =>
      st ← st.check "opt: initialized objective refused" (r.contains "objective")
  | _ => st ← st.check "opt: initialized objective refused" (false)
  match optimizeModelBb s3 with
  | .unsupported r =>
      st ← st.check "bb: initialized objective refused" (r.contains "objective")
  | _ => st ← st.check "bb: initialized objective refused" (false)

  -- ## Unsupported gates (mirror solveModel's refusals)

  -- unsupported global
  let s4 := parseOrPanic
    "var 1..4: u;\nvar 1..4: v;\nconstraint fzn_span([u, v]);\nsolve minimize u;"
  match optimizeModel s4 with
  | .unsupported r => st ← st.check "opt: fzn_span unsupported" (r.contains "fzn_span")
  | _ => st ← st.check "opt: fzn_span unsupported" (false)
  -- unbounded var int
  let s5 := parseOrPanic "var int: x;\nsolve minimize x;"
  match optimizeModel s5 with
  | .unsupported r => st ← st.check "opt: unbounded var int unsupported" (r.contains "finite")
  | _ => st ← st.check "opt: unbounded var int unsupported" (false)
  -- ill-formed model (duplicate declaration)
  let s6 := parseOrPanic "var 1..3: x;\nvar 1..3: x;\nsolve minimize x;"
  match optimizeModel s6 with
  | .unsupported _ => st ← st.check "opt: ill-formed unsupported" true
  | _ => st ← st.check "opt: ill-formed unsupported" (false)
  -- the B&B gates agree with the reference on refusals
  st ← st.check "bb: refusal gates agree with reference"
    (sameVerdict (optimizeModel s4) (optimizeModelBb s4)
      && sameVerdict (optimizeModel s5) (optimizeModelBb s5)
      && sameVerdict (optimizeModel s6) (optimizeModelBb s6))

  -- ## All-solutions battery: every solvable model above, both
  --    optimizers agree on the verdict and the value

  let models : List String :=
    [ "var 1..9: x;\nvar 1..9: y;\nconstraint int_le(x, y);\nsolve minimize x;"
    , "var 1..9: x;\nvar 1..9: y;\nconstraint int_le(x, y);\nsolve maximize x;"
    , "var 1..5: x;\nconstraint int_eq(x, 3);\nsolve minimize x;"
    , "var -5..-1: x;\nsolve maximize x;"
    , "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve minimize x;"
    , "var bool: b;\nsolve minimize b;"
    , "var 1..3: x;\nsolve satisfy;" ]
  let mut idx := 0
  for src in models do
    idx := idx + 1
    let m := parseOrPanic src
    st ← st.check s!"bb agrees with reference: battery {idx}"
      (sameVerdict (optimizeModel m) (optimizeModelBb m)
        && match optimizeModel m, optimizeModelBb m with
           | .optimal _ v1, .optimal _ v2 => v1 == v2
           | .unsat, .unsat => true
           | .unsupported _, .unsupported _ => true
           | _, _ => false)
    -- where an optimum exists, it matches brute force
    match optimizeModel m with
    | .optimal _ v =>
        let isMin := match m.solve with
          | .minimize _ _ => true
          | _ => false
        st ← st.check s!"opt: battery {idx} matches brute force"
          (bruteForceOpt m isMin == some v)
    | _ => pure ()

  -- ## The master theorems' conclusions re-verified by brute force

  -- for the minimize-x model: every accepted assignment has
  -- objective ≥ the reported optimum (optimizeModel_optimal)
  match optimizeModel m1 with
  | .optimal _ v =>
      let ok := (allAssigns (slotDomains m1)).all (fun asg =>
        if checkModelSolution m1 (emitAssignment (slotNames m1) asg) == .accepted then
          match slotObjective m1 (slotNames m1) asg with
          | some v' => v <= v'
          | none => false
        else true)
      st ← st.check "opt: optimality re-verified by brute force" ok
  | _ => st ← st.check "opt: minimality brute force" (false)
  -- same for the B&B entry point (optimizeModelBb_optimal)
  match optimizeModelBb m1 with
  | .optimal _ v =>
      let ok := (allAssigns (slotDomains m1)).all (fun asg =>
        if checkModelSolution m1 (emitAssignment (slotNames m1) asg) == .accepted then
          match slotObjective m1 (slotNames m1) asg with
          | some v' => v <= v'
          | none => false
        else true)
      st ← st.check "bb: optimality re-verified by brute force" ok
  | _ => st ← st.check "bb: minimality brute force" (false)
  -- and the maximize model (optimizeModelBb_optimal, maximize direction)
  match optimizeModelBb m3 with
  | .optimal _ v =>
      let ok := (allAssigns (slotDomains m3)).all (fun asg =>
        if checkModelSolution m3 (emitAssignment (slotNames m3) asg) == .accepted then
          match slotObjective m3 (slotNames m3) asg with
          | some v' => v' <= v
          | none => false
        else true)
      st ← st.check "bb: maximization optimality re-verified" ok
  | _ => st ← st.check "bb: maximality brute force" (false)

  if st.failed == 0 then
    IO.println s!"passed {st.passed} optimization tests"
    return 0
  else
    IO.eprintln s!"{st.failed} optimization tests FAILED ({st.passed} passed)"
    return 1
