import solver.Solver

/-!
# Enumeration tests (PLAN.md 6.7, part 1)

Tests the all-solutions enumeration of `solver/Enum.lean`:

* unit tests on `enumerateAll`: generic slot lists with 0, 1, and
  many solutions; empty-domain slots; no slots; leaf-always-false;
  duplicate-free results (the distinctness guarantee of
  `enumerateAll_nodup` re-verified by a pairwise scan on every
  instance);
* end-to-end tests through `enumModel`: small FlatZinc models
  (int_plus sum, fzn_all_different_int, Boolean connectives), each
  reported text re-checked with the verified checker, the count
  cross-checked against brute-force enumeration over `allAssigns`,
  an UNSAT model (empty report), a duplicated-domain model (the
  deduplicated one-element domain), and the unsupported gates
  (fzn_span, unbounded var, ill-formed);
* the master theorems are instantiated on the actual outcomes the
  way `solver/TestsHeur.lean` does (the theorem's conclusions are
  re-verified by brute force).
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

/-- Pairwise-distinctness of a list of strings, by brute force
    (used to re-verify `enumerateAll_nodup`/`enumModel_nodup`). -/
private def pairwiseDistinct (l : List String) : Bool :=
  l.all (fun x => l.count x == 1)

/-- Brute-force all-solutions count through the checker: the number
    of complete assignments of the given slot domains whose emitted
    text the checker accepts. -/
private def bruteForceCount (m : Model) (names : List String)
    (doms : List (List Value)) : Nat :=
  ((allAssigns doms).filter (fun asg =>
    checkModelSolution m (emitAssignment names asg) == .accepted)).length

def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Unit tests: enumerateAll on generic slot lists

  -- two solutions of x + y == 5, in search order
  st ← st.check "enumerateAll: two solutions in order"
    (enumerateAll (fun l => match l with
      | [a, b] => a + b == (5 : Int)
      | _ => false) ([[1, 2, 3], [3, 4]] : List (List Int)) []
      == [[1, 4], [2, 3]])
  -- no solution: leaf always false
  st ← st.check "enumerateAll: leaf always false gives []"
    (enumerateAll (fun _ => false) ([[1, 2], [10, 20]] : List (List Int)) [] == [])
  -- all four assignments pass
  st ← st.check "enumerateAll: leaf always true gives all"
    (enumerateAll (fun _ => true) ([[1, 2], [10, 20]] : List (List Int)) []
      == [[1, 10], [1, 20], [2, 10], [2, 20]])
  -- empty-domain slot: no assignment at all
  st ← st.check "enumerateAll: empty domain gives []"
    (enumerateAll (fun _ => true) ([[], [1]] : List (List Int)) [] == [])
  -- no slots: the empty assignment, leaf decides
  st ← st.check "enumerateAll: no slots, leaf true"
    (enumerateAll (fun l => l == []) ([] : List (List Int)) [] == [[]])
  st ← st.check "enumerateAll: no slots, leaf false"
    (enumerateAll (fun _ => false) ([] : List (List Int)) [] == [])
  -- one solution among three
  st ← st.check "enumerateAll: one of three"
    (enumerateAll (fun l => l == [2]) ([[1, 2, 3]] : List (List Int)) [] == [[2]])
  -- agreement with the declarative spec on a mixed battery:
  -- reported set = { a ∈ allAssigns | leaf a } and all distinct
  let leafMix : List Int → Bool := fun l => match l with
    | [a, b, c] => a + b == c && c != 4
    | _ => false
  let mixSlots : List (List Int) := [[1, 2], [2, 3], [3, 4]]
  let res := enumerateAll leafMix mixSlots []
  st ← st.check "enumerateAll: agreement with allAssigns filter"
    ((res.length == ((allAssigns mixSlots).filter leafMix).length) &&
      res.all (fun a => (allAssigns mixSlots).contains a && leafMix a))
  st ← st.check "enumerateAll: results distinct"
    (pairwiseDistinct (res.map toString))
  -- the membership theorem instantiated on the outcome (brute-force
  -- re-verification of both directions)
  let mut okMem := true
  for a in allAssigns mixSlots do
    if leafMix a then
      okMem := okMem && res.contains a
  st ← st.check "enumerateAll: every satisfying assignment reported" okMem

  -- ## End-to-end: enumModel on FlatZinc models

  -- int_plus on small domains: all (x, y) with x + y == 5
  let m1 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  match enumModel m1 with
  | .sat texts =>
      -- every text is checker-accepted (enumModel_sat_sound's conclusion)
      let mut okAcc := true
      for t in texts do
        okAcc := okAcc && (checkModelSolution m1 t == .accepted)
      st ← st.check "enum: int_plus every text accepted" okAcc
      -- count matches brute force: (1,4)? no — domains 1..3: (2,3),(3,2) → 2
      let brute := bruteForceCount m1 ["x", "y"] [[.int 1, .int 2, .int 3],
        [.int 1, .int 2, .int 3]]
      st ← st.check "enum: int_plus count matches brute force"
        (texts.length == brute && brute == 2)
      -- completeness (enumModel_complete's conclusion, brute force)
      let mut okComp := true
      for asg in allAssigns [[.int 1, .int 2, .int 3], [.int 1, .int 2, .int 3]] do
        if checkModelSolution m1 (emitAssignment ["x", "y"] asg) == .accepted then
          okComp := okComp && texts.contains (emitAssignment ["x", "y"] asg)
      st ← st.check "enum: int_plus completeness" okComp
      -- distinctness (enumModel_nodup's conclusion)
      st ← st.check "enum: int_plus texts distinct" (pairwiseDistinct texts)
  | _ => st ← st.check "enum: int_plus model enumerated" (false)

  -- fzn_all_different_int on 3 vars with a forcing constraint:
  -- x ≤ 1 and all different → x = 1, {y, z} = {2, 3}
  let m2 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
     constraint fzn_all_different_int([x, y, z]);\n\
     constraint int_le(x, 1);\nsolve satisfy;"
  match enumModel m2 with
  | .sat texts =>
      let mut okAcc := true
      for t in texts do
        okAcc := okAcc && (checkModelSolution m2 t == .accepted)
      st ← st.check "enum: alldiff every text accepted" okAcc
      st ← st.check "enum: alldiff count matches brute force"
        (texts.length == bruteForceCount m2 ["x", "y", "z"]
          [[.int 1, .int 2, .int 3], [.int 1, .int 2, .int 3], [.int 1, .int 2, .int 3]]
          && texts.length == 2)
      st ← st.check "enum: alldiff texts distinct" (pairwiseDistinct texts)
  | _ => st ← st.check "enum: alldiff model enumerated" (false)

  -- Boolean connectives: bool_and(a, b, true) has the unique solution
  let m3 := parseOrPanic
    "var bool: a;\nvar bool: b;\nconstraint bool_and(a, b, true);\nsolve satisfy;"
  match enumModel m3 with
  | .sat texts =>
      st ← st.check "enum: bool unique solution"
        (texts.length == 1 && texts.head? == some "a = true;\nb = true;\n----------")
      st ← st.check "enum: bool text accepted"
        (checkModelSolution m3 (texts.head?.getD "") == .accepted)
  | _ => st ← st.check "enum: bool model enumerated" (false)

  -- duplicated enumerated domain: var {1, 1} behaves as one value,
  -- reported exactly once (the dedup guarantee)
  let m4 := parseOrPanic "var {1, 1}: x;\nsolve satisfy;"
  match enumModel m4 with
  | .sat texts =>
      st ← st.check "enum: duplicated domain deduped"
        (texts.length == 1 && checkModelSolution m4 (texts.head?.getD "") == .accepted)
  | _ => st ← st.check "enum: duplicated domain enumerated" (false)

  -- UNSAT: int_plus impossible on the domains
  let u1 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
  match enumModel u1 with
  | .unsat =>
      st ← st.check "enum: unsat model reported unsat" true
      -- brute-force cross-check through the checker
      let ok := (allAssigns [[.int 1, .int 2], [.int 1, .int 2]]).all (fun asg =>
        checkModelSolution u1 (emitAssignment ["x", "y"] asg) != .accepted)
      st ← st.check "enum: unsat brute force agrees" ok
  | _ => st ← st.check "enum: unsat model reported unsat" (false)

  -- UNSAT: contradictory constraints
  let u2 := parseOrPanic
    "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;"
  match enumModel u2 with
  | .unsat => st ← st.check "enum: contradictory model unsat" true
  | _ => st ← st.check "enum: contradictory model unsat" (false)

  -- UNSAT: empty domain slot
  let u3 := parseOrPanic "var 11..10: x;\nsolve satisfy;"
  match enumModel u3 with
  | .unsat => st ← st.check "enum: empty domain unsat" true
  | _ => st ← st.check "enum: empty domain unsat" (false)

  -- ## Unsupported gates (mirror solveModel's refusals)

  -- unsupported global (fzn_span needs optional variables)
  let s1 := parseOrPanic
    "var 1..4: u;\nvar 1..4: v;\nconstraint fzn_span([u, v]);\nsolve satisfy;"
  match enumModel s1 with
  | .unsupported r => st ← st.check "enum: fzn_span unsupported" (r.contains "fzn_span")
  | _ => st ← st.check "enum: fzn_span unsupported" (false)

  -- unbounded var int
  let s2 := parseOrPanic "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
  match enumModel s2 with
  | .unsupported r => st ← st.check "enum: unbounded var int unsupported" (r.contains "finite")
  | _ => st ← st.check "enum: unbounded var int unsupported" (false)

  -- ill-formed model (duplicate declaration)
  let s3 := parseOrPanic "var 1..3: x;\nvar 1..3: x;\nsolve satisfy;"
  match enumModel s3 with
  | .unsupported _ => st ← st.check "enum: ill-formed unsupported" true
  | _ => st ← st.check "enum: ill-formed unsupported" (false)

  -- ## Agreement with solveModel: sat/unsat outcomes coincide

  let models : List String :=
    [ "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
    , "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
    , "var bool: a;\nvar bool: b;\nconstraint bool_and(a, b, true);\nsolve satisfy;"
    , "var 1..2: x;\nvar 1..2: y;\nconstraint fzn_all_different_int([x, y]);\nsolve satisfy;" ]
  let mut idx := 0
  for src in models do
    idx := idx + 1
    let m := parseOrPanic src
    let enumSat := match enumModel m with | .sat _ => true | _ => false
    let solveSat := match solveModel m with | .sat _ => true | _ => false
    st ← st.check s!"enum: agreement with solveModel instance {idx}"
      (enumSat == solveSat)

  if st.failed == 0 then
    IO.println s!"passed {st.passed} enumeration tests"
    return 0
  else
    IO.eprintln s!"{st.failed} enumeration tests FAILED ({st.passed} passed)"
    return 1
