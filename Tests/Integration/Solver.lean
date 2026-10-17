import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
import LeanFzn.Integration.Chronological
import LeanFzn.Integration.ReferenceCorrectness
import LeanFzn.Integration.CertifiedSolve
import LeanFzn.Integration.Certified
import LeanFzn.Integration.Lcg
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


/-!
# Solver test executable (the certified path)

Tests the certified LeanFzn.Solver stack end to end:

* `allAssigns` on small slot lists (the declarative specification
  shared by the exhaustive reference search and the LCG layer);
* `search` finds and misses assignments (the executable shared
  search);
* the DIRECT certified-fragment compiler (`compileModel`) on SAT,
  UNSAT, and unsupported models, including theorem-level nonvacuity
  of `solve_sat_correct` / `solve_unsat_correct` (the direct
  exhaustive reference LeanFzn.Solver, retained as internal cross-check);
* the CERTIFIED LCG command path (`solveCertified`) on the singleton
  fragment: SAT stores, emitted text accepted by the verified
  checker, UNSAT verdicts, fragment refusals, and theorem-level
  nonvacuity of `solveCertified_sat_correct` /
  `solveCertified_unsat_correct`.

The legacy checker-mediated LeanFzn.Solver tests (propagation, MRV,
restarts, NoGood learning, enumeration, optimization) were retired
with the legacy LeanFzn.Solver stack (PLAN.md §1); Git history keeps them.
-/

open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Solver LeanFzn.Checker LeanFzn.Checker.Solution LeanFzn.Semantics.Globals

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

-- The test block is long (the C1–C5 family checks all live in one `main`
-- `do` block); raise the elaborator's recursion budget for it (an
-- elaboration-only setting; no semantic effect). PLAN C9 remainder:
-- the two-element array-shape checks grew the block past the 200k
-- heartbeat budget of the LCNF compiler step, hence the disabled
-- heartbeat bound (like the other long test drivers).
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }

  -- ## Unit tests: allAssigns (the specification)

  -- all assignments of two two-value slots, in the search's order
  st ← st.check "allAssigns: two 2-value slots"
    (allAssigns ([[1, 2], [10, 20]] : List (List Int)) ==
      [[1, 10], [2, 10], [1, 20], [2, 20]])
  -- an empty slot admits no assignment
  st ← st.check "allAssigns: empty domain slot"
    (allAssigns ([[], [1]] : List (List Int)) == [])
  -- no slots: the single empty assignment
  st ← st.check "allAssigns: no slots"
    (allAssigns ([] : List (List Int)) == [[]])

  -- ## Unit tests: search (the executable)

  -- finds the first assignment passing the leaf, in order
  st ← st.check "search: first hit in order"
    (search (fun l => l == [1, 20]) ([[1, 2], [10, 20]] : List (List Int)) []
      == some [1, 20])
  -- no assignment passes: none
  st ← st.check "search: none when leaf always fails"
    (search (fun _ => false) ([[1, 2], [10, 20]] : List (List Int)) [] == none)
  -- an empty domain slot makes the subtree unsatisfiable
  st ← st.check "search: empty domain gives none"
    (search (fun _ => true) ([[], [1]] : List (List Int)) [] == none)
  -- no slots: the leaf decides on the empty assignment
  st ← st.check "search: no slots, leaf true"
    (search (fun l => l == []) ([] : List (List Int)) [] == some [])
  st ← st.check "search: no slots, leaf false"
    (search (fun _ => false) ([] : List (List Int)) [] == none)
  -- completeness on a tiny instance: search finds an assignment iff
  -- some assignment in allAssigns passes the leaf
  let leaf : List Int → Bool := fun l => match l with
    | [a, b] => a + b == 5
    | _ => false
  let slots : List (List Int) := [[1, 2, 3], [3, 4]]
  let searchHit := (search leaf slots []).isSome
  let specHit := (allAssigns slots).any leaf
  st ← st.check "search vs allAssigns agreement"
    (searchHit == specHit && searchHit)


  -- ## Phase 2: the DIRECT certified-fragment compiler (nonvacuous tests)

  -- SAT: int_plus on two 1..3 slots (accepted fragment, solved by search)
  let d1 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModel d1 with
  | .error e => st ← st.check "direct: int_plus model compiles" (false)
  | .ok problem =>
      st ← st.check "direct: int_plus model compiles" (true)
      st ← st.check "direct: problem has two slots"
        (problem.domains.length == 2)
      st ← st.check "direct: problem has one constraint"
        (problem.constraints.length == 1)
      match LeanFzn.Solver.Reference.solveCompiled problem with
      | some a =>
          st ← st.check "direct: int_plus finds a summing pair" (a.length == 2)
          match a[0]!, a[1]! with
          | .int p, .int q =>
              st ← st.check "direct: found pair sums to 5" (p + q == 5)
          | _, _ => st ← st.check "direct: found pair sums to 5" (false)
      | none => st ← st.check "direct: int_plus finds a summing pair" (false)

  -- SAT verification standalone re-check
  match LeanFzn.Compiler.compileModel d1 with
  | .ok problem =>
      match LeanFzn.Solver.Reference.solveCompiled problem with
      | some a =>
          match a[0]!, a[1]! with
          | .int p, .int q =>
              st ← st.check "direct: found pair sums to 5 (recheck)" (p + q == 5)
          | _, _ => st ← st.check "direct: found pair sums to 5 (recheck)" (false)
      | none => st ← st.check "direct: found pair sums to 5 (recheck)" (false)
  | .error _ => st ← st.check "direct: found pair sums to 5 (recheck)" (false)

  -- UNSAT: int_plus on two 1..2 slots with sum 10 (impossible)
  let d2 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModel d2 with
  | .error _ => st ← st.check "direct: impossible sum compiles" (false)
  | .ok problem =>
      st ← st.check "direct: impossible sum compiles" (true)
      st ← st.check "direct: impossible sum yields no assignment"
        (LeanFzn.Solver.Reference.solveCompiled problem == none)

  -- UNSAT: contradictory bounds (int_le and int_gt on one slot)
  let d3 := parseOrPanic
    "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModel d3 with
  | .error _ => st ← st.check "direct: contradictory bounds compiles" (false)
  | .ok problem =>
      st ← st.check "direct: contradictory bounds compiles" (true)
      st ← st.check "direct: contradictory bounds yields no assignment"
        (LeanFzn.Solver.Reference.solveCompiled problem == none)

  -- unsupported: unbounded var int is rejected with a reason
  let d4 := parseOrPanic
    "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
  let ok4 := match LeanFzn.Compiler.compileModel d4 with
    | .error e => e.contains "unbounded" || e.contains "outside"
    | .ok _ => false
  st ← st.check "direct: unbounded var rejected" ok4

  -- unsupported: predicate items are outside the certified fragment
  let d5 := parseOrPanic
    "predicate p(int: a);\nvar 1..3: x;\nsolve satisfy;"
  let ok5 := match LeanFzn.Compiler.compileModel d5 with
    | .error e => e.contains "predicate"
    | .ok _ => false
  st ← st.check "direct: predicate items rejected" ok5

  -- unsupported: globals not in the extractable set
  let d6 := parseOrPanic
    "var 1..3: x;\nconstraint fzn_all_different_int([x]);\nsolve satisfy;"
  let ok6 := match LeanFzn.Compiler.compileModel d6 with
    | .error e => e.contains "unsupported"
    | .ok _ => false
  st ← st.check "direct: fzn_ globals rejected" ok6

  -- Public LCG acceptance on large finite domains: equality propagation
  -- should select a late witness before enumerating complete assignments.
  let d7 := parseOrPanic
    "var 0..10000: x;\nconstraint int_eq(x, 9999);\nsolve satisfy;"
  let enumerated := String.intercalate ", " ((List.range 2048).map toString)
  let d8 := parseOrPanic
    ("var {" ++ enumerated ++ "}: x;\nconstraint int_eq(x, 2047);\nsolve satisfy;")
  let d9 := parseOrPanic
    "var 0..1000: x;\nvar 0..1000: y;\nconstraint int_eq(x, 999);\n\
     constraint int_eq(y, 998);\nsolve satisfy;"
  for (label, model, expectedLeaves) in
      [("large finite range", d7, 10001),
       ("large enumerated domain", d8, 2048),
       ("large finite product", d9, 1002001)] do
    match LeanFzn.Compiler.compileModel model with
    | .error e =>
        st ← st.check s!"lcg public: {label} compiles" false
        IO.eprintln s!"unexpected rejection: {e}"
    | .ok problem =>
        st ← st.check s!"lcg public: {label} retains the declared domains"
          (leavesProduct problem.domains == expectedLeaves)
        let measured := LeanFzn.Integration.solveDomWithStats
          (LeanFzn.Integration.toLCG problem)
        st ← st.check s!"lcg public: {label} propagates to one checked leaf"
          (measured.2.propagations > 0 && measured.2.checkedLeaves == 1)
        match LeanFzn.Integration.solveCertified model with
        | .sat store =>
            st ← st.check s!"lcg public: {label} emits a checker-accepted solution"
              (checkModelSolution model
                (LeanFzn.Integration.emitCertifiedSolution model store) == .accepted)
        | _ =>
            st ← st.check s!"lcg public: {label} emits a checker-accepted solution" false

  -- THEOREM-LEVEL nonvacuity: solve_sat_correct applies to a real
  -- solved model (the kernel checks the composed chain end to end).
  -- The models are built as terms so the well-formedness proofs
  -- reduce by native evaluation.
  let dsat : Model :=
    { predicates := []
      parameters := []
      variables :=
        [ .basic (.intRange 1 3) (Ident.mk "x") [] none
        , .basic (.intRange 1 3) (Ident.mk "y") [] none ]
      constraints :=
        [ { name := Ident.mk "int_plus"
          , args := [ .basic (.ident (Ident.mk "x"))
                    , .basic (.ident (Ident.mk "y"))
                    , .basic (.lit (.int 5)) ]
          , anns := [] } ]
      solve := .satisfy [] }
  have wsat : WellFormed fullSig dsat :=
    (LeanFzn.Checker.wellFormedFastB_iff dsat).mp (by native_decide)
  match hsolve : LeanFzn.Solver.Reference.solve dsat with
  | .sat store =>
      -- run the certified theorem on the actual verdict
      have _hsat : Satisfies fullSig fullInterp dsat store :=
        LeanFzn.Integration.Reference.solve_sat_correct
          (model := dsat) (store := store) wsat hsolve
      st ← st.check "direct theorem: solve_sat_correct applies" (true)
      -- the satisfying store's constraints hold (executable twin)
      st ← st.check "direct theorem: sat store satisfies constraints"
        (dsat.constraints.all (fun c =>
          LeanFzn.Semantics.Globals.fullInterpB c.name
            (match c.args.mapM (Expr.eval store) with
             | some args => args
             | none => [])))
  | _ => st ← st.check "direct theorem: solve_sat_correct applies" (false)

  -- THEOREM-LEVEL nonvacuity: solve_unsat_correct applies
  let dunsat : Model :=
    { predicates := []
      parameters := []
      variables :=
        [ .basic (.intRange 1 2) (Ident.mk "x") [] none
        , .basic (.intRange 1 2) (Ident.mk "y") [] none ]
      constraints :=
        [ { name := Ident.mk "int_plus"
          , args := [ .basic (.ident (Ident.mk "x"))
                    , .basic (.ident (Ident.mk "y"))
                    , .basic (.lit (.int 10)) ]
          , anns := [] } ]
      solve := .satisfy [] }
  have wunsat : WellFormed fullSig dunsat :=
    (LeanFzn.Checker.wellFormedFastB_iff dunsat).mp (by native_decide)
  match hunsolve : LeanFzn.Solver.Reference.solve dunsat with
  | .unsat =>
      have _hunsat : ¬ ∃ store, Satisfies fullSig fullInterp dunsat store ∧
          LeanFzn.Compiler.ParamHonest dunsat store :=
        LeanFzn.Integration.Reference.solve_unsat_correct
          (model := dunsat) wunsat hunsolve
      st ← st.check "direct theorem: solve_unsat_correct applies" (true)
  | _ => st ← st.check "direct theorem: solve_unsat_correct applies" (false)

  -- ## Phase 3: the CERTIFIED LCG command path (nonvacuous tests)

  -- the executable command: SAT on the singleton fragment
  let csat := parseOrPanic
    "var {3}: x;\nvar {2}: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified csat with
  | .sat store =>
      st ← st.check "certified: singleton SAT returns a store" (true)
      -- the store's reads are in the declared domains
      st ← st.check "certified: x reads 3"
        (store (Ident.mk "x") == some (Value.int 3))
      st ← st.check "certified: y reads 2"
        (store (Ident.mk "y") == some (Value.int 2))
      -- the emitted text round-trips through the reference checker
      st ← st.check "certified: emitted text is checker-accepted"
        (checkModelSolution csat
          (LeanFzn.Integration.emitCertifiedSolution csat store)
          == .accepted)
  | _ => st ← st.check "certified: singleton SAT returns a store" (false)

  -- the executable command: UNSAT on the singleton fragment
  let cunsat := parseOrPanic
    "var {2}: x;\nvar {2}: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
  st ← st.check "certified: singleton UNSAT"
    (match LeanFzn.Integration.solveCertified cunsat with
     | .unsat => true
     | _ => false)

  -- multi-value domains: ADMITTED by the widened gate; the engine
  -- decides + backtracks (plusSlot propagator coverage)
  let cfrag := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nconstraint int_plus(x, y, z);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cfrag with
  | .sat store =>
      -- the SAT theorem applies (multi-value!); the store satisfies
      -- the constraint executably: x + y = z on the read values
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      let z := (store (Ident.mk "z")).get!
      st ← st.check "certified: multi-value domain solves by decisions"
        (match x, y, z with
         | .int a, .int b, .int c => a + b == c
         | _, _, _ => false)
      -- the emitted text is checker-accepted
      st ← st.check "certified: multi-value emitted text checker-accepted"
        (checkModelSolution cfrag
          (LeanFzn.Integration.emitCertifiedSolution cfrag store)
          == .accepted)
  | _ => st ← st.check "certified: multi-value domain solves by decisions" (false)

  -- THEOREM-LEVEL nonvacuity on the widened gate: the SAT theorem
  -- applies to a multi-value model (decisions + backtracking)
  have wcfrag : WellFormed fullSig cfrag :=
    (LeanFzn.Checker.wellFormedFastB_iff cfrag).mp (by native_decide)
  match hcres : LeanFzn.Integration.solveCertified cfrag with
  | .sat cstore =>
      have _hcert : Satisfies fullSig fullInterp cfrag cstore :=
        LeanFzn.Integration.solveCertified_sat_correct
          (m := cfrag) (store := cstore) wcfrag hcres
      st ← st.check "certified theorem: multi-value SAT theorem applies" true
      pure ()
  | _ =>
      st ← st.check "certified theorem: multi-value SAT theorem applies" false
      pure ()

  -- multi-value UNSAT (plusSlot + const bounds; no linLe): the
  -- engine refutes AND the wide door certifies the exclusion
  let cmunsat2 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nvar 1..2: z;\nconstraint int_plus(x, y, z);\nconstraint int_le(x, 0);\nsolve satisfy;"
  st ← st.check "certified: multi-value UNSAT (wide door)"
    (match LeanFzn.Integration.solveCertified cmunsat2 with
     | .unsat => true
     | _ => false)

  -- multi-value UNSAT over int_le/int_lt (le/lt slots): the wide
  -- door's core shape
  let cmunsat3 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nconstraint int_le(x, y);\nconstraint int_lt(y, x);\nsolve satisfy;"
  st ← st.check "certified: multi-value UNSAT (le/lt)"
    (match LeanFzn.Integration.solveCertified cmunsat3 with
     | .unsat => true
     | _ => false)

  -- End-to-end frontier regressions: a SAT sibling and the K4 UNSAT
  -- model must both finish, with checker/source-theorem applications.
  let cph3 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\nconstraint int_ne(x, y);\nconstraint int_ne(x, z);\nconstraint int_ne(y, z);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cph3 with
  | .sat store =>
      -- the three reads are pairwise distinct integers (a valid
      -- all-different witness over 0..2)
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      let z := (store (Ident.mk "z")).get!
      st ← st.check "certified: int_ne pigeonhole (3 slots/3 vals) solves SAT"
        (match x, y, z with
         | .int a, .int b, .int c =>
             !(a == b) && !(a == c) && !(b == c) &&
               0 ≤ a && a ≤ 2 && 0 ≤ b && b ≤ 2 && 0 ≤ c && c ≤ 2
         | _, _, _ => false)
      -- the emitted text round-trips through the checker
      st ← st.check "certified: int_ne pigeonhole SAT text checker-accepted"
        (checkModelSolution cph3
          (LeanFzn.Integration.emitCertifiedSolution cph3 store)
          == .accepted)
  | _ => st ← st.check "certified: int_ne pigeonhole (3 slots/3 vals) solves SAT" (false)

  -- Four slots over three values are UNSAT. The pending frontier must
  -- remember exhausted siblings instead of restarting the x=2/1/0 cycle.
  let cph4 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\nvar 0..2: w;\nconstraint int_ne(x, y);\nconstraint int_ne(x, z);\nconstraint int_ne(y, z);\nconstraint int_ne(x, w);\nconstraint int_ne(y, w);\nconstraint int_ne(z, w);\nsolve satisfy;"
  st ← st.check "certified: int_ne pigeonhole (4 slots/3 vals) UNSAT"
    (match LeanFzn.Integration.solveCertified cph4 with
     | .unsat => true
     | _ => false)
  -- THEOREM-LEVEL nonvacuity: the wide-door unsat theorem applies to
  -- the fallback-nogood-refuted pigeonhole
  have wcph4 : WellFormed fullSig cph4 :=
    (LeanFzn.Checker.wellFormedFastB_iff cph4).mp (by native_decide)
  match hph4 : LeanFzn.Integration.solveCertified cph4 with
  | .unsat =>
      have _hph : ¬ ∃ store, Satisfies fullSig fullInterp cph4
          store ∧ LeanFzn.Semantics.ParamHonest cph4 store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := cph4) wcph4 hph4
      st ← st.check "certified theorem: fallback-nogood unsat_correct applies" true
      pure ()
  | _ =>
      st ← st.check "certified theorem: fallback-nogood unsat_correct applies" false
  -- THE BOOL/MIN/MAX/ABS FAMILY REGRESSIONS (PLAN §5 item 3, the
  -- six 2026-10-01 registrations): each model previously
  -- fuel-exhausted or was unsupported; now the propagators drive
  -- the search to a checker-accepted solution
  let cbooland := parseOrPanic
    "var bool: a;\nvar bool: b;\nvar bool: c;\nconstraint bool_and(a, b, c);\nconstraint bool_not(c, a);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cbooland with
  | .sat store =>
      -- a ∧ b = c with c = ¬a: (a=false, b=false, c=false) and
      -- (a=false,b=true,c=false) both work; check the reads agree
      let a := (store (Ident.mk "a")).get!
      let b := (store (Ident.mk "b")).get!
      let c := (store (Ident.mk "c")).get!
      st ← st.check "certified: bool_and+bool_not model solves SAT"
        (match a, b, c with
         | .bool x, .bool y, .bool z =>
             (x && y) == z && z == !x
         | _, _, _ => false)
      st ← st.check "certified: bool model text checker-accepted"
        (checkModelSolution cbooland
          (LeanFzn.Integration.emitCertifiedSolution cbooland store)
          == .accepted)
  | _ => st ← st.check "certified: bool_and+bool_not model solves SAT" (false)

  let cminmax := parseOrPanic
    "var 0..5: x;\nvar 0..5: y;\nvar 0..5: z;\nconstraint int_min(x, y, z);\nconstraint int_max(x, y, x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cminmax with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      let z := (store (Ident.mk "z")).get!
      st ← st.check "certified: int_min/int_max model solves SAT"
        (match x, y, z with
         | .int a, .int b, .int c => min a b == c && max a b == a
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_min/int_max model solves SAT" (false)

  let cabs := parseOrPanic
    "var -5..5: x;\nvar 0..5: r;\nconstraint int_abs(x, r);\nconstraint int_lt(r, 3);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cabs with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let r := (store (Ident.mk "r")).get!
      st ← st.check "certified: int_abs model solves SAT"
        (match x, r with
         | .int a, .int b => LeanFzn.Solver.Propagation.DomainFiltering.absValue a == b && b < 3
         | _, _ => false)
  | _ => st ← st.check "certified: int_abs model solves SAT" (false)

  -- PLAN L7: `int_abs` on the LCG route — the `.absSlot` family is
  -- re-registered with the explained bound propagator `propAbs` (the
  -- A3 obligation triple), so these checks assert the mixed LCG gate
  -- accepts the compiled model and the LCG verdict agrees with
  -- exhaustive enumeration of the declared domains.
  let routeAbs := parseOrPanic
    "var -5..5: x;\nvar 0..5: r;\nconstraint int_abs(x, r);\nconstraint int_lt(r, 3);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAbs with
  | .error _ => st ← st.check "route: int_abs compiles" false
  | .ok cp =>
      st ← st.check "route: int_abs model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_abs: r = |x| at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int rv] =>
              rv == LeanFzn.Solver.Propagation.DomainFiltering.absValue xv
          | _ => false)
      -- r < 3 with r = |x|: r ∈ {0,1,2} and x ∈ {-r, r} gives 5 assignments
      st ← st.check
        "route: int_abs: exactly 5 solutions by enumeration"
        (sols.length == 5)
      st ← st.check "route: int_abs SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  -- the NEGATIVE-operand corner: x ∈ -5..-3 with |x| = 4 forces x = -4
  let routeAbsNeg := parseOrPanic
    "var -5..-3: x;\nvar 0..5: r;\nconstraint int_abs(x, r);\nconstraint int_eq(r, 4);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAbsNeg with
  | .error _ => st ← st.check "route: negative int_abs compiles" false
  | .ok cp =>
      st ← st.check "route: negative int_abs passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: negative int_abs: exactly 1 solution (x = -4) by enumeration"
        (sols == [[.int (-4), .int 4]])
      st ← st.check "route: negative int_abs SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  -- UNSAT: r ≥ 0 always holds for r = |x|, so r < 0 is infeasible
  let routeAbsU := parseOrPanic
    "var -5..5: x;\nvar 0..5: r;\nconstraint int_abs(x, r);\nconstraint int_lt(r, 0);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAbsU with
  | .error _ => st ← st.check "route: int_abs UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: int_abs UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_abs UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_abs UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- PLAN L7: `int_div`/`int_mod` on the LCG route — the `.divGen`/
  -- `.modGen` shapes are re-registered with the explained bound
  -- propagators `propDiv`/`propMod` (their obligation triples live in
  -- `Fam/Arith.lean`), so these checks assert the mixed LCG gate
  -- accepts the compiled models and the LCG verdict agrees with
  -- exhaustive enumeration of the declared domains (the divisor is a
  -- literal or an integer-singleton slot domain, which is what `divPin`
  -- consumes).
  let routeDiv := parseOrPanic
    "var -7..7: x;\nvar 3..3: d;\nvar 0..7: r;\nconstraint int_div(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeDiv with
  | .error _ => st ← st.check "route: int_div compiles" false
  | .ok cp =>
      st ← st.check "route: int_div model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_div: r = truncated quotient at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int dv, .int rv] =>
              dv ≠ 0 && rv == Int.tdiv xv dv
          | _ => false)
      st ← st.check
        "route: int_div: exactly 10 solutions by enumeration"
        (sols.length == 10)
      st ← st.check "route: int_div SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  -- truncation discriminator: with FLOOR division this model is
  -- satisfiable (floor (−1/3) = −1); the truncated reading gives
  -- tdiv(−1,3) = tdiv(−2,3) = 0 ≠ −1, so the route must say UNSAT.
  let routeDivU := parseOrPanic
    "var -2..-1: x;\nvar 3..3: d;\nvar -1..-1: r;\nconstraint int_div(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeDivU with
  | .error _ => st ← st.check "route: int_div truncation compiles" false
  | .ok cp =>
      st ← st.check "route: int_div truncation passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_div truncation UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_div truncation UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  -- the zero-divisor conflict: `d = 0` given by an integer-singleton
  -- slot domain (the `divPin`/`FixExpl` shape `propDiv` conflicts on).
  let routeDivZ := parseOrPanic
    "var 0..0: d;\nvar 1..3: x;\nvar 0..9: r;\nconstraint int_div(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeDivZ with
  | .error _ => st ← st.check "route: int_div zero divisor compiles" false
  | .ok cp =>
      st ← st.check "route: int_div zero divisor passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_div zero divisor UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_div zero divisor UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  -- the LITERAL zero divisor: the empty-clause conflict (`divZeroClause`).
  let routeDivZL := parseOrPanic
    "var 1..3: x;\nvar 0..9: r;\nconstraint int_div(x, 0, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeDivZL with
  | .error _ => st ← st.check "route: int_div literal zero compiles" false
  | .ok cp =>
      st ← st.check "route: int_div literal zero passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_div literal zero UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_div literal zero UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  -- PLAN L7: `int_mod` — the `Int.tmod` sign convention (the remainder
  -- follows the dividend) is the discriminating semantics.
  let routeMod := parseOrPanic
    "var -6..6: x;\nvar 2..2: d;\nvar 0..6: r;\nconstraint int_mod(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMod with
  | .error _ => st ← st.check "route: int_mod compiles" false
  | .ok cp =>
      st ← st.check "route: int_mod model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_mod: r = truncated remainder at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int dv, .int rv] =>
              dv ≠ 0 && rv == Int.tmod xv dv
          | _ => false)
      st ← st.check
        "route: int_mod: exactly 10 solutions by enumeration"
        (sols.length == 10)
      st ← st.check "route: int_mod SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  -- sign discriminator: tmod(−3,2) = −1 (the dividend's sign), so
  -- r = 1 is infeasible (an `emod` reading would return 1 and SAT it).
  let routeModU := parseOrPanic
    "var -3..-3: x;\nvar 2..2: d;\nvar 1..1: r;\nconstraint int_mod(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeModU with
  | .error _ => st ← st.check "route: int_mod sign compiles" false
  | .ok cp =>
      st ← st.check "route: int_mod sign passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_mod sign UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_mod sign UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  -- the tmod sign positively: (−3) mod 2 = −1 is the single solution.
  let routeModS := parseOrPanic
    "var -3..-3: x;\nvar 2..2: d;\nvar -1..-1: r;\nconstraint int_mod(x, d, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeModS with
  | .error _ =>
      st ← st.check "route: int_mod negative remainder compiles" false
  | .ok cp =>
      st ← st.check "route: int_mod negative remainder passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: int_mod negative remainder: (x,d,r) = (−3,2,−1) accepted"
        (sols == [[.int (-3), .int 2, .int (-1)]])
      st ← st.check
        "route: int_mod negative remainder SAT witness on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- the bool UNSAT shape: a ∨ b = c, c = ¬a, a ∧ b = c — jointly
  -- unsatisfiable (c=¬a and a∧b=c force a=b=c and c=¬a)
  let cboolunsat := parseOrPanic
    "var bool: a;\nvar bool: b;\nvar bool: c;\nconstraint bool_or(a, b, c);\nconstraint bool_not(c, a);\nconstraint bool_and(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: bool or+not+and mix is UNSAT"
    (match LeanFzn.Integration.solveCertified cboolunsat with
     | .unsat => true
     | _ => false)

  -- THE LINLE/LINEQ/TIMES/ALLDIFF FAMILY REGRESSIONS (PLAN §5 item 3
  -- completion, 2026-10-02): the fixed propLinLe2's reasons are
  -- state-free valid, so multi-value linLe UNSAT is now CERTIFIED
  -- through the wide door (the linLeFree gate is GONE)
  let clinleu := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_lin_le([1,1],[x,y],2);\nconstraint int_lin_le([1,-1],[y,x],-2);\nsolve satisfy;"
  st ← st.check "certified: multi-value linLe UNSAT (wide door, no gate)"
    (match LeanFzn.Integration.solveCertified clinleu with
     | .unsat => true
     | _ => false)
  have wclinleu : WellFormed fullSig clinleu :=
    (LeanFzn.Checker.wellFormedFastB_iff clinleu).mp (by native_decide)
  match hleu : LeanFzn.Integration.solveCertified clinleu with
  | .unsat =>
      have _hlu : ¬ ∃ store, Satisfies fullSig fullInterp clinleu
          store ∧ LeanFzn.Semantics.ParamHonest clinleu store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := clinleu) wclinleu hleu
      st ← st.check "certified theorem: linLe wide-door unsat_correct applies" true
      pure ()
  | _ =>
      st ← st.check "certified theorem: linLe wide-door unsat_correct applies" false
      pure ()

  -- linLe SAT still solves
  let clinles := parseOrPanic
    "var 1..3: x;\nconstraint int_lin_le([1],[x],2);\nsolve satisfy;"
  st ← st.check "certified: linLe SAT"
    (match LeanFzn.Integration.solveCertified clinles with
     | .sat _ => true
     | _ => false)

  -- linEq (int_plus with a literal result)
  let clineq := parseOrPanic
    "var 0..5: x;\nvar 0..5: y;\nconstraint int_plus(x, y, 7);\nsolve satisfy;"
  st ← st.check "certified: int_plus literal (linEq) SAT"
    (match LeanFzn.Integration.solveCertified clineq with
    | .sat store =>
        let x := (store (Ident.mk "x")).get!
        let y := (store (Ident.mk "y")).get!
        match x, y with
        | .int a, .int b => a + b == 7
        | _, _ => false
    | _ => false)

  -- THE GENERAL-COEFFICIENT LINEAR REGRESSIONS (2026-10-03): the
  -- propLinLe2/propLinEq2 slots now narrow with coefficients
  -- c ∉ {1,−1} via Euclidean Int.div bounds (lin2_fl_hi_lt /
  -- lin2_cl_neg_lo_gt), so multi-value general-coefficient models
  -- solve and refute through the wide certified door
  -- general-c SAT: 2x + y ≤ 4 with y ≤ 0 — the propagator narrows
  -- x (2x ≤ 4 − y ≤ 4) and the search completes with reads
  -- satisfying both constraints
  let clinle2s := parseOrPanic
    "var 0..5: x;\nvar 0..5: y;\nconstraint int_lin_le([2,1],[x,y],4);\nconstraint int_lin_le([1],[y],0);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified clinle2s with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      st ← st.check "certified: general-c linLe SAT (2x+y≤4, y≤0)"
        (match x, y with
        | .int a, .int b => 2 * a + b ≤ 4 ∧ b ≤ 0
        | _, _ => false)
      st ← st.check "certified: general-c linLe SAT text checker-accepted"
        (checkModelSolution clinle2s
          (LeanFzn.Integration.emitCertifiedSolution clinle2s store)
          == .accepted)
  | _ => st ← st.check "certified: general-c linLe SAT (2x+y≤4, y≤0)" (false)

  -- general-c linLe UNSAT: 2x + y ≤ 0 with x,y ≥ 1 — 2x + y ≥ 3 > 0
  let clinle2u := parseOrPanic
    "var 1..5: x;\nvar 1..5: y;\nconstraint int_lin_le([2,1],[x,y],0);\nsolve satisfy;"
  st ← st.check "certified: general-c linLe UNSAT (2x+y≤0, x,y≥1)"
    (match LeanFzn.Integration.solveCertified clinle2u with
     | .unsat => true
     | _ => false)
  have wclinle2u : WellFormed fullSig clinle2u :=
    (LeanFzn.Checker.wellFormedFastB_iff clinle2u).mp (by native_decide)
  match hle2u : LeanFzn.Integration.solveCertified clinle2u with
  | .unsat =>
      have _hl2u : ¬ ∃ store, Satisfies fullSig fullInterp clinle2u
          store ∧ LeanFzn.Semantics.ParamHonest clinle2u store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := clinle2u) wclinle2u hle2u
      st ← st.check
        "certified theorem: general-c linLe unsat_correct applies" true
      pure ()
  | _ =>
      st ← st.check
        "certified theorem: general-c linLe unsat_correct applies" false
      pure ()

  -- general-c linEq SAT: 3x + y = 7 has solutions (x=0,y=7 etc.); the
  -- reads satisfy the equation
  let clineq2s := parseOrPanic
    "var 0..10: x;\nvar 0..10: y;\nconstraint int_lin_eq([3,1],[x,y],7);\nsolve satisfy;"
  st ← st.check "certified: general-c linEq SAT (3x+y=7)"
    (match LeanFzn.Integration.solveCertified clineq2s with
    | .sat store =>
        let x := (store (Ident.mk "x")).get!
        let y := (store (Ident.mk "y")).get!
        match x, y with
        | .int a, .int b => 3 * a + b == 7
        | _, _ => false
    | _ => false)

  -- general-c linEq UNSAT: 3x + y = 7 over 0..1 slots — 3x + y ∈
  -- {0..4}, 7 is out of reach
  let clineq2u := parseOrPanic
    "var 0..1: x;\nvar 0..1: y;\nconstraint int_lin_eq([3,1],[x,y],7);\nsolve satisfy;"
  st ← st.check "certified: general-c linEq UNSAT (3x+y=7 over 0..1)"
    (match LeanFzn.Integration.solveCertified clineq2u with
     | .unsat => true
     | _ => false)

  -- THE int_lin_ne FAMILY (PLAN C1, routed since PLAN L0b1): the
  -- `int_lin_ne` constraint is extracted to `DomConstraint.linNe` and
  -- registers the generic checking propagator `propCheck` (PLAN L0b1),
  -- so its models pass the mixed LCG route gate; the leaf `satisfiedB`
  -- check still enforces it. Every verdict below is
  -- cross-checked against exhaustive enumeration of the declared
  -- domains (the same `allAssigns` specification the reference search
  -- uses).
  -- SAT, single variable: x ≠ 2 over 1..3
  let clinne1 := parseOrPanic
    "var 1..3: x;\nconstraint int_lin_ne([1],[x],2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull clinne1 with
  | .error _ => st ← st.check "linNe: compiles" false
  | .ok cp =>
      st ← st.check "linNe: extracted as .linNe"
        (cp.constraints.any fun dc =>
          match dc with | .linNe .. => true | _ => false)
  let linne1Spec : Bool := (allAssigns [[1, 2, 3]]).any fun l =>
    match l with | [a] => a != 2 | _ => false
  st ← st.check "linNe: enumeration finds x ≠ 2 over 1..3" linne1Spec
  match LeanFzn.Integration.solveCertified clinne1 with
  | .sat store =>
      st ← st.check "certified: int_lin_ne([1],[x],2) SAT store has x ≠ 2"
        (match (store (Ident.mk "x")).get! with
         | .int a => a != 2
         | _ => false)
  | _ => st ← st.check "certified: int_lin_ne([1],[x],2) SAT" false

  -- SAT, multi-variable with a negative coefficient: 3x − 2y ≠ 5
  -- over x ∈ −3..3, y ∈ 4..6 (witness x=1, y=4: 3 − 8 = −5)
  let clinne2 := parseOrPanic
    "var -3..3: x;\nvar 4..6: y;\nconstraint int_lin_ne([3,-2],[x,y],5);\nsolve satisfy;"
  let linne2Spec : Bool :=
    (allAssigns [[-3, -2, -1, 0, 1, 2, 3], [4, 5, 6]]).any fun l =>
      match l with | [a, b] => 3 * a - 2 * b != 5 | _ => false
  st ← st.check "linNe: enumeration finds 3x − 2y ≠ 5" linne2Spec
  match LeanFzn.Integration.solveCertified clinne2 with
  | .sat store =>
      st ← st.check "certified: int_lin_ne([3,-2],[x,y],5) SAT store has 3x − 2y ≠ 5"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => 3 * a - 2 * b != 5
         | _, _ => false)
  | _ => st ← st.check "certified: int_lin_ne([3,-2],[x,y],5) SAT" false

  -- UNSAT, forced equality: x ∈ {2} pins x = 2, the disequality x ≠ 2
  -- is violated at every enumerated point
  let clinne3 := parseOrPanic
    "var 2..2: x;\nconstraint int_lin_ne([1],[x],2);\nsolve satisfy;"
  let linne3Spec : Bool := (allAssigns [[2]]).any fun l =>
    match l with | [a] => a != 2 | _ => false
  st ← st.check "linNe: enumeration finds no x ≠ 2 in {2}" (!linne3Spec)
  st ← st.check "certified: int_lin_ne([1],[x],2) over {2} UNSAT"
    (match LeanFzn.Integration.solveCertified clinne3 with
     | .unsat => true
     | _ => false)

  -- UNSAT, multi-variable with coupling: x + y ≤ 2 forces x = y = 1
  -- over 1..3 × 1..3, where x + y = 2 violates x + y ≠ 2
  let clinne4 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_lin_le([1,1],[x,y],2);\nconstraint int_lin_ne([1,1],[x,y],2);\nsolve satisfy;"
  let linne4Spec : Bool := (allAssigns [[1, 2, 3], [1, 2, 3]]).any fun l =>
    match l with | [a, b] => a + b <= 2 && a + b != 2 | _ => false
  st ← st.check "linNe: enumeration finds no x+y≤2 ∧ x+y≠2" (!linne4Spec)
  st ← st.check "certified: linLe+linNe multi-var coupled UNSAT"
    (match LeanFzn.Integration.solveCertified clinne4 with
     | .unsat => true
     | _ => false)

  -- PLAN L2 (`propLinNe`): single-value removal and the all-fixed conflict.
  -- SAT: x ≤ 0 pins x = 0, so x + y ≠ 3 removes y = 3 (y ≠ 3 in the store)
  let clinne5 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nconstraint int_lin_ne([1,1],[x,y],3);\nconstraint int_le(x,0);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified clinne5 with
  | .sat store =>
      st ← st.check "certified: linNe prunes (x=0, x+y≠3 gives y≠3)"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => a == 0 && a + b != 3
         | _, _ => false)
  | _ => st ← st.check "certified: linNe prunes (x=0, x+y≠3) SAT" false
  -- UNSAT: x = 1, y = 2 fixed forces 2x + y = 4, violating 2x + y ≠ 4
  let clinne6 := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nconstraint int_lin_ne([2,1],[x,y],4);\nsolve satisfy;"
  st ← st.check "certified: linNe all-fixed conflict UNSAT"
    (match LeanFzn.Integration.solveCertified clinne6 with
     | .unsat => true
     | _ => false)
  -- UNSAT by two removals: x, y ∈ {0,1}, z = 3 fixed; x + y + z ≠ 3,
  -- x + y + z ≠ 4, x + y + z ≠ 5 leave no sum for x + y ∈ {0,1,2}
  let clinne7 := parseOrPanic
    "var 0..1: x;\nvar 0..1: y;\nvar 3..3: z;\nconstraint int_lin_ne([1,1,1],[x,y,z],3);\nconstraint int_lin_ne([1,1,1],[x,y,z],4);\nconstraint int_lin_ne([1,1,1],[x,y,z],5);\nsolve satisfy;"
  st ← st.check "certified: linNe chained removals UNSAT"
    (match LeanFzn.Integration.solveCertified clinne7 with
     | .unsat => true
     | _ => false)
  -- negative coefficient: 2x - y ≠ 1 with y = 3 fixed removes x = 2
  let clinne8 := parseOrPanic
    "var 0..3: x;\nvar 3..3: y;\nconstraint int_lin_ne([2,-1],[x,y],1);\nconstraint int_le(2,x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified clinne8 with
  | .sat store =>
      st ← st.check "certified: linNe negative coefficient (x≥2, 2x-y≠1)"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => 2 * a - b != 1 && a >= 2
         | _, _ => false)
  | _ => st ← st.check "certified: linNe negative coefficient SAT" false

  -- PLAN L4 (`propLeReifSlot`): int_le_reif with the reif slot pinned.
  -- r = true: x ≤ y ≤ 1, maximize-free check of the store
  let cleif1 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_le_reif(x,y,r);\nconstraint bool_clause([r],[]);\nconstraint int_le(y,1);\nconstraint int_le(1,x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cleif1 with
  | .sat store =>
      st ← st.check "certified: int_le_reif r=true gives x ≤ y"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == true && a <= b
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_le_reif r=true SAT" false
  -- r = false: y < x
  let cleif2 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_le_reif(x,y,r);\nconstraint bool_clause([],[r]);\nconstraint int_le(y,1);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cleif2 with
  | .sat store =>
      st ← st.check "certified: int_le_reif r=false gives y < x"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == false && b < a
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_le_reif r=false SAT" false
  -- UNSAT: r = true but x ≥ 2 > 1 ≥ y
  let cleif3 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_le_reif(x,y,r);\nconstraint bool_clause([r],[]);\nconstraint int_le(y,1);\nconstraint int_le(2,x);\nsolve satisfy;"
  st ← st.check "certified: int_le_reif r=true contradictory bounds UNSAT"
    (match LeanFzn.Integration.solveCertified cleif3 with
     | .unsat => true
     | _ => false)
  -- UNSAT: r = false but x ≤ 0 ≤ y
  let cleif4 := parseOrPanic
    "var 0..0: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_le_reif(x,y,r);\nconstraint bool_clause([],[r]);\nsolve satisfy;"
  st ← st.check "certified: int_le_reif r=false contradictory bounds UNSAT"
    (match LeanFzn.Integration.solveCertified cleif4 with
     | .unsat => true
     | _ => false)

  -- PLAN L4 (`propEqReifSlot`): int_eq_reif with the reif slot pinned.
  -- r = true: x = y (the bounds force x = y = 1)
  let ceqif1 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_eq_reif(x,y,r);\nconstraint bool_clause([r],[]);\nconstraint int_le(y,1);\nconstraint int_le(1,x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified ceqif1 with
  | .sat store =>
      st ← st.check "certified: int_eq_reif r=true gives x = y"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == true && a == b
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_eq_reif r=true SAT" false
  -- r = false: x ≠ y (x = 0 is fixed, so y must move off 0)
  let ceqif2 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_eq_reif(x,y,r);\nconstraint bool_clause([],[r]);\nconstraint int_eq(x,0);\nconstraint int_le(y,1);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified ceqif2 with
  | .sat store =>
      st ← st.check "certified: int_eq_reif r=false gives x ≠ y"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == false && a != b
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_eq_reif r=false SAT" false
  -- UNSAT: r = true but x = 1 ≠ y = 2
  let ceqif3 := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_eq_reif(x,y,r);\nconstraint bool_clause([r],[]);\nsolve satisfy;"
  st ← st.check "certified: int_eq_reif r=true contradictory values UNSAT"
    (match LeanFzn.Integration.solveCertified ceqif3 with
     | .unsat => true
     | _ => false)
  -- UNSAT: r = false but x = y = 1
  let ceqif4 := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_eq_reif(x,y,r);\nconstraint bool_clause([],[r]);\nsolve satisfy;"
  st ← st.check "certified: int_eq_reif r=false contradictory values UNSAT"
    (match LeanFzn.Integration.solveCertified ceqif4 with
     | .unsat => true
     | _ => false)

  -- PLAN L4 (`propNeReifSlot`): int_ne_reif with the reif slot pinned.
  -- r = true: x ≠ y
  let cneif1 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_ne_reif(x,y,r);\nconstraint bool_clause([r],[]);\nconstraint int_le(y,1);\nconstraint int_le(1,x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cneif1 with
  | .sat store =>
      st ← st.check "certified: int_ne_reif r=true gives x ≠ y"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == true && a != b
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_ne_reif r=true SAT" false
  -- r = false: x = y (the bounds force x = y = 1)
  let cneif2 := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: r;\nconstraint int_ne_reif(x,y,r);\nconstraint bool_clause([],[r]);\nconstraint int_le(y,1);\nconstraint int_le(1,x);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cneif2 with
  | .sat store =>
      st ← st.check "certified: int_ne_reif r=false gives x = y"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
            (store (Ident.mk "r")).get! with
         | .int a, .int b, .bool r => r == false && a == b
         | _, _, _ => false)
  | _ => st ← st.check "certified: int_ne_reif r=false SAT" false
  -- UNSAT: r = true but x = y = 1
  let cneif3 := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_ne_reif(x,y,r);\nconstraint bool_clause([r],[]);\nsolve satisfy;"
  st ← st.check "certified: int_ne_reif r=true contradictory values UNSAT"
    (match LeanFzn.Integration.solveCertified cneif3 with
     | .unsat => true
     | _ => false)
  -- UNSAT: r = false but x = 1 ≠ y = 2
  let cneif4 := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_ne_reif(x,y,r);\nconstraint bool_clause([],[r]);\nsolve satisfy;"
  st ← st.check "certified: int_ne_reif r=false contradictory values UNSAT"
    (match LeanFzn.Integration.solveCertified cneif4 with
     | .unsat => true
     | _ => false)

  -- THE C3 BOOLEAN ARRAY/INT FAMILIES (PLAN C3): `array_bool_and`,
  -- `bool2int` and `bool_eq`. Each is extracted to its own
  -- `DomConstraint` and registers NO propagator (leaf-enforced, the
  -- certified local-fallback route), so every verdict below is
  -- cross-checked against exhaustive enumeration of the declared
  -- domains (the same `allAssigns` specification the reference
  -- search uses).

  -- bool_eq SAT: two free Booleans forced equal
  let cbooleq := parseOrPanic
    "var bool: a;\nvar bool: b;\nconstraint bool_eq(a, b);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cbooleq with
  | .error _ => st ← st.check "bool_eq: compiles" false
  | .ok cp =>
      st ← st.check "bool_eq: extracted as .boolEqSlot"
        (cp.constraints.any fun dc =>
          match dc with | .boolEqSlot .. => true | _ => false)
  let booleqSpec : Bool :=
    (allAssigns ([[false, true], [false, true]] : List (List Bool))).any fun l =>
      match l with | [a, b] => a == b | _ => false
  st ← st.check "bool_eq: enumeration finds a = b" booleqSpec
  match LeanFzn.Integration.solveCertified cbooleq with
  | .sat store =>
      st ← st.check "certified: bool_eq SAT store has a = b"
        (match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get! with
         | .bool x, .bool y => x == y
         | _, _ => false)
  | _ => st ← st.check "certified: bool_eq SAT" false

  -- bool_eq UNSAT: equality plus a negation link
  let cboolequ := parseOrPanic
    "var bool: a;\nvar bool: b;\nconstraint bool_eq(a, b);\nconstraint bool_not(a, b);\nsolve satisfy;"
  let boolequSpec : Bool :=
    (allAssigns ([[false, true], [false, true]] : List (List Bool))).any fun l =>
      match l with | [a, b] => a == b && b == !a | _ => false
  st ← st.check "bool_eq: enumeration finds no a = b = ¬a" (!boolequSpec)
  st ← st.check "certified: bool_eq + bool_not UNSAT"
    (match LeanFzn.Integration.solveCertified cboolequ with
     | .unsat => true
     | _ => false)

  -- bool2int SAT: the integer is the 0/1 view of the Boolean
  let cbool2int := parseOrPanic
    "var bool: b;\nvar 0..1: i;\nconstraint bool2int(b, i);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cbool2int with
  | .error _ => st ← st.check "bool2int: compiles" false
  | .ok cp =>
      st ← st.check "bool2int: extracted as .bool2intSlot"
        (cp.constraints.any fun dc =>
          match dc with | .bool2intSlot .. => true | _ => false)
  let bool2intSpec : Bool :=
    (allAssigns ([[0, 1], [0, 1]] : List (List Int))).any fun l =>
      match l with
      | [b, i] => i == (if b == 1 then 1 else 0)
      | _ => false
  st ← st.check "bool2int: enumeration finds i = 0/1 of b" bool2intSpec
  match LeanFzn.Integration.solveCertified cbool2int with
  | .sat store =>
      st ← st.check "certified: bool2int SAT store has i = 0/1 of b"
        (match (store (Ident.mk "b")).get!, (store (Ident.mk "i")).get! with
         | .bool x, .int j => j == (if x then 1 else 0)
         | _, _ => false)
  | _ => st ← st.check "certified: bool2int SAT" false

  -- bool2int UNSAT: b pinned false (i = 0) with i ≠ 0
  let cbool2intu := parseOrPanic
    "var bool: b;\nvar 0..1: i;\nconstraint bool2int(b, i);\nconstraint bool_not(b, true);\nconstraint int_ne(i, 0);\nsolve satisfy;"
  let bool2intuSpec : Bool :=
    (allAssigns ([[0, 1], [0, 1]] : List (List Int))).any fun l =>
      match l with
      | [b, i] => (i == (if b == 1 then 1 else 0)) && b == 0 && i != 0
      | _ => false
  st ← st.check "bool2int: enumeration finds no b = false ∧ i ≠ 0" (!bool2intuSpec)
  st ← st.check "certified: bool2int + pinned-false + i ≠ 0 UNSAT"
    (match LeanFzn.Integration.solveCertified cbool2intu with
     | .unsat => true
     | _ => false)

  -- bool2int UNSAT coupling: two views of one Boolean must agree
  let cbool2int2 := parseOrPanic
    "var bool: b;\nvar 0..1: i;\nvar 0..1: j;\nconstraint bool2int(b, i);\nconstraint bool2int(b, j);\nconstraint int_ne(i, j);\nsolve satisfy;"
  let bool2int2Spec : Bool :=
    (allAssigns ([[0, 1], [0, 1], [0, 1]] : List (List Int))).any fun l =>
      match l with
      | [b, i, j] =>
          i == (if b == 1 then 1 else 0) ∧ j == (if b == 1 then 1 else 0) ∧
            i != j
      | _ => false
  st ← st.check "bool2int: enumeration finds no two differing views" (!bool2int2Spec)
  st ← st.check "certified: bool2int+bool2int+int_ne coupled UNSAT"
    (match LeanFzn.Integration.solveCertified cbool2int2 with
     | .unsat => true
     | _ => false)

  -- array_bool_and SAT: the target is the conjunction of the array
  let caba := parseOrPanic
    "var bool: b1;\nvar bool: b2;\nvar bool: r;\narray [1..2] of var bool: bs = [b1, b2];\nconstraint array_bool_and(bs, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull caba with
  | .error _ => st ← st.check "array_bool_and: compiles" false
  | .ok cp =>
      st ← st.check "array_bool_and: extracted as .arrayBoolAndSlot"
        (cp.constraints.any fun dc =>
          match dc with | .arrayBoolAndSlot .. => true | _ => false)
  let abaSpec : Bool :=
    (allAssigns ([[false, true], [false, true], [false, true]] :
      List (List Bool))).any fun l =>
      match l with | [a, b, r] => r == (a && b) | _ => false
  st ← st.check "array_bool_and: enumeration finds r = b1 ∧ b2" abaSpec
  match LeanFzn.Integration.solveCertified caba with
  | .sat store =>
      st ← st.check "certified: array_bool_and SAT store has r = b1 ∧ b2"
        (match (store (Ident.mk "b1")).get!, (store (Ident.mk "b2")).get!,
            (store (Ident.mk "r")).get! with
         | .bool a, .bool b, .bool r => r == (a && b)
         | _, _, _ => false)
  | _ => st ← st.check "certified: array_bool_and SAT" false

  -- array_bool_and UNSAT: r = false with both sources true
  let cabau := parseOrPanic
    "var bool: b1;\nvar bool: b2;\nvar bool: r;\narray [1..2] of var bool: bs = [b1, b2];\nconstraint array_bool_and(bs, r);\nconstraint bool_not(r, true);\nconstraint bool_not(b1, false);\nconstraint bool_not(b2, false);\nsolve satisfy;"
  let abauSpec : Bool :=
    (allAssigns ([[false, true], [false, true], [false, true]] :
      List (List Bool))).any fun l =>
      match l with
      | [a, b, r] => r == (a && b) && r == false && a == true && b == true
      | _ => false
  st ← st.check "array_bool_and: enumeration finds no r = false ∧ b1 = b2 = true"
    (!abauSpec)
  st ← st.check "certified: array_bool_and pinned-false UNSAT"
    (match LeanFzn.Integration.solveCertified cabau with
     | .unsat => true
     | _ => false)

  -- array_bool_and on the EMPTY array: the `all` of the empty source
  -- array is `true`, so the target is forced true
  let cabaNil := parseOrPanic
    "var bool: r;\nconstraint array_bool_and([], r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cabaNil with
  | .error _ => st ← st.check "array_bool_and empty: compiles" false
  | .ok cp =>
      st ← st.check "array_bool_and empty: extracted as .arrayBoolAndSlot []"
        (cp.constraints.any fun dc =>
          match dc with | .arrayBoolAndSlot [] _ => true | _ => false)
  let abaNilSpec : Bool :=
    (allAssigns ([[false, true]] : List (List Bool))).any fun l =>
      match l with | [r] => r == true | _ => false
  st ← st.check "array_bool_and empty: enumeration finds r = true" abaNilSpec
  match LeanFzn.Integration.solveCertified cabaNil with
  | .sat store =>
      st ← st.check "certified: array_bool_and [] SAT store has r = true"
        (match (store (Ident.mk "r")).get! with
         | .bool r => r
         | _ => false)
  | _ => st ← st.check "certified: array_bool_and [] SAT" false

  -- array_bool_and empty UNSAT: the target cannot be false
  let cabaNilu := parseOrPanic
    "var bool: r;\nconstraint array_bool_and([], r);\nconstraint bool_not(r, true);\nsolve satisfy;"
  let abaNiluSpec : Bool :=
    (allAssigns ([[false, true]] : List (List Bool))).any fun l =>
      match l with | [r] => r == true && r == false | _ => false
  st ← st.check "array_bool_and empty: enumeration finds no r = true ∧ r = false"
    (!abaNiluSpec)
  st ← st.check "certified: array_bool_and [] pinned-false UNSAT"
    (match LeanFzn.Integration.solveCertified cabaNilu with
     | .unsat => true
     | _ => false)

  -- array_bool_and of three slots: a two-level conjunction chain
  let caba3 := parseOrPanic
    "var bool: b1;\nvar bool: b2;\nvar bool: b3;\nvar bool: r;\narray [1..3] of var bool: bs = [b1, b2, b3];\nconstraint array_bool_and(bs, r);\nsolve satisfy;"
  let aba3Spec : Bool :=
    (allAssigns ([[false, true], [false, true], [false, true], [false, true]] :
      List (List Bool))).any fun l =>
      match l with | [a, b, c, r] => r == (a && b && c) | _ => false
  st ← st.check "array_bool_and 3: enumeration finds r = b1 ∧ b2 ∧ b3" aba3Spec
  match LeanFzn.Integration.solveCertified caba3 with
  | .sat store =>
      st ← st.check "certified: array_bool_and 3 SAT store has r = b1 ∧ b2 ∧ b3"
        (match (store (Ident.mk "b1")).get!, (store (Ident.mk "b2")).get!,
            (store (Ident.mk "b3")).get!, (store (Ident.mk "r")).get! with
         | .bool a, .bool b, .bool c, .bool r => r == (a && b && c)
         | _, _, _, _ => false)
  | _ => st ← st.check "certified: array_bool_and 3 SAT" false



  -- THE C4 ELEMENT FAMILIES (PLAN C4): `array_int_element`,
  -- `array_var_int_element` and `array_var_bool_element` (the
  -- FlatZinc element predicates). The library's `valuesGet1` is
  -- 1-BASED, so the index must lie in `1..len`: index 0 and index
  -- `len + 1` are unsatisfiable. Each family is extracted to its own
  -- `DomConstraint` and registers NO propagator (leaf-enforced, the
  -- certified local-fallback route), so every verdict below is
  -- cross-checked against exhaustive enumeration of the declared
  -- domains (the same `allAssigns` specification the reference
  -- search uses).

  -- array_int_element SAT: e = xs[i] over a CONSTANT integer array
  let caie := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 1..3: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull caie with
  | .error _ => st ← st.check "array_int_element: compiles" false
  | .ok cp =>
      st ← st.check "array_int_element: extracted as .arrayIntElementSlot"
        (cp.constraints.any fun dc =>
          match dc with | .arrayIntElementSlot .. => true | _ => false)
  let aieGet (i : Int) : Int :=
    match i with | 1 => 10 | 2 => 20 | 3 => 30 | _ => 0
  let aieSpec : Bool :=
    (allAssigns ([[1, 2, 3], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with | [i, e] => e == aieGet i | _ => false
  st ← st.check "array_int_element: enumeration finds e = xs[i]" aieSpec
  match LeanFzn.Integration.solveCertified caie with
  | .sat store =>
      st ← st.check "certified: array_int_element SAT store has e = xs[i]"
        (match (store (Ident.mk "i")).get!, (store (Ident.mk "e")).get! with
         | .int i, .int e => e == aieGet i
         | _, _ => false)
  | _ => st ← st.check "certified: array_int_element SAT" false

  -- array_int_element at the index domain's UPPER boundary: i pinned
  -- to the array's LAST index forces the read e = 30
  let caie3 := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 3..3: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nsolve satisfy;"
  let aie3Spec : Bool :=
    (allAssigns ([[3], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with | [i, e] => e == aieGet i | _ => false
  st ← st.check "array_int_element: boundary index i = 3 (last) SAT" aie3Spec
  match LeanFzn.Integration.solveCertified caie3 with
  | .sat store =>
      st ← st.check "certified: boundary index i = 3 store has e = 30"
        (match (store (Ident.mk "e")).get! with
         | .int e => e == 30
         | _ => false)
  | _ => st ← st.check "certified: boundary index i = 3 store has e = 30" false

  -- array_int_element OUT of range at both boundaries: index 0 and
  -- index 4 (= len + 1) admit no 1-based read
  let caie0 := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 0..0: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nsolve satisfy;"
  let aie0Spec : Bool :=
    (allAssigns ([[0], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with
        | [i, e] => (i == 1 && e == 10) || (i == 2 && e == 20) ||
            (i == 3 && e == 30)
        | _ => false
  st ← st.check "array_int_element: enumeration finds no index-0 read" (!aie0Spec)
  st ← st.check "certified: array_int_element index 0 UNSAT"
    (match LeanFzn.Integration.solveCertified caie0 with
     | .unsat => true
     | _ => false)
  let caie4 := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 4..4: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nsolve satisfy;"
  let aie4Spec : Bool :=
    (allAssigns ([[4], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with
        | [i, e] => (i == 1 && e == 10) || (i == 2 && e == 20) ||
            (i == 3 && e == 30)
        | _ => false
  st ← st.check "array_int_element: enumeration finds no index-4 read" (!aie4Spec)
  st ← st.check "certified: array_int_element index 4 (len+1) UNSAT"
    (match LeanFzn.Integration.solveCertified caie4 with
     | .unsat => true
     | _ => false)

  -- array_int_element CHAINED: e ≤ 15 rules out the reads 20 and 30,
  -- so only (i = 1, e = 10) remains
  let caiec := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 1..3: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nconstraint int_le(e, 15);\nsolve satisfy;"
  let caiecSpec : Bool :=
    (allAssigns ([[1, 2, 3], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with | [i, e] => e == aieGet i && e <= 15 | _ => false
  st ← st.check "array_int_element: chained e ≤ 15 SAT (read 10 only)" caiecSpec
  match LeanFzn.Integration.solveCertified caiec with
  | .sat store =>
      st ← st.check "certified: chained store has e = 10 at i = 1"
        (match (store (Ident.mk "i")).get!, (store (Ident.mk "e")).get! with
         | .int i, .int e => e == aieGet i && e <= 15 && i == 1
         | _, _ => false)
  | _ => st ← st.check "certified: chained store has e = 10 at i = 1" false
  let caiecu := parseOrPanic
    "array [1..3] of int: xs = [10, 20, 30];\nvar 1..3: i;\nvar 0..40: e;\nconstraint array_int_element(i, xs, e);\nconstraint int_le(e, 5);\nsolve satisfy;"
  let caiecuSpec : Bool :=
    (allAssigns ([[1, 2, 3], [0, 10, 20, 30, 40]] : List (List Int))).any
      fun l => match l with | [i, e] => e == aieGet i && e <= 5 | _ => false
  st ← st.check "array_int_element: chained e ≤ 5 has no read" (!caiecuSpec)
  st ← st.check "certified: array_int_element chained e ≤ 5 UNSAT"
    (match LeanFzn.Integration.solveCertified caiecu with
     | .unsat => true
     | _ => false)

  -- array_var_int_element SAT: e = ys[i] over a VARIABLE array alias
  let cavie := parseOrPanic
    "var 0..3: a;\nvar 0..3: b;\nvar 0..3: c;\narray [1..3] of var int: ys = [a, b, c];\nvar 1..3: i;\nvar 0..3: e;\nconstraint array_var_int_element(i, ys, e);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cavie with
  | .error _ => st ← st.check "array_var_int_element: compiles" false
  | .ok cp =>
      st ← st.check "array_var_int_element: extracted as .arrayVarIntElementSlot"
        (cp.constraints.any fun dc =>
          match dc with | .arrayVarIntElementSlot .. => true | _ => false)
  let avieGet (a b c i : Int) : Int :=
    match i with | 1 => a | 2 => b | 3 => c | _ => -1
  let avieSpec : Bool :=
    (allAssigns ([[0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 3],
      [0, 1, 2, 3]] : List (List Int))).any fun l =>
      match l with | [a, b, c, i, e] => e == avieGet a b c i | _ => false
  st ← st.check "array_var_int_element: enumeration finds e = ys[i]" avieSpec
  match LeanFzn.Integration.solveCertified cavie with
  | .sat store =>
      st ← st.check "certified: array_var_int_element SAT store has e = ys[i]"
        (match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get!,
            (store (Ident.mk "c")).get!, (store (Ident.mk "i")).get!,
            (store (Ident.mk "e")).get! with
         | .int a, .int b, .int c, .int i, .int e => e == avieGet a b c i
         | _, _, _, _, _ => false)
  | _ => st ← st.check "certified: array_var_int_element SAT" false

  -- array_var_int_element at the index domain's UPPER boundary:
  -- i pinned to the last index forces e = c
  let cavie3 := parseOrPanic
    "var 0..3: a;\nvar 0..3: b;\nvar 0..3: c;\narray [1..3] of var int: ys = [a, b, c];\nvar 3..3: i;\nvar 0..3: e;\nconstraint array_var_int_element(i, ys, e);\nsolve satisfy;"
  let avie3Spec : Bool :=
    (allAssigns ([[0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [3],
      [0, 1, 2, 3]] : List (List Int))).any fun l =>
      match l with | [a, b, c, i, e] => e == avieGet a b c i | _ => false
  st ← st.check "array_var_int_element: boundary index i = 3 SAT" avie3Spec
  match LeanFzn.Integration.solveCertified cavie3 with
  | .sat store =>
      st ← st.check "certified: boundary store has e = c"
        (match (store (Ident.mk "c")).get!, (store (Ident.mk "e")).get! with
         | .int c, .int e => e == c
         | _, _ => false)
  | _ => st ← st.check "certified: boundary store has e = c" false

  -- array_var_int_element OUT of range: index 0 admits no 1-based read
  let cavie0 := parseOrPanic
    "var 0..3: a;\nvar 0..3: b;\nvar 0..3: c;\narray [1..3] of var int: ys = [a, b, c];\nvar 0..0: i;\nvar 0..3: e;\nconstraint array_var_int_element(i, ys, e);\nsolve satisfy;"
  let avie0Spec : Bool :=
    (allAssigns ([[0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [0],
      [0, 1, 2, 3]] : List (List Int))).any fun l =>
      match l with | [a, b, c, i, e] => e == avieGet a b c i | _ => false
  st ← st.check "array_var_int_element: enumeration finds no index-0 read"
    (!avie0Spec)
  st ← st.check "certified: array_var_int_element index 0 UNSAT"
    (match LeanFzn.Integration.solveCertified cavie0 with
     | .unsat => true
     | _ => false)

  -- array_var_int_element CHAINED: e ≤ 1 restricts the read to the
  -- elements ≤ 1, and e ≤ −1 is impossible (all elements ≥ 0)
  let caviec := parseOrPanic
    "var 0..3: a;\nvar 0..3: b;\nvar 0..3: c;\narray [1..3] of var int: ys = [a, b, c];\nvar 1..3: i;\nvar 0..3: e;\nconstraint array_var_int_element(i, ys, e);\nconstraint int_le(e, 1);\nsolve satisfy;"
  let caviecSpec : Bool :=
    (allAssigns ([[0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 3],
      [0, 1, 2, 3]] : List (List Int))).any fun l =>
      match l with | [a, b, c, i, e] => e == avieGet a b c i && e <= 1 | _ => false
  st ← st.check "array_var_int_element: chained e ≤ 1 SAT" caviecSpec
  match LeanFzn.Integration.solveCertified caviec with
  | .sat store =>
      st ← st.check "certified: chained store reads an element ≤ 1"
        (match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get!,
            (store (Ident.mk "c")).get!, (store (Ident.mk "i")).get!,
            (store (Ident.mk "e")).get! with
         | .int a, .int b, .int c, .int i, .int e =>
             e == avieGet a b c i && e <= 1
         | _, _, _, _, _ => false)
  | _ => st ← st.check "certified: chained store reads an element ≤ 1" false
  let caviecu := parseOrPanic
    "var 2..3: a;\nvar 2..3: b;\nvar 2..3: c;\narray [1..3] of var int: ys = [a, b, c];\nvar 1..3: i;\nvar 0..3: e;\nconstraint array_var_int_element(i, ys, e);\nconstraint int_le(e, 1);\nsolve satisfy;"
  let caviecuSpec : Bool :=
    (allAssigns ([[2, 3], [2, 3], [2, 3], [1, 2, 3],
      [0, 1, 2, 3]] : List (List Int))).any fun l =>
      match l with
      | [a, b, c, i, e] => e == avieGet a b c i && e <= 1
      | _ => false
  st ← st.check "array_var_int_element: chained e ≤ 1 over 2..3 has no read"
    (!caviecuSpec)
  st ← st.check "certified: array_var_int_element chained UNSAT"
    (match LeanFzn.Integration.solveCertified caviecu with
     | .unsat => true
     | _ => false)

  -- array_var_bool_element SAT: e = bs[i] over a VARIABLE Boolean
  -- array alias
  let cavbe := parseOrPanic
    "var bool: a;\nvar bool: b;\narray [1..2] of var bool: bs = [a, b];\nvar 1..2: i;\nvar bool: e;\nconstraint array_var_bool_element(i, bs, e);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cavbe with
  | .error _ => st ← st.check "array_var_bool_element: compiles" false
  | .ok cp =>
      st ← st.check "array_var_bool_element: extracted as .arrayVarBoolElementSlot"
        (cp.constraints.any fun dc =>
          match dc with | .arrayVarBoolElementSlot .. => true | _ => false)
  let avbeGet (a b : Bool) (i : Int) : Bool :=
    match i with | 1 => a | 2 => b | _ => false
  let avbeSpec : Bool :=
    (allAssigns ([[.bool false, .bool true], [.bool false, .bool true],
      [.int 1, .int 2], [.bool false, .bool true]] : List (List Value))).any
      fun l => match l with
        | [.bool a, .bool b, .int i, .bool e] => e == avbeGet a b i
        | _ => false
  st ← st.check "array_var_bool_element: enumeration finds e = bs[i]" avbeSpec
  match LeanFzn.Integration.solveCertified cavbe with
  | .sat store =>
      st ← st.check "certified: array_var_bool_element SAT store has e = bs[i]"
        (match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get!,
            (store (Ident.mk "i")).get!, (store (Ident.mk "e")).get! with
         | .bool a, .bool b, .int i, .bool e => e == avbeGet a b i
         | _, _, _, _ => false)
  | _ => st ← st.check "certified: array_var_bool_element SAT" false

  -- array_var_bool_element at the index domain's UPPER boundary:
  -- i pinned to the last index forces e = b
  let cavbe2 := parseOrPanic
    "var bool: a;\nvar bool: b;\narray [1..2] of var bool: bs = [a, b];\nvar 2..2: i;\nvar bool: e;\nconstraint array_var_bool_element(i, bs, e);\nsolve satisfy;"
  let avbe2Spec : Bool :=
    (allAssigns ([[.bool false, .bool true], [.bool false, .bool true],
      [.int 2], [.bool false, .bool true]] : List (List Value))).any
      fun l => match l with
        | [.bool a, .bool b, .int i, .bool e] => e == avbeGet a b i
        | _ => false
  st ← st.check "array_var_bool_element: boundary index i = 2 SAT" avbe2Spec
  match LeanFzn.Integration.solveCertified cavbe2 with
  | .sat store =>
      st ← st.check "certified: boundary store has e = b"
        (match (store (Ident.mk "b")).get!, (store (Ident.mk "e")).get! with
         | .bool b, .bool e => e == b
         | _, _ => false)
  | _ => st ← st.check "certified: boundary store has e = b" false

  -- array_var_bool_element OUT of range: index 0 admits no 1-based read
  let cavbe0 := parseOrPanic
    "var bool: a;\nvar bool: b;\narray [1..2] of var bool: bs = [a, b];\nvar 0..0: i;\nvar bool: e;\nconstraint array_var_bool_element(i, bs, e);\nsolve satisfy;"
  let avbe0Spec : Bool :=
    (allAssigns ([[.bool false, .bool true], [.bool false, .bool true],
      [.int 0], [.bool false, .bool true]] : List (List Value))).any
      fun l => match l with
        | [.bool a, .bool b, .int i, .bool e] =>
            (i == 1 && e == a) || (i == 2 && e == b)
        | _ => false
  st ← st.check "array_var_bool_element: enumeration finds no index-0 read"
    (!avbe0Spec)
  st ← st.check "certified: array_var_bool_element index 0 UNSAT"
    (match LeanFzn.Integration.solveCertified cavbe0 with
     | .unsat => true
     | _ => false)

  -- array_var_bool_element CHAINED: all elements true and e pinned
  -- false is unsatisfiable; with a free element it is satisfiable
  -- through the first index
  let cavbeu := parseOrPanic
    "var bool: a;\nvar bool: b;\narray [1..2] of var bool: bs = [a, b];\nvar 1..2: i;\nvar bool: e;\nconstraint array_var_bool_element(i, bs, e);\nconstraint bool_not(a, false);\nconstraint bool_not(b, false);\nconstraint bool_not(e, true);\nsolve satisfy;"
  let avbeuSpec : Bool :=
    (allAssigns ([[.bool false, .bool true], [.bool false, .bool true],
      [.int 1, .int 2], [.bool false, .bool true]] : List (List Value))).any
      fun l => match l with
        | [.bool a, .bool b, .int i, .bool e] =>
            e == avbeGet a b i && a == true && b == true && e == false
        | _ => false
  st ← st.check "array_var_bool_element: chained all-true e = false has no read"
    (!avbeuSpec)
  st ← st.check "certified: array_var_bool_element chained UNSAT"
    (match LeanFzn.Integration.solveCertified cavbeu with
     | .unsat => true
     | _ => false)
  let cavbec := parseOrPanic
    "var bool: a;\nvar bool: b;\narray [1..2] of var bool: bs = [a, b];\nvar 1..2: i;\nvar bool: e;\nconstraint array_var_bool_element(i, bs, e);\nconstraint bool_not(a, false);\nconstraint bool_not(e, true);\nsolve satisfy;"
  let cavbecSpec : Bool :=
    (allAssigns ([[.bool false, .bool true], [.bool false, .bool true],
      [.int 1, .int 2], [.bool false, .bool true]] : List (List Value))).any
      fun l => match l with
        | [.bool a, .bool b, .int i, .bool e] =>
            e == avbeGet a b i && a == true && e == false
        | _ => false
  st ← st.check "array_var_bool_element: chained a, e = false/true SAT (i = 2)"
    cavbecSpec
  match LeanFzn.Integration.solveCertified cavbec with
  | .sat store =>
      st ← st.check "certified: chained store reads b = false at i = 2"
        (match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get!,
            (store (Ident.mk "i")).get!, (store (Ident.mk "e")).get! with
         | .bool a, .bool b, .int i, .bool e =>
             e == avbeGet a b i && a == true && e == false && i == 2
         | _, _, _, _ => false)
  | _ => st ← st.check "certified: chained store reads b = false at i = 2" false


  -- timesSlot: x·y = z over slots, with a bounding le
  let ctimes := parseOrPanic
    "var 1..4: x;\nvar 1..4: y;\nvar 1..16: z;\nconstraint int_times(x, y, z);\nsolve satisfy;"
  st ← st.check "certified: int_times SAT"
    (match LeanFzn.Integration.solveCertified ctimes with
     | .sat store =>
         let x := (store (Ident.mk "x")).get!
         let y := (store (Ident.mk "y")).get!
         let z := (store (Ident.mk "z")).get!
         match x, y, z with
         | .int a, .int b, .int c => a * b == c
         | _, _, _ => false
     | _ => false)
  let ctimesu := parseOrPanic
    "var 1..4: x;\nvar 1..4: y;\nvar 1..16: z;\nconstraint int_times(x, y, z);\nconstraint int_le(z, 0);\nsolve satisfy;"
  st ← st.check "certified: int_times UNSAT (times+le)"
    (match LeanFzn.Integration.solveCertified ctimesu with
     | .unsat => true
     | _ => false)

  -- times sign deductions: z < 0 with y > 0 propagates x < 0
  -- (the operand-side sign arm x ≤ 0 narrows x to [-3,-1])
  let ctimessign := parseOrPanic
    "var -3..3: x;\nvar 1..4: y;\nvar -12..12: z;\nconstraint int_times(x, y, z);\nconstraint int_le(z, -1);\nsolve satisfy;"
  st ← st.check "certified: int_times sign UNSAT (z<0, y>0, x≥0)"
    (match LeanFzn.Integration.solveCertified ctimessign with
     | .sat store =>
         let x := (store (Ident.mk "x")).get!
         let y := (store (Ident.mk "y")).get!
         let z := (store (Ident.mk "z")).get!
         match x, y, z with
         | .int a, .int b, .int c => a * b == c ∧ a ≤ -1 ∧ b ≥ 1 ∧ c ≤ -1
         | _, _, _ => false
     | _ => false)
  let ctimessignu := parseOrPanic
    "var 0..3: x;\nvar 1..4: y;\nvar -12..12: z;\nconstraint int_times(x, y, z);\nconstraint int_le(z, -1);\nsolve satisfy;"
  st ← st.check "certified: int_times sign UNSAT (z<0, y>0, x≥0)"
    (match LeanFzn.Integration.solveCertified ctimessignu with
     | .unsat => true
     | _ => false)
  -- the dual: z > 0 with y < 0 propagates x ≤ 0
  let ctimessignd := parseOrPanic
    "var -3..3: x;\nvar -4..-1: y;\nvar -12..12: z;\nconstraint int_times(x, y, z);\nconstraint int_le(1, z);\nsolve satisfy;"
  st ← st.check "certified: int_times sign SAT (z>0, y<0 → x<0)"
    (match LeanFzn.Integration.solveCertified ctimessignd with
     | .sat store =>
         let x := (store (Ident.mk "x")).get!
         let y := (store (Ident.mk "y")).get!
         let z := (store (Ident.mk "z")).get!
         match x, y, z with
         | .int a, .int b, .int c => a * b == c ∧ a ≤ -1 ∧ b ≤ -1 ∧ c ≥ 1
         | _, _, _ => false
     | _ => false)

  -- allDiff: the 3-slots/2-values pigeonhole (empty-clause conflict
  -- → the fallback-nogood machinery)
  let cad := parseOrPanic
    "var 0..1: x;\nvar 0..1: y;\nvar 0..1: z;\nconstraint all_different([x, y, z]);\nsolve satisfy;"
  st ← st.check "certified: all_different pigeonhole UNSAT"
    (match LeanFzn.Integration.solveCertified cad with
     | .unsat => true
     | _ => false)
  have wcad : WellFormed fullSig cad :=
    (LeanFzn.Checker.wellFormedFastB_iff cad).mp (by native_decide)
  match had : LeanFzn.Integration.solveCertified cad with
  | .unsat =>
      have _had : ¬ ∃ store, Satisfies fullSig fullInterp cad
          store ∧ LeanFzn.Semantics.ParamHonest cad store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := cad) wcad had
      st ← st.check "certified theorem: allDiff unsat_correct applies" true
      pure ()
  | _ =>
      st ← st.check "certified theorem: allDiff unsat_correct applies" false
      pure ()

  -- THEOREM-LEVEL nonvacuity: solveCertified_unsat_correct applies
  -- on the WIDE (multi-value, non-linLe) refutation
  have wcm3 : WellFormed fullSig cmunsat3 :=
    (LeanFzn.Checker.wellFormedFastB_iff cmunsat3).mp (by native_decide)
  match hcm3 : LeanFzn.Integration.solveCertified cmunsat3 with
  | .unsat =>
      have _hcm : ¬ ∃ store, Satisfies fullSig fullInterp cmunsat3
          store ∧ LeanFzn.Semantics.ParamHonest cmunsat3 store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := cmunsat3) wcm3 hcm3
      st ← st.check "certified theorem: wide unsat_correct applies"
        true
      pure ()
  | _ =>
      st ← st.check "certified theorem: wide unsat_correct applies" false
      pure ()

  -- compile failure: unsupported
  let cbad := parseOrPanic
    "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified cbad with
  | .unsupported r =>
      st ← st.check "certified: unbounded var refused"
        (r.contains "unbounded")
  | _ => st ← st.check "certified: unbounded var refused" (false)

  -- THEOREM-LEVEL nonvacuity: solveCertified_sat_correct applies to
  -- a real command run (the composed chain, kernel-checked)
  have wcsat : WellFormed fullSig csat :=
    (LeanFzn.Checker.wellFormedFastB_iff csat).mp (by native_decide)
  match hcres : LeanFzn.Integration.solveCertified csat with
  | .sat cstore =>
      have _hcert : Satisfies fullSig fullInterp csat cstore :=
        LeanFzn.Integration.solveCertified_sat_correct
          (m := csat) (store := cstore) wcsat hcres
      st ← st.check "certified theorem: solveCertified_sat_correct applies"
        true
      pure ()
  | _ =>
      st ← st.check "certified theorem: solveCertified_sat_correct applies"
        false
      pure ()

  -- THEOREM-LEVEL nonvacuity: solveCertified_unsat_correct applies
  have wcunsat : WellFormed fullSig cunsat :=
    (LeanFzn.Checker.wellFormedFastB_iff cunsat).mp (by native_decide)
  match hcures : LeanFzn.Integration.solveCertified cunsat with
  | .unsat =>
      have _hcu : ¬ ∃ store, Satisfies fullSig fullInterp cunsat store ∧
          LeanFzn.Semantics.ParamHonest cunsat store :=
        LeanFzn.Integration.solveCertified_unsat_correct
          (m := cunsat) wcunsat hcures
      st ← st.check "certified theorem: solveCertified_unsat_correct applies"
        true
      pure ()
  | _ =>
      st ← st.check "certified theorem: solveCertified_unsat_correct applies"
        false
      pure ()

  -- the fallback shape (parameter argument) also solves + certifies
  let dpar := parseOrPanic
    "int: k = 3;\nvar 1..5: x;\nconstraint int_le(x, k);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModel dpar with
  | .error _ => st ← st.check "direct: parameter fallback compiles" (false)
  | .ok problem =>
      st ← st.check "direct: parameter fallback compiles" (true)
      st ← st.check "direct: parameter fallback has one slot"
        (problem.domains.length == 1)
      match LeanFzn.Solver.Reference.solveCompiled problem with
      | some a =>
          st ← st.check "direct: parameter fallback finds a value"
            (a.length == 1)
          match a[0]! with
          | .int p => st ← st.check "direct: parameter fallback value ≤ 3" (p ≤ 3)
          | _ => st ← st.check "direct: parameter fallback value ≤ 3" (false)
      | none => st ← st.check "direct: parameter fallback finds a value" (false)

  -- ## Phase 4: the AUXILIARY-SLOT literal shapes (the nine pinning
  -- shapes; each compiles via fresh aux slots with singleton pinned
  -- domains and solves through the standard DomConstraint paths)

  -- int_times(x, y, 6): SAT with the checker-accepted output
  let ct1 := parseOrPanic
    "var 1..6: x;\nvar 1..6: y;\nconstraint int_times(x, y, 6);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified ct1 with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      st ← st.check "aux: int_times(x,y,6) solves SAT"
        (match x, y with
         | .int a, .int b => a * b == 6
         | _, _ => false)
      st ← st.check "aux: int_times emitted text checker-accepted"
        (checkModelSolution ct1
          (LeanFzn.Integration.emitCertifiedSolution ct1 store)
          == .accepted)
  | _ => st ← st.check "aux: int_times(x,y,6) solves SAT" (false)

  -- int_times(x, y, 6) + int_le(x, 1): UNSAT (x=1 forces y=6 > 3)
  let ct2 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_times(x, y, 6);\nconstraint int_le(x, 1);\nsolve satisfy;"
  st ← st.check "aux: int_times+int_le UNSAT"
    (match LeanFzn.Integration.solveCertified ct2 with
     | .unsat => true
     | _ => false)

  -- int_ne(x, 3): SAT
  let ct3 := parseOrPanic
    "var 1..3: x;\nconstraint int_ne(x, 3);\nsolve satisfy;"
  st ← st.check "aux: int_ne(x,3) SAT"
    (match LeanFzn.Integration.solveCertified ct3 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a ≠ 3
         | _ => false
     | _ => false)

  -- int_ne(x, 3) on the singleton {3}: UNSAT
  let ct4 := parseOrPanic
    "var 3..3: x;\nconstraint int_ne(x, 3);\nsolve satisfy;"
  st ← st.check "aux: int_ne(x,3) singleton UNSAT"
    (match LeanFzn.Integration.solveCertified ct4 with
     | .unsat => true
     | _ => false)

  -- int_ne(3, x): the symmetric form
  let ct5 := parseOrPanic
    "var 1..3: x;\nconstraint int_ne(3, x);\nsolve satisfy;"
  st ← st.check "aux: int_ne(3,x) SAT"
    (match LeanFzn.Integration.solveCertified ct5 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a ≠ 3
         | _ => false
     | _ => false)

  -- PLAN C5b: reified comparisons with one int-literal operand
  -- (x pinned to 2 so the reification is forced: SAT yields the
  -- expected r, and demanding the opposite is UNSAT)
  let reifCases : List (String × String × Bool) :=
    [ ("int_eq_reif(x,2,r)", "int_eq_reif(x, 2, r)", true)
    , ("int_eq_reif(2,x,r)", "int_eq_reif(2, x, r)", true)
    , ("int_le_reif(x,1,r)", "int_le_reif(x, 1, r)", false)
    , ("int_le_reif(3,x,r)", "int_le_reif(3, x, r)", false)
    , ("int_ne_reif(x,2,r)", "int_ne_reif(x, 2, r)", false)
    , ("int_ne_reif(1,x,r)", "int_ne_reif(1, x, r)", true) ]
  for (nm, cstr, expR) in reifCases do
    let base := "var 2..2: x;\nvar bool: r;\nconstraint " ++ cstr ++ ";\n"
    let ctS := parseOrPanic (base ++ "solve satisfy;")
    st ← st.check s!"aux: {nm} SAT"
      (match LeanFzn.Integration.solveCertified ctS with
       | .sat store =>
           match (store (Ident.mk "r")).get! with
           | .bool b => b == expR
           | _ => false
       | _ => false)
    -- demand the opposite value of r: UNSAT
    let opp := if expR then "constraint bool_not(r, true);\n"
      else "constraint bool_not(r, false);\n"
    let ctU := parseOrPanic (base ++ opp ++ "solve satisfy;")
    st ← st.check s!"aux: {nm} opposite UNSAT"
      (match LeanFzn.Integration.solveCertified ctU with
       | .unsat => true
       | _ => false)

  -- PLAN C9: min/max with one int-literal operand (x pinned to 4, k = 2)
  let mmCases : List (String × String × Int) :=
    [ ("int_min(x,2,z)", "int_min(x, 2, z)", 2)
    , ("int_min(2,x,z)", "int_min(2, x, z)", 2)
    , ("int_max(x,2,z)", "int_max(x, 2, z)", 4)
    , ("int_max(2,x,z)", "int_max(2, x, z)", 4) ]
  for (nm, cstr, expZ) in mmCases do
    let base := "var 4..4: x;\nvar 0..9: z;\nconstraint " ++ cstr ++ ";\n"
    let ctS := parseOrPanic (base ++ "solve satisfy;")
    st ← st.check s!"aux: {nm} SAT"
      (match LeanFzn.Integration.solveCertified ctS with
       | .sat store =>
           match (store (Ident.mk "z")).get! with
           | .int b => b == expZ
           | _ => false
       | _ => false)
    let ctU := parseOrPanic
      (base ++ s!"constraint int_ne(z, {expZ});\n" ++ "solve satisfy;")
    st ← st.check s!"aux: {nm} wrong result UNSAT"
      (match LeanFzn.Integration.solveCertified ctU with
       | .unsat => true
       | _ => false)

  -- bool_and(x, y, true): SAT with checker-accepted output
  let ct6 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, true);\nsolve satisfy;"
  match LeanFzn.Integration.solveCertified ct6 with
  | .sat store =>
      st ← st.check "aux: bool_and(x,y,true) solves SAT"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => a && b
         | _, _ => false)
      st ← st.check "aux: bool_and(true) emitted text checker-accepted"
        (checkModelSolution ct6
          (LeanFzn.Integration.emitCertifiedSolution ct6 store)
          == .accepted)
  | _ => st ← st.check "aux: bool_and(x,y,true) solves SAT" (false)

  -- bool_and(x, y, false) + bool_or(x, y, true): SAT (exactly one true)
  let ct7 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, false);\nconstraint bool_or(x, y, true);\nsolve satisfy;"
  st ← st.check "aux: bool_and(false)+bool_or(true) SAT"
    (match LeanFzn.Integration.solveCertified ct7 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => !(a && b) && (a || b)
         | _, _ => false
     | _ => false)

  -- bool_and(x, y, false) + bool_and(x, y, true): UNSAT
  let ct8 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, false);\nconstraint bool_and(x, y, true);\nsolve satisfy;"
  st ← st.check "aux: bool_and(false)+bool_and(true) UNSAT"
    (match LeanFzn.Integration.solveCertified ct8 with
     | .unsat => true
     | _ => false)

  -- bool_or(x, y, false): SAT (both false)
  let ct9 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_or(x, y, false);\nsolve satisfy;"
  st ← st.check "aux: bool_or(x,y,false) SAT"
    (match LeanFzn.Integration.solveCertified ct9 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => !(a || b)
         | _, _ => false
     | _ => false)

  -- int_times(x, 3, y): the symmetric literal-middle form
  let ct10 := parseOrPanic
    "var 1..3: x;\nvar 1..9: y;\nconstraint int_times(x, 3, y);\nsolve satisfy;"
  st ← st.check "aux: int_times(x,3,y) SAT"
    (match LeanFzn.Integration.solveCertified ct10 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => a * 3 == b
         | _, _ => false
     | _ => false)

  -- int_times(3, x, y): the symmetric literal-first form
  let ct11 := parseOrPanic
    "var 1..3: x;\nvar 1..9: y;\nconstraint int_times(3, x, y);\nsolve satisfy;"
  st ← st.check "aux: int_times(3,x,y) SAT"
    (match LeanFzn.Integration.solveCertified ct11 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => 3 * a == b
         | _, _ => false
     | _ => false)

  -- int_times with TWO literal arguments: now SUPPORTED (the
  -- two-literal times shapes timesRKK/KKR/KRR — see the aux-slot
  -- expansion's CompileAux2* proofs and Exact's coverage arms);
  -- x·2 = 6 over x ∈ 1..3 solves at x = 3
  let ct12 := parseOrPanic
    "var 1..3: x;\nconstraint int_times(x, 2, 6);\nsolve satisfy;"
  st ← st.check "aux: int_times(x,2,6) two-literal SAT"
    (match LeanFzn.Integration.solveCertified ct12 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a * 2 == 6
         | _ => false
     | _ => false)

  -- the aux-slot structure: int_times(x,y,6) has ONE aux slot with
  -- the singleton domain {6}
  match LeanFzn.Compiler.compileModel ct1 with
  | .ok p =>
      st ← st.check "aux: int_times uses one aux slot (3 slots total)"
        (p.domains.length == 3)
      st ← st.check "aux: the aux slot's domain is the singleton {6}"
        (p.domains[2]! == [.int 6])
  | .error _ =>
      st ← st.check "aux: int_times uses one aux slot (3 slots total)" (false)
      st ← st.check "aux: the aux slot's domain is the singleton {6}" (false)

  -- THE C5 REIFIED FAMILIES (PLAN C5): `int_eq_reif`, `int_le_reif`,
  -- `int_ne_reif` (ident-ident-ident) and `int_lin_eq_reif`,
  -- `int_lin_le_reif`, `int_lin_ne_reif`
  -- (int-array-ident-array-int-ident). Each is extracted to its own
  -- `DomConstraint` (`.eqReifSlot`/`.leReifSlot`/`.neReifSlot`/
  -- `.linEqReif`/`.linLeReif`/`.linNeReif`) and registers NO propagator
  -- (leaf-enforced, the certified local-fallback route), so every
  -- verdict below is cross-checked against exhaustive enumeration of
  -- the declared domains. Per family: the reification slot
  -- unconstrained (both truth values realizable, the store agreeing
  -- with `R ↔ rel`), `R = true` forcing the relation (SAT store
  -- checked, and the refuting pin UNSAT), and the relation forcing
  -- `R = true` with `R` otherwise unconstrained. `bool_not(r, false)`
  -- pins `R = true` (the established literal pin form). Every model
  -- declares the compared slots as `x`, `y` and the reification slot
  -- as `r`, so the two enumeration helpers below apply to every
  -- family.

  -- exhaustive enumeration over the slots [x, y, r]
  -- (ints × ints × bools): is there an assignment with `R ↔ rel`
  -- (and additionally `R = b` when `rPin = some b`)?
  let reifWitness : (Int → Int → Bool) → List Int → List Int →
      Option Bool → Bool :=
    fun rel dx dy rPin =>
      (allAssigns ([dx.map .int, dy.map .int, [.bool false, .bool true]] :
        List (List Value))).any fun l =>
        match l with
        | [.int p, .int q, .bool rb] =>
            rb == rel p q &&
              (match rPin with | some b => rb == b | none => true)
        | _ => false
  -- the certified store's three slots agree with `R ↔ rel`
  let reifStoreOk : (Int → Int → Bool) → Store → Bool :=
    fun rel store =>
      match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
          (store (Ident.mk "r")).get! with
      | .int p, .int q, .bool rb => rb == rel p q
      | _, _, _ => false
  -- the certified store's reification slot reads `true`
  let rTrue : Store → Bool :=
    fun store =>
      match (store (Ident.mk "r")).get! with
      | .bool rb => rb
      | _ => false

  -- int_eq_reif: R ↔ (x = y)
  let eqRel : Int → Int → Bool := fun p q => p == q
  let ceqru := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_eq_reif(x, y, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull ceqru with
  | .error _ => st ← st.check "int_eq_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_eq_reif: extracted as .eqReifSlot"
        (cp.constraints.any fun dc =>
          match dc with | .eqReifSlot .. => true | _ => false)
  st ← st.check "int_eq_reif: enumeration finds a witness with r unconstrained"
    (reifWitness eqRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_eq_reif: r unconstrained realizes both truth values"
    (reifWitness eqRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness eqRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_eq_reif store has r ↔ x = y"
    (match LeanFzn.Integration.solveCertified ceqru with
     | .sat store => reifStoreOk eqRel store
     | _ => false)
  -- int_eq_reif: R = true forces x = y, and is refuted at x = 1, y = 2
  let ceqrt := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_eq_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_eq_reif: enumeration finds R = true with x = y"
    (reifWitness eqRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_eq_reif R = true forces x = y"
    (match LeanFzn.Integration.solveCertified ceqrt with
     | .sat store => reifStoreOk eqRel store && rTrue store
     | _ => false)
  let ceqrtu := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_eq_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_eq_reif: enumeration finds no R = true at x = 1, y = 2"
    (!reifWitness eqRel [1] [2] (some true))
  st ← st.check "certified: int_eq_reif R = true at x = 1, y = 2 UNSAT"
    (match LeanFzn.Integration.solveCertified ceqrtu with
     | .unsat => true
     | _ => false)
  -- int_eq_reif: x = y forces R = true with R unconstrained
  let ceqrf := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_eq_reif(x, y, r);\nsolve satisfy;"
  st ← st.check "int_eq_reif: enumeration at x = y = 1 admits R = true only"
    (reifWitness eqRel [1] [1] (some true) &&
      !reifWitness eqRel [1] [1] (some false))
  st ← st.check "certified: x = y = 1 forces R = true (r unconstrained)"
    (match LeanFzn.Integration.solveCertified ceqrf with
     | .sat store => rTrue store && reifStoreOk eqRel store
     | _ => false)

  -- int_le_reif: R ↔ (x ≤ y)
  let leRel : Int → Int → Bool := fun p q => p <= q
  let cleu := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_le_reif(x, y, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cleu with
  | .error _ => st ← st.check "int_le_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_le_reif: extracted as .leReifSlot"
        (cp.constraints.any fun dc =>
          match dc with | .leReifSlot .. => true | _ => false)
  st ← st.check "int_le_reif: enumeration finds a witness with r unconstrained"
    (reifWitness leRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_le_reif: r unconstrained realizes both truth values"
    (reifWitness leRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness leRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_le_reif store has r ↔ x ≤ y"
    (match LeanFzn.Integration.solveCertified cleu with
     | .sat store => reifStoreOk leRel store
     | _ => false)
  -- int_le_reif: R = true forces x ≤ y, and is refuted at x = 2, y = 1
  let clet := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_le_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_le_reif: enumeration finds R = true with x ≤ y"
    (reifWitness leRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_le_reif R = true forces x ≤ y"
    (match LeanFzn.Integration.solveCertified clet with
     | .sat store => reifStoreOk leRel store && rTrue store
     | _ => false)
  let cletu := parseOrPanic
    "var 2..2: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_le_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_le_reif: enumeration finds no R = true at x = 2, y = 1"
    (!reifWitness leRel [2] [1] (some true))
  st ← st.check "certified: int_le_reif R = true at x = 2, y = 1 UNSAT"
    (match LeanFzn.Integration.solveCertified cletu with
     | .unsat => true
     | _ => false)
  -- int_le_reif: x ≤ y forces R = true with R unconstrained
  let clef := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_le_reif(x, y, r);\nsolve satisfy;"
  st ← st.check "int_le_reif: enumeration at x = 1, y = 2 admits R = true only"
    (reifWitness leRel [1] [2] (some true) &&
      !reifWitness leRel [1] [2] (some false))
  st ← st.check "certified: x = 1 ≤ y = 2 forces R = true (r unconstrained)"
    (match LeanFzn.Integration.solveCertified clef with
     | .sat store => rTrue store && reifStoreOk leRel store
     | _ => false)

  -- int_ne_reif: R ↔ (x ≠ y)
  let neRel : Int → Int → Bool := fun p q => p != q
  let cneu := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_ne_reif(x, y, r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cneu with
  | .error _ => st ← st.check "int_ne_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_ne_reif: extracted as .neReifSlot"
        (cp.constraints.any fun dc =>
          match dc with | .neReifSlot .. => true | _ => false)
  st ← st.check "int_ne_reif: enumeration finds a witness with r unconstrained"
    (reifWitness neRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_ne_reif: r unconstrained realizes both truth values"
    (reifWitness neRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness neRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_ne_reif store has r ↔ x ≠ y"
    (match LeanFzn.Integration.solveCertified cneu with
     | .sat store => reifStoreOk neRel store
     | _ => false)
  -- int_ne_reif: R = true forces x ≠ y, and is refuted at x = y = 1
  let cnet := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_ne_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_ne_reif: enumeration finds R = true with x ≠ y"
    (reifWitness neRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_ne_reif R = true forces x ≠ y"
    (match LeanFzn.Integration.solveCertified cnet with
     | .sat store => reifStoreOk neRel store && rTrue store
     | _ => false)
  let cnetu := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_ne_reif(x, y, r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_ne_reif: enumeration finds no R = true at x = y = 1"
    (!reifWitness neRel [1] [1] (some true))
  st ← st.check "certified: int_ne_reif R = true at x = y = 1 UNSAT"
    (match LeanFzn.Integration.solveCertified cnetu with
     | .unsat => true
     | _ => false)
  -- int_ne_reif: x ≠ y forces R = true with R unconstrained
  let cnef := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_ne_reif(x, y, r);\nsolve satisfy;"
  st ← st.check "int_ne_reif: enumeration at x = 1, y = 2 admits R = true only"
    (reifWitness neRel [1] [2] (some true) &&
      !reifWitness neRel [1] [2] (some false))
  st ← st.check "certified: x = 1 ≠ y = 2 forces R = true (r unconstrained)"
    (match LeanFzn.Integration.solveCertified cnef with
     | .sat store => rTrue store && reifStoreOk neRel store
     | _ => false)

  -- int_lin_eq_reif: R ↔ (2x + y = 2)
  let lqRel : Int → Int → Bool := fun p q => 2 * p + q == 2
  let clqu := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_eq_reif([2,1],[x,y],2,r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull clqu with
  | .error _ => st ← st.check "int_lin_eq_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_lin_eq_reif: extracted as .linEqReif"
        (cp.constraints.any fun dc =>
          match dc with | .linEqReif .. => true | _ => false)
  st ← st.check "int_lin_eq_reif: enumeration finds a witness (r unconstrained)"
    (reifWitness lqRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_lin_eq_reif: r unconstrained realizes both truth values"
    (reifWitness lqRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness lqRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_lin_eq_reif store has r ↔ 2x + y = 2"
    (match LeanFzn.Integration.solveCertified clqu with
     | .sat store => reifStoreOk lqRel store
     | _ => false)
  -- int_lin_eq_reif: R = true forces 2x + y = 2, refuted at x = 2, y = 0
  let clqt := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_eq_reif([2,1],[x,y],2,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_eq_reif: enumeration finds R = true with 2x + y = 2"
    (reifWitness lqRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_lin_eq_reif R = true forces 2x + y = 2"
    (match LeanFzn.Integration.solveCertified clqt with
     | .sat store => reifStoreOk lqRel store && rTrue store
     | _ => false)
  let clqtu := parseOrPanic
    "var 2..2: x;\nvar 0..0: y;\nvar bool: r;\nconstraint int_lin_eq_reif([2,1],[x,y],2,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_eq_reif: enumeration finds no R = true at x = 2, y = 0"
    (!reifWitness lqRel [2] [0] (some true))
  st ← st.check "certified: int_lin_eq_reif R = true at x = 2, y = 0 UNSAT"
    (match LeanFzn.Integration.solveCertified clqtu with
     | .unsat => true
     | _ => false)
  -- int_lin_eq_reif: 2x + y = 2 forces R = true with R unconstrained
  let clqf := parseOrPanic
    "var 1..1: x;\nvar 0..0: y;\nvar bool: r;\nconstraint int_lin_eq_reif([2,1],[x,y],2,r);\nsolve satisfy;"
  st ← st.check "int_lin_eq_reif: enumeration at x = 1, y = 0 admits R = true only"
    (reifWitness lqRel [1] [0] (some true) &&
      !reifWitness lqRel [1] [0] (some false))
  st ← st.check "certified: 2x + y = 2 at x = 1, y = 0 forces R = true"
    (match LeanFzn.Integration.solveCertified clqf with
     | .sat store => rTrue store && reifStoreOk lqRel store
     | _ => false)

  -- int_lin_le_reif: R ↔ (x + y ≤ 2)
  let llRel : Int → Int → Bool := fun p q => p + q <= 2
  let cllu := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_le_reif([1,1],[x,y],2,r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull cllu with
  | .error _ => st ← st.check "int_lin_le_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_lin_le_reif: extracted as .linLeReif"
        (cp.constraints.any fun dc =>
          match dc with | .linLeReif .. => true | _ => false)
  st ← st.check "int_lin_le_reif: enumeration finds a witness (r unconstrained)"
    (reifWitness llRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_lin_le_reif: r unconstrained realizes both truth values"
    (reifWitness llRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness llRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_lin_le_reif store has r ↔ x + y ≤ 2"
    (match LeanFzn.Integration.solveCertified cllu with
     | .sat store => reifStoreOk llRel store
     | _ => false)
  -- int_lin_le_reif: R = true forces x + y ≤ 2, refuted at x = 1, y = 2
  let cllt := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_le_reif([1,1],[x,y],2,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_le_reif: enumeration finds R = true with x + y ≤ 2"
    (reifWitness llRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_lin_le_reif R = true forces x + y ≤ 2"
    (match LeanFzn.Integration.solveCertified cllt with
     | .sat store => reifStoreOk llRel store && rTrue store
     | _ => false)
  let clltu := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_lin_le_reif([1,1],[x,y],2,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_le_reif: enumeration finds no R = true at x = 1, y = 2"
    (!reifWitness llRel [1] [2] (some true))
  st ← st.check "certified: int_lin_le_reif R = true at x = 1, y = 2 UNSAT"
    (match LeanFzn.Integration.solveCertified clltu with
     | .unsat => true
     | _ => false)
  -- int_lin_le_reif: x + y ≤ 2 forces R = true with R unconstrained
  let cllf := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_lin_le_reif([1,1],[x,y],2,r);\nsolve satisfy;"
  st ← st.check "int_lin_le_reif: enumeration at x = y = 1 admits R = true only"
    (reifWitness llRel [1] [1] (some true) &&
      !reifWitness llRel [1] [1] (some false))
  st ← st.check "certified: x + y ≤ 2 at x = y = 1 forces R = true"
    (match LeanFzn.Integration.solveCertified cllf with
     | .sat store => rTrue store && reifStoreOk llRel store
     | _ => false)

  -- int_lin_ne_reif: R ↔ (x − y ≠ 0)
  let lnRel : Int → Int → Bool := fun p q => p - q != 0
  let clnu := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,r);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull clnu with
  | .error _ => st ← st.check "int_lin_ne_reif: compiles" false
  | .ok cp =>
      st ← st.check "int_lin_ne_reif: extracted as .linNeReif"
        (cp.constraints.any fun dc =>
          match dc with | .linNeReif .. => true | _ => false)
  st ← st.check "int_lin_ne_reif: enumeration finds a witness (r unconstrained)"
    (reifWitness lnRel [0, 1, 2] [0, 1, 2] none)
  st ← st.check "int_lin_ne_reif: r unconstrained realizes both truth values"
    (reifWitness lnRel [0, 1, 2] [0, 1, 2] (some true) &&
      reifWitness lnRel [0, 1, 2] [0, 1, 2] (some false))
  st ← st.check "certified: int_lin_ne_reif store has r ↔ x − y ≠ 0"
    (match LeanFzn.Integration.solveCertified clnu with
     | .sat store => reifStoreOk lnRel store
     | _ => false)
  -- int_lin_ne_reif: R = true forces x − y ≠ 0, refuted at x = y = 1
  let clnt := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: r;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_ne_reif: enumeration finds R = true with x − y ≠ 0"
    (reifWitness lnRel [0, 1, 2] [0, 1, 2] (some true))
  st ← st.check "certified: int_lin_ne_reif R = true forces x − y ≠ 0"
    (match LeanFzn.Integration.solveCertified clnt with
     | .sat store => reifStoreOk lnRel store && rTrue store
     | _ => false)
  let clntu := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: r;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,r);\nconstraint bool_not(r, false);\nsolve satisfy;"
  st ← st.check "int_lin_ne_reif: enumeration finds no R = true at x = y = 1"
    (!reifWitness lnRel [1] [1] (some true))
  st ← st.check "certified: int_lin_ne_reif R = true at x = y = 1 UNSAT"
    (match LeanFzn.Integration.solveCertified clntu with
     | .unsat => true
     | _ => false)
  -- int_lin_ne_reif: x − y ≠ 0 forces R = true with R unconstrained
  let clnf := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: r;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,r);\nsolve satisfy;"
  st ← st.check "int_lin_ne_reif: enumeration at x = 1, y = 2 admits R = true only"
    (reifWitness lnRel [1] [2] (some true) &&
      !reifWitness lnRel [1] [2] (some false))
  st ← st.check "certified: x − y ≠ 0 at x = 1, y = 2 forces R = true"
    (match LeanFzn.Integration.solveCertified clnf with
     | .sat store => rTrue store && reifStoreOk lnRel store
     | _ => false)

  -- THE C6 ARITHMETIC AND EXTREME FAMILIES (PLAN C6): the general
  -- `int_div`/`int_mod` (the StdLib predicate's exact reading
  -- `b ≠ 0 ∧ c = Int.tdiv a b` / `c = Int.tmod a b`, so negative
  -- operands TRUNCATE towards zero and the remainder's sign follows
  -- the dividend), the general `int_min`/`int_max` with a literal
  -- operand (`.minPair`/`.maxPair`, all three operands integers — the
  -- rect-euler `int_min(x, y, 0)` / `int_max(0, x, y)` shapes) and
  -- the `array_int_maximum`/`array_int_minimum` array forms
  -- (`.maxGen`/`.minGen`, `maxValue`/`minValue` of the operand
  -- values, result argument first, the EMPTY array unsatisfiable).
  -- Each is extracted to its own `DomConstraint` and registers NO
  -- propagator (leaf-enforced, the certified local-fallback route),
  -- so every verdict below is cross-checked against exhaustive
  -- enumeration of the declared domains (the same `allAssigns`
  -- specification the reference search uses). The three-operand
  -- models declare their slots as `a`, `b`, `c`; the array models as
  -- `m` (the result, first argument in the source) and `x`, `y` (the
  -- variable array's elements).

  -- exhaustive enumeration over the three int slots [a, b, c]
  let arithWitness : (Int → Int → Int → Bool) → List Int → List Int →
      List Int → Bool :=
    fun rel da db dc =>
      (allAssigns [da, db, dc]).any fun l =>
        match l with
        | [p, q, s] => rel p q s
        | _ => false
  -- the certified store's [a, b, c] slots satisfy `rel`
  let arithStoreOk : (Int → Int → Int → Bool) → Store → Bool :=
    fun rel store =>
      match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get!,
          (store (Ident.mk "c")).get! with
      | .int p, .int q, .int s => rel p q s
      | _, _, _ => false

  -- int_div: c = tdiv a b with b ≠ 0 (a zero divisor is unsatisfiable)
  let divRel : Int → Int → Int → Bool :=
    fun p q s => q != 0 && s == Int.tdiv p q
  let gdiv := parseOrPanic
    "var -9..9: a;\nvar -3..3: b;\nvar -9..9: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gdiv with
  | .error _ => st ← st.check "int_div: compiles" false
  | .ok cp =>
      st ← st.check "int_div: extracted as .divGen"
        (cp.constraints.any fun dc =>
          match dc with | .divGen .. => true | _ => false)
  st ← st.check "int_div: enumeration finds a truncated-quotient witness"
    (arithWitness divRel [-9, -1, 0, 1, 9] [-3, -1, 0, 1, 3] [-9, -3, 0, 3, 9])
  st ← st.check "int_div: enumeration rejects a zero divisor"
    (!arithWitness divRel [4] [0] [0, 1, 2])
  st ← st.check "certified: int_div store has c = tdiv a b"
    (match LeanFzn.Integration.solveCertified gdiv with
     | .sat store => arithStoreOk divRel store
     | _ => false)
  -- int_div truncates towards zero: tdiv(-7, 2) = -3 (not the floor -4)
  let gdivNeg := parseOrPanic
    "var -7..-7: a;\nvar 2..2: b;\nvar -3..-3: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: tdiv(-7, 2) = -3 SAT (truncated, not floored)"
    (match LeanFzn.Integration.solveCertified gdivNeg with
     | .sat store => arithStoreOk divRel store
     | _ => false)
  let gdivNegB := parseOrPanic
    "var 7..7: a;\nvar -2..-2: b;\nvar -3..-3: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: tdiv(7, -2) = -3 SAT (truncation on both signs)"
    (match LeanFzn.Integration.solveCertified gdivNegB with
     | .sat store => arithStoreOk divRel store
     | _ => false)
  let gdivFloor := parseOrPanic
    "var -7..-7: a;\nvar 2..2: b;\nvar -4..-4: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: int_div pinned to the floor quotient -4 UNSAT"
    (match LeanFzn.Integration.solveCertified gdivFloor with
     | .unsat => true
     | _ => false)
  let gdivCeil := parseOrPanic
    "var -7..-7: a;\nvar 2..2: b;\nvar 3..3: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: int_div pinned away from zero (3) UNSAT"
    (match LeanFzn.Integration.solveCertified gdivCeil with
     | .unsat => true
     | _ => false)
  let gdivZero := parseOrPanic
    "var 4..4: a;\nvar 0..0: b;\nvar -9..9: c;\nconstraint int_div(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: int_div zero divisor UNSAT"
    (match LeanFzn.Integration.solveCertified gdivZero with
     | .unsat => true
     | _ => false)
  -- literals on BOTH operands (the rect-euler `int_div(0, 11, c)` and
  -- `int_mod(x, 2, y)` shapes): the constant quotient 100 / 10 = 10
  let gdivLit := parseOrPanic
    "var 9..11: c;\nconstraint int_div(100, 10, c);\nsolve satisfy;"
  st ← st.check "certified: int_div(100, 10, c) store has c = 10"
    (match LeanFzn.Integration.solveCertified gdivLit with
     | .sat store =>
         match (store (Ident.mk "c")).get! with
         | .int s => s == 10
         | _ => false
     | _ => false)
  let gdivLitU := parseOrPanic
    "var 9..9: c;\nconstraint int_div(100, 10, c);\nsolve satisfy;"
  st ← st.check "certified: int_div(100, 10, 9) UNSAT"
    (match LeanFzn.Integration.solveCertified gdivLitU with
     | .unsat => true
     | _ => false)

  -- int_mod: c = tmod a b with b ≠ 0 (the remainder's sign follows
  -- the dividend: tmod(-7, 2) = -1 and tmod(7, -2) = 1)
  let modRel : Int → Int → Int → Bool :=
    fun p q s => q != 0 && s == Int.tmod p q
  let gmod := parseOrPanic
    "var -7..7: a;\nvar -4..4: b;\nvar -7..7: c;\nconstraint int_mod(a, b, c);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gmod with
  | .error _ => st ← st.check "int_mod: compiles" false
  | .ok cp =>
      st ← st.check "int_mod: extracted as .modGen"
        (cp.constraints.any fun dc =>
          match dc with | .modGen .. => true | _ => false)
  st ← st.check "int_mod: enumeration finds a truncated-remainder witness"
    (arithWitness modRel [-7, -1, 0, 1, 7] [-4, -1, 0, 1, 4] [-7, -1, 0, 1, 7])
  st ← st.check "int_mod: enumeration rejects a zero divisor"
    (!arithWitness modRel [-7] [0] [-7, 0, 7])
  st ← st.check "certified: int_mod store has c = tmod a b"
    (match LeanFzn.Integration.solveCertified gmod with
     | .sat store => arithStoreOk modRel store
     | _ => false)
  let gmodNeg := parseOrPanic
    "var -7..-7: a;\nvar 2..2: b;\nvar -1..-1: c;\nconstraint int_mod(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: tmod(-7, 2) = -1 SAT (sign of the dividend)"
    (match LeanFzn.Integration.solveCertified gmodNeg with
     | .sat store => arithStoreOk modRel store
     | _ => false)
  let gmodNegB := parseOrPanic
    "var 7..7: a;\nvar -2..-2: b;\nvar 1..1: c;\nconstraint int_mod(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: tmod(7, -2) = 1 SAT"
    (match LeanFzn.Integration.solveCertified gmodNegB with
     | .sat store => arithStoreOk modRel store
     | _ => false)
  let gmodFloor := parseOrPanic
    "var -7..-7: a;\nvar 2..2: b;\nvar 1..1: c;\nconstraint int_mod(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: int_mod pinned to the floor remainder 1 UNSAT"
    (match LeanFzn.Integration.solveCertified gmodFloor with
     | .unsat => true
     | _ => false)
  let gmodZero := parseOrPanic
    "var 4..4: a;\nvar 0..0: b;\nvar -7..7: c;\nconstraint int_mod(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: int_mod zero divisor UNSAT"
    (match LeanFzn.Integration.solveCertified gmodZero with
     | .unsat => true
     | _ => false)
  -- a literal DIVISOR: c = tmod a 2
  let gmodLit := parseOrPanic
    "var 0..6: a;\nvar -1..1: c;\nconstraint int_mod(a, 2, c);\nsolve satisfy;"
  st ← st.check "certified: int_mod(a, 2, c) store has c = tmod a 2"
    (match LeanFzn.Integration.solveCertified gmodLit with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "c")).get! with
         | .int p, .int s => s == Int.tmod p 2
         | _, _ => false
     | _ => false)
  let gmodLitU := parseOrPanic
    "var -7..-7: a;\nvar 1..1: c;\nconstraint int_mod(a, 2, c);\nsolve satisfy;"
  st ← st.check "certified: int_mod(-7, 2, 1) UNSAT"
    (match LeanFzn.Integration.solveCertified gmodLitU with
     | .unsat => true
     | _ => false)

  -- int_min with a LITERAL result (the rect-euler shape): all three
  -- operands are integers, so the third operand IS min of the two.
  -- PLAN C9 remainder: the literal RESULT operand is now expanded into
  -- `minSlot` over a fresh aux slot PINNED to the literal.
  let gminLit := parseOrPanic
    "var 0..5: a;\nvar 1..4: b;\nconstraint int_min(a, b, 0);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gminLit with
  | .error _ => st ← st.check "int_min literal: compiles" false
  | .ok cp =>
      st ← st.check "int_min literal result: PLAN C9 expands to .minSlot over a pinned aux"
        (cp.constraints.any fun dc =>
          match dc with | .minSlot _ _ _ => true | _ => false)
      st ← st.check "int_min literal result: the aux slot is pinned to 0"
        (cp.domains.any fun d => match d with | [.int 0] => true | _ => false)
  st ← st.check "int_min literal: enumeration finds min = 0 (a = 0)"
    ((allAssigns [[0, 1, 2, 3, 4, 5], [1, 2, 3, 4]] : List (List Int)).any
      fun l => match l with | [p, q] => min p q == 0 | _ => false)
  st ← st.check "certified: int_min(a, b, 0) store has min a b = 0"
    (match LeanFzn.Integration.solveCertified gminLit with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get! with
         | .int p, .int q => min p q == 0
         | _, _ => false
     | _ => false)
  let gminLitU := parseOrPanic
    "var 4..5: a;\nvar 4..5: b;\nconstraint int_min(a, b, 3);\nsolve satisfy;"
  st ← st.check "int_min literal: enumeration finds no min = 3 over {4,5}"
    (!((allAssigns [[4, 5], [4, 5]] : List (List Int)).any
      fun l => match l with | [p, q] => min p q == 3 | _ => false))
  st ← st.check "certified: int_min(a, b, 3) over {4,5} UNSAT"
    (match LeanFzn.Integration.solveCertified gminLitU with
     | .unsat => true
     | _ => false)
  -- the EQUAL-value edge case with a literal second operand:
  -- c = min a 3 at a = 3 is 3
  let gminEq := parseOrPanic
    "var 3..3: a;\nvar 0..9: c;\nconstraint int_min(a, 3, c);\nsolve satisfy;"
  st ← st.check "certified: int_min(3, 3, c) store has c = 3"
    (match LeanFzn.Integration.solveCertified gminEq with
     | .sat store =>
         match (store (Ident.mk "c")).get! with
         | .int s => s == 3
         | _ => false
     | _ => false)

  -- int_max with a literal FIRST operand (the rect-euler
  -- `int_max(0, x, y)` shape): c = max a 0
  let gmaxMix := parseOrPanic
    "var 1..5: a;\nvar 0..5: c;\nconstraint int_max(a, 0, c);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gmaxMix with
  | .error _ => st ← st.check "int_max literal: compiles" false
  | .ok cp =>
      st ← st.check "int_max literal: PLAN C9 compiles to .maxSlot over a pinned aux"
        (cp.constraints.any fun dc =>
          match dc with | .maxSlot _ _ _ => true | _ => false)
  st ← st.check "certified: int_max(a, 0, c) store has c = max a 0"
    (match LeanFzn.Integration.solveCertified gmaxMix with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "c")).get! with
         | .int p, .int s => s == max p 0
         | _, _ => false
     | _ => false)
  let gmaxU := parseOrPanic
    "var 1..2: a;\nvar 5..5: c;\nconstraint int_max(a, 0, c);\nsolve satisfy;"
  st ← st.check "certified: int_max(a, 0, 5) over a ∈ {1,2} UNSAT"
    (match LeanFzn.Integration.solveCertified gmaxU with
     | .unsat => true
     | _ => false)
  -- NEGATIVE operands with a literal: c = max a (-3) at a = -5 is -3
  let gmaxNeg := parseOrPanic
    "var -5..-5: a;\nvar -5..-1: c;\nconstraint int_max(a, -3, c);\nsolve satisfy;"
  st ← st.check "certified: int_max(-5, -3, c) store has c = -3"
    (match LeanFzn.Integration.solveCertified gmaxNeg with
     | .sat store =>
         match (store (Ident.mk "c")).get! with
         | .int s => s == -3
         | _ => false
     | _ => false)

  -- PLAN C9 remainder: the LITERAL-RESULT shapes (`int_min(a, b, k)` /
  -- `int_max(a, b, k)`, the literal in the third position), expanded
  -- to `.minSlot`/`.maxSlot` over a fresh aux slot PINNED to `k`.
  let gminRRK := parseOrPanic
    "var 2..3: a;\nvar 5..6: b;\nconstraint int_min(a, b, 2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gminRRK with
  | .error _ => st ← st.check "int_min literal-result: compiles" false
  | .ok cp =>
      st ← st.check "int_min literal-result: PLAN C9 expands to .minSlot over a pinned aux"
        (cp.constraints.any (fun dc =>
          match dc with | .minSlot _ _ _ => true | _ => false) ∧
         cp.domains.any (fun d => match d with | [.int 2] => true | _ => false))
  st ← st.check "certified: int_min(a, b, 2) store has min a b = 2 (a = 2)"
    (match LeanFzn.Integration.solveCertified gminRRK with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get! with
         | .int p, .int q => min p q == 2
         | _, _ => false
     | _ => false)
  let gminRRKU := parseOrPanic
    "var 5..6: a;\nvar 5..6: b;\nconstraint int_min(a, b, 2);\nsolve satisfy;"
  st ← st.check "certified: int_min(a, b, 2) over {5,6} UNSAT"
    (match LeanFzn.Integration.solveCertified gminRRKU with
     | .unsat => true
     | _ => false)
  let gmaxRRK := parseOrPanic
    "var 5..6: a;\nvar 2..3: b;\nconstraint int_max(a, b, 6);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gmaxRRK with
  | .error _ => st ← st.check "int_max literal-result: compiles" false
  | .ok cp =>
      st ← st.check "int_max literal-result: PLAN C9 expands to .maxSlot over a pinned aux"
        (cp.constraints.any (fun dc =>
          match dc with | .maxSlot _ _ _ => true | _ => false) ∧
         cp.domains.any (fun d => match d with | [.int 6] => true | _ => false))
  st ← st.check "certified: int_max(a, b, 6) store has max a b = 6 (a = 6)"
    (match LeanFzn.Integration.solveCertified gmaxRRK with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get! with
         | .int p, .int q => max p q == 6
         | _, _ => false
     | _ => false)
  let gmaxRRKU := parseOrPanic
    "var 2..3: a;\nvar 2..3: b;\nconstraint int_max(a, b, 6);\nsolve satisfy;"
  st ← st.check "certified: int_max(a, b, 6) over {2,3} UNSAT"
    (match LeanFzn.Integration.solveCertified gmaxRRKU with
     | .unsat => true
     | _ => false)
  -- the negative-literal-results corner: min(a, b, -3) with a = -3
  let gminRRKNeg := parseOrPanic
    "var -3..-2: a;\nvar -1..0: b;\nconstraint int_min(a, b, -3);\nsolve satisfy;"
  st ← st.check "certified: int_min(a, b, -3) store has min a b = -3"
    (match LeanFzn.Integration.solveCertified gminRRKNeg with
     | .sat store =>
         match (store (Ident.mk "a")).get!, (store (Ident.mk "b")).get! with
         | .int p, .int q => min p q == -3
         | _, _ => false
     | _ => false)
  -- both slots pinned to the literal value: min(2, 2, 2) is satisfiable
  let gminRRKEq := parseOrPanic
    "var 2..2: a;\nvar 2..2: b;\nconstraint int_min(a, b, 2);\nsolve satisfy;"
  st ← st.check "certified: int_min(2, 2, 2) SAT"
    (match LeanFzn.Integration.solveCertified gminRRKEq with
     | .sat _ => true
     | _ => false)
  -- the all-literal corner stays on the checked `minPair` path (a
  -- ground constraint the leaf decides): min(1, 2, 3) is false
  let gminGround := parseOrPanic
    "var 0..0: a;\nconstraint int_min(1, 2, 3);\nsolve satisfy;"
  st ← st.check "certified: ground int_min(1, 2, 3) UNSAT"
    (match LeanFzn.Integration.solveCertified gminGround with
     | .unsat => true
     | _ => false)

  -- array_int_maximum over a VARIABLE array: m = max x y, including
  -- the all-negative case (the max of negatives is the largest one)
  let gmaxVar := parseOrPanic
    "var -2..2: x;\nvar -2..2: y;\narray [1..2] of var int: xs = [x, y];\nvar -2..2: m;\nconstraint array_int_maximum(m, xs);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gmaxVar with
  | .error _ => st ← st.check "array_int_maximum: compiles" false
  | .ok cp =>
      -- PLAN C9 remainder: the 2-element array is INLINED to a literal
      -- array by the compiler and the shape now rewrites to .maxSlot
      -- (the .maxGen leaf route is exercised by the 3-element model
      -- below)
      st ← st.check "array_int_maximum: 2-element array rewrites to .maxSlot"
        (cp.constraints.any fun dc =>
          match dc with | .maxSlot .. => true | _ => false)
  st ← st.check "array_int_maximum: enumeration finds m = max x y"
    ((allAssigns [[-2, -1, 0, 1, 2], [-2, -1, 0, 1, 2],
        [-2, -1, 0, 1, 2]] : List (List Int)).any fun l =>
      match l with | [xv, yv, mv] => mv == max xv yv | _ => false)
  st ← st.check "certified: array_int_maximum(m, [x, y]) store has m = max x y"
    (match LeanFzn.Integration.solveCertified gmaxVar with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
             (store (Ident.mk "m")).get! with
         | .int xv, .int yv, .int mv => mv == max xv yv
         | _, _, _ => false
     | _ => false)
  let gmaxNegArr := parseOrPanic
    "var -9..-9: x;\nvar -2..-2: y;\narray [1..2] of var int: xs = [x, y];\nvar -9..-1: m;\nconstraint array_int_maximum(m, xs);\nsolve satisfy;"
  st ← st.check "certified: array_int_maximum of {-9, -2} store has m = -2"
    (match LeanFzn.Integration.solveCertified gmaxNegArr with
     | .sat store =>
         match (store (Ident.mk "m")).get! with
         | .int mv => mv == -2
         | _ => false
     | _ => false)
  let gmaxVarU := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\narray [1..2] of var int: xs = [x, y];\nvar 0..0: m;\nconstraint array_int_maximum(m, xs);\nsolve satisfy;"
  st ← st.check "certified: array_int_maximum pinned to 0 with x, y ≥ 1 UNSAT"
    (match LeanFzn.Integration.solveCertified gmaxVarU with
     | .unsat => true
     | _ => false)
  -- the EMPTY array: `maxValue [] = none`, so the source predicate is
  -- unsatisfiable for every m
  let gmaxNil := parseOrPanic
    "var 0..0: m;\nconstraint array_int_maximum(m, []);\nsolve satisfy;"
  st ← st.check "certified: array_int_maximum on the empty array UNSAT"
    (match LeanFzn.Integration.solveCertified gmaxNil with
     | .unsat => true
     | _ => false)

  -- array_int_minimum over a VARIABLE array: m = min x y
  let gminVar := parseOrPanic
    "var -2..2: x;\nvar -2..2: y;\narray [1..2] of var int: xs = [x, y];\nvar -2..2: m;\nconstraint array_int_minimum(m, xs);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gminVar with
  | .error _ => st ← st.check "array_int_minimum: compiles" false
  | .ok cp =>
      -- PLAN C9 remainder: the 2-element array now rewrites to .minSlot
      -- (the .minGen leaf route is exercised by the 3-element model
      -- below)
      st ← st.check "array_int_minimum: 2-element array rewrites to .minSlot"
        (cp.constraints.any fun dc =>
          match dc with | .minSlot .. => true | _ => false)
  -- the 3-element array has no binary chain: it stays leaf-enforced
  let gminVar3 := parseOrPanic
    "var -2..2: x;\nvar -2..2: y;\nvar -2..2: z;\narray [1..3] of var int: xs = [x, y, z];\nvar -2..2: m;\nconstraint array_int_minimum(m, xs);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gminVar3 with
  | .error _ => st ← st.check "array_int_minimum 3-element: compiles" false
  | .ok cp =>
      st ← st.check "array_int_minimum: 3-element array stays on .minGen"
        (cp.constraints.any fun dc =>
          match dc with | .minGen .. => true | _ => false)
  st ← st.check "certified: array_int_minimum 3-element store has m = min of three"
    (match LeanFzn.Integration.solveCertified gminVar3 with
     | .sat store =>
         match (store (Ident.mk "m")).get! with
         | .int mv =>
             match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
                 (store (Ident.mk "z")).get! with
             | .int xv, .int yv, .int zv => mv == min (min xv yv) zv
             | _, _, _ => false
         | _ => false
     | _ => false)
  let gmaxVar3 := parseOrPanic
    "var -2..2: x;\nvar -2..2: y;\nvar -2..2: z;\narray [1..3] of var int: xs = [x, y, z];\nvar -2..2: m;\nconstraint array_int_maximum(m, xs);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull gmaxVar3 with
  | .error _ => st ← st.check "array_int_maximum 3-element: compiles" false
  | .ok cp =>
      st ← st.check "array_int_maximum: 3-element array stays on .maxGen"
        (cp.constraints.any fun dc =>
          match dc with | .maxGen .. => true | _ => false)
  st ← st.check "certified: array_int_maximum 3-element store has m = max of three"
    (match LeanFzn.Integration.solveCertified gmaxVar3 with
     | .sat store =>
         match (store (Ident.mk "m")).get! with
         | .int mv =>
             match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
                 (store (Ident.mk "z")).get! with
             | .int xv, .int yv, .int zv => mv == max (max xv yv) zv
             | _, _, _ => false
         | _ => false
     | _ => false)
  st ← st.check "array_int_minimum: enumeration finds m = min x y"
    ((allAssigns [[-2, -1, 0, 1, 2], [-2, -1, 0, 1, 2],
        [-2, -1, 0, 1, 2]] : List (List Int)).any fun l =>
      match l with | [xv, yv, mv] => mv == min xv yv | _ => false)
  st ← st.check "certified: array_int_minimum(m, [x, y]) store has m = min x y"
    (match LeanFzn.Integration.solveCertified gminVar with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
             (store (Ident.mk "m")).get! with
         | .int xv, .int yv, .int mv => mv == min xv yv
         | _, _, _ => false
     | _ => false)
  let gminNegArr := parseOrPanic
    "var -9..-9: x;\nvar -2..-2: y;\narray [1..2] of var int: xs = [x, y];\nvar -9..-1: m;\nconstraint array_int_minimum(m, xs);\nsolve satisfy;"
  st ← st.check "certified: array_int_minimum of {-9, -2} store has m = -9"
    (match LeanFzn.Integration.solveCertified gminNegArr with
     | .sat store =>
         match (store (Ident.mk "m")).get! with
         | .int mv => mv == -9
         | _ => false
     | _ => false)
  let gminVarU := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\narray [1..2] of var int: xs = [x, y];\nvar 5..5: m;\nconstraint array_int_minimum(m, xs);\nsolve satisfy;"
  st ← st.check "certified: array_int_minimum pinned to 5 with x, y ≤ 2 UNSAT"
    (match LeanFzn.Integration.solveCertified gminVarU with
     | .unsat => true
     | _ => false)
  let gminNil := parseOrPanic
    "var 0..0: m;\nconstraint array_int_minimum(m, []);\nsolve satisfy;"
  st ← st.check "certified: array_int_minimum on the empty array UNSAT"
    (match LeanFzn.Integration.solveCertified gminNil with
     | .unsat => true
     | _ => false)

  -- PLAN C9 remainder: the TWO-ELEMENT ARRAY shapes
  -- (`array_int_minimum(r, [x, y])` / `array_int_maximum(r, [x, y])`)
  -- are rewritten into `int_min(x, y, r)` / `int_max(x, y, r)` over the
  -- model's OWN slots (no aux slot), so they reach the explained
  -- `minSlot`/`maxSlot` propagators and the LCG route. The rewrite
  -- fires on the literal-array AST `[Expr.basic (.ident r),
  -- Expr.array [BasicExpr.ident x, BasicExpr.ident y]]` (the parser's
  -- representation, checked below by the `.minSlot`/`.maxSlot` route).
  let routeMinGen2 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 0..9: r;\nconstraint array_int_minimum(r, [x, y]);\nconstraint int_eq(r, 1);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen2 with
  | .error _ => st ← st.check "route: array_int_minimum 2-array compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_minimum 2-array expands to .minSlot"
        (cp.constraints.any (fun dc =>
           match dc with | .minSlot _ _ _ => true | _ => false) ∧
         !(cp.constraints.any (fun dc =>
           match dc with | .minGen .. => true | _ => false)))
      st ← st.check "route: array_int_minimum 2-array uses the model slots only"
        (cp.names == ["x", "y", "r"])
      st ← st.check "route: array_int_minimum 2-array passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_minimum 2-array: r = min x y at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int yv, .int rv] => rv == 1 && rv == min xv yv
          | _ => false)
      st ← st.check
        "route: array_int_minimum 2-array: exactly 5 solutions by enumeration"
        (sols.length == 5)
      st ← st.check
        "route: array_int_minimum 2-array SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: array_int_minimum(r, [x, y]) store has r = min x y"
    (match LeanFzn.Integration.solveCertified routeMinGen2 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
             (store (Ident.mk "r")).get! with
         | .int xv, .int yv, .int rv => rv == min xv yv
         | _, _, _ => false
     | _ => false)
  let routeMinGen2U := parseOrPanic
    "var 2..3: x;\nvar 2..3: y;\nvar 1..1: r;\nconstraint array_int_minimum(r, [x, y]);\nconstraint int_lt(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen2U with
  | .error _ => st ← st.check "route: array_int_minimum 2-array UNSAT compiles" false
  | .ok cp =>
      st ← st.check
        "route: array_int_minimum 2-array UNSAT by exhaustive enumeration"
        ((allAssigns cp.domains).filter (accepts cp) |>.isEmpty)
      st ← st.check "route: array_int_minimum 2-array UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  st ← st.check "certified: array_int_minimum with min > r UNSAT"
    (match LeanFzn.Integration.solveCertified routeMinGen2U with
     | .unsat => true
     | _ => false)
  let routeMaxGen2 := parseOrPanic
    "var 1..4: x;\nvar 1..4: y;\nvar 0..9: r;\nconstraint array_int_maximum(r, [x, y]);\nconstraint int_lt(x, y);\nconstraint int_eq(r, 4);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxGen2 with
  | .error _ => st ← st.check "route: array_int_maximum 2-array compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_maximum 2-array expands to .maxSlot"
        (cp.constraints.any (fun dc =>
           match dc with | .maxSlot _ _ _ => true | _ => false) ∧
         !(cp.constraints.any (fun dc =>
           match dc with | .maxGen .. => true | _ => false)))
      st ← st.check "route: array_int_maximum 2-array passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_maximum 2-array: r = max x y at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int yv, .int rv] => rv == 4 && rv == max xv yv
          | _ => false)
      -- coupled with int_lt: y = 4 with x ∈ {1,2,3} is 3 assignments
      st ← st.check
        "route: array_int_maximum 2-array: exactly 3 solutions by enumeration"
        (sols.length == 3)
      st ← st.check
        "route: array_int_maximum 2-array SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: array_int_maximum(r, [x, y]) store has r = max x y"
    (match LeanFzn.Integration.solveCertified routeMaxGen2 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
             (store (Ident.mk "r")).get! with
         | .int xv, .int yv, .int rv => rv == max xv yv
         | _, _, _ => false
     | _ => false)
  let routeMaxGen2U := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nvar 5..5: r;\nconstraint array_int_maximum(r, [x, y]);\nsolve satisfy;"
  st ← st.check "certified: array_int_maximum with max < r UNSAT"
    (match LeanFzn.Integration.solveCertified routeMaxGen2U with
     | .unsat => true
     | _ => false)
  -- the NEGATIVE corner: min of {-9, -2} is -9 (and max is -2)
  let routeMinGen2Neg := parseOrPanic
    "var -9..-9: x;\nvar -2..-2: y;\nvar -9..-1: r;\nconstraint array_int_minimum(r, [x, y]);\nsolve satisfy;"
  st ← st.check "certified: array_int_minimum(r, [-9, -2]) store has r = -9"
    (match LeanFzn.Integration.solveCertified routeMinGen2Neg with
     | .sat store =>
         match (store (Ident.mk "r")).get! with
         | .int rv => rv == -9
         | _ => false
     | _ => false)
  -- n = 3 is NOT rewritten (no binary chain yet): it stays the
  -- leaf-enforced `.minGen`, and the verdict is still correct
  let routeMinGen3 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 0..9: r;\nconstraint array_int_minimum(r, [x, y, z]);\nconstraint int_eq(r, 1);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen3 with
  | .error _ => st ← st.check "route: array_int_minimum 3-array compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_minimum 3-array stays leaf-enforced (.minGen)"
        (cp.constraints.any (fun dc =>
          match dc with | .minGen .. => true | _ => false))
  st ← st.check "certified: array_int_minimum(r, [x, y, z]) store has r = 1"
    (match LeanFzn.Integration.solveCertified routeMinGen3 with
     | .sat store =>
         match (store (Ident.mk "r")).get! with
         | .int rv => rv == 1
         | _ => false
     | _ => false)

  -- ## PLAN L0c: the `propCheck` families on the public LCG route
  -- (`int_lin_ne`, `int_le_reif`, `int_max`). Every case compiles the
  -- source, checks that the mixed LCG route gate accepts the compiled
  -- problem (`lcgRouteGateMixed`), and checks that the LCG-route
  -- verdict (`solveCompiledLcg`) agrees with exhaustive enumeration of
  -- the declared domains (SAT witnesses by membership, UNSAT by
  -- emptiness).

  -- int_lin_ne SAT: x ≠ 2 over 1..3 (witness x = 1)
  let routeLinne := parseOrPanic
    "var 1..3: x;\nconstraint int_lin_ne([1],[x],2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinne with
  | .error _ => st ← st.check "route: int_lin_ne compiles" false
  | .ok cp =>
      st ← st.check "route: int_lin_ne model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_lin_ne SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_lin_ne UNSAT (coupled): x + y ≤ 2 forces x + y = 2 over 1..3,
  -- which violates x + y ≠ 2; both families are on the LCG route now
  let routeLinneU := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_lin_le([1,1],[x,y],2);\nconstraint int_lin_ne([1,1],[x,y],2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinneU with
  | .error _ => st ← st.check "route: coupled int_lin_ne UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: coupled int_lin_ne UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: coupled int_lin_ne UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: coupled int_lin_ne UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_le_reif SAT: b pinned true forces x ≤ y; x < y satisfies it
  let routeLeReif := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_le_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_lt(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLeReif with
  | .error _ => st ← st.check "route: int_le_reif compiles" false
  | .ok cp =>
      st ← st.check "route: int_le_reif model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_le_reif SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_le_reif UNSAT: b pinned true forces x ≤ y, but y < x
  let routeLeReifU := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_le_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_lt(y, x);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLeReifU with
  | .error _ => st ← st.check "route: pinned int_le_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: pinned int_le_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: pinned int_le_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: pinned int_le_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_eq_reif SAT: b pinned true forces x = y; x = y satisfies it
  let routeEqReif := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_eq_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_eq(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeEqReif with
  | .error _ => st ← st.check "route: int_eq_reif compiles" false
  | .ok cp =>
      st ← st.check "route: int_eq_reif model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_eq_reif SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_eq_reif UNSAT: b pinned true forces x = y, but x ≠ y
  let routeEqReifU := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_eq_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_ne(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeEqReifU with
  | .error _ => st ← st.check "route: pinned int_eq_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: pinned int_eq_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: pinned int_eq_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: pinned int_eq_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_ne_reif SAT: b pinned true forces x ≠ y; x ≠ y satisfies it
  let routeNeReif := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_ne_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_ne(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeNeReif with
  | .error _ => st ← st.check "route: int_ne_reif compiles" false
  | .ok cp =>
      st ← st.check "route: int_ne_reif model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_ne_reif SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_ne_reif UNSAT: b pinned true forces x ≠ y, but x = y
  let routeNeReifU := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_ne_reif(x, y, b);\nconstraint bool_clause([b], []);\nconstraint int_eq(x, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeNeReifU with
  | .error _ => st ← st.check "route: pinned int_ne_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: pinned int_ne_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: pinned int_ne_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: pinned int_ne_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- ## PLAN L5: the linear reified families on the public LCG route
  -- (`int_lin_eq_reif`, `int_lin_ne_reif`). Same shape as the L0c/L4
  -- groups: compile the source, check that the mixed LCG route gate
  -- accepts the compiled problem (`lcgRouteGateMixed`), and compare the
  -- LCG-route verdict (`solveCompiledLcg`) with exhaustive enumeration
  -- of the declared domains (SAT witnesses by membership, UNSAT by
  -- emptiness).

  -- int_lin_eq_reif SAT (pin true): 2x + y = 3 with b = true (x = y = 1)
  let routeLinEqReif := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_lin_eq_reif([2,1],[x,y],3,b);\nconstraint bool_clause([b], []);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinEqReif with
  | .error _ => st ← st.check "route: int_lin_eq_reif compiles" false
  | .ok cp =>
      st ← st.check "route: int_lin_eq_reif model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_lin_eq_reif SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_lin_eq_reif UNSAT (pin true): x + y = 7 is infeasible over 0..3
  let routeLinEqReifU := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar bool: b;\nconstraint int_lin_eq_reif([1,1],[x,y],7,b);\nconstraint bool_clause([b], []);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinEqReifU with
  | .error _ => st ← st.check "route: pinned int_lin_eq_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: pinned int_lin_eq_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: pinned int_lin_eq_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: pinned int_lin_eq_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_lin_eq_reif UNSAT (pin false): b = false requires x + y ≠ 3, but
  -- x = 1, y = 2 pin x + y = 3
  let routeLinEqReifF := parseOrPanic
    "var 1..1: x;\nvar 2..2: y;\nvar bool: b;\nconstraint int_lin_eq_reif([1,1],[x,y],3,b);\nconstraint bool_clause([], [b]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinEqReifF with
  | .error _ => st ← st.check "route: false-pinned int_lin_eq_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: false-pinned int_lin_eq_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: false-pinned int_lin_eq_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: false-pinned int_lin_eq_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_lin_ne_reif SAT (pin true): x − y ≠ 0 with b = true (x = 0, y = 1)
  let routeLinNeReif := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar bool: b;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,b);\nconstraint bool_clause([b], []);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinNeReif with
  | .error _ => st ← st.check "route: int_lin_ne_reif compiles" false
  | .ok cp =>
      st ← st.check "route: int_lin_ne_reif model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_lin_ne_reif SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_lin_ne_reif UNSAT (pin true): b = true requires x − y ≠ 0, but
  -- x = y = 1 pin x − y = 0
  let routeLinNeReifU := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar bool: b;\nconstraint int_lin_ne_reif([1,-1],[x,y],0,b);\nconstraint bool_clause([b], []);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinNeReifU with
  | .error _ => st ← st.check "route: pinned int_lin_ne_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: pinned int_lin_ne_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: pinned int_lin_ne_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: pinned int_lin_ne_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_lin_ne_reif UNSAT (pin false): b = false requires x + y = 1, but
  -- x = y = 0 pin x + y = 0
  let routeLinNeReifF := parseOrPanic
    "var 0..0: x;\nvar 0..0: y;\nvar bool: b;\nconstraint int_lin_ne_reif([1,1],[x,y],1,b);\nconstraint bool_clause([], [b]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeLinNeReifF with
  | .error _ => st ← st.check "route: false-pinned int_lin_ne_reif UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: false-pinned int_lin_ne_reif UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: false-pinned int_lin_ne_reif UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: false-pinned int_lin_ne_reif UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_max SAT: z = max(x, y) with z ≤ 2 (x = y = z = 0 works)
  let routeMax := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar 0..3: z;\nconstraint int_max(x, y, z);\nconstraint int_le(z, 2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMax with
  | .error _ => st ← st.check "route: int_max compiles" false
  | .ok cp =>
      st ← st.check "route: int_max model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_max SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_max UNSAT: z = max(x, y) must equal x or y, so z ≠ x ∧ z ≠ y
  -- is impossible
  let routeMaxU := parseOrPanic
    "var 0..3: x;\nvar 0..3: y;\nvar 0..3: z;\nconstraint int_max(x, y, z);\nconstraint int_ne(z, x);\nconstraint int_ne(z, y);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxU with
  | .error _ => st ← st.check "route: int_max UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: int_max UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_max UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_max UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- int_times SAT: x · y = z over y ∈ [1,4], z ∈ [0,12] — the propTimes
  -- sign arm (0 < y, z ≥ 0) deduces x ≥ 0 (x = 0, y = 1, z = 0 works)
  let routeTimes := parseOrPanic
    "var -3..3: x;\nvar 1..4: y;\nvar 0..12: z;\nconstraint int_times(x, y, z);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeTimes with
  | .error _ => st ← st.check "route: int_times compiles" false
  | .ok cp =>
      st ← st.check "route: int_times model passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_times SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)

  -- int_times UNSAT: x = 1 · y ∈ {2,3} forces z ∈ {2,3}, outside z ∈ [0,1]
  -- (the propTimes corner arm refutes it)
  let routeTimesU := parseOrPanic
    "var 1..1: x;\nvar 2..3: y;\nvar 0..1: z;\nconstraint int_times(x, y, z);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeTimesU with
  | .error _ => st ← st.check "route: int_times UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: int_times UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: int_times UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: int_times UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  -- ## PLAN L8: the strengthened `all_different` — the fixed-slot VALUE
  -- ELIMINATIONS. These models exercise the new `.implied` emissions on
  -- the public LCG route: each checks the mixed route gate, the verdict
  -- against exhaustive enumeration, and the certified store.

  -- SAT (c = 5 ∉ {0,1}): x is pinned to 5, so the value 5 is eliminated
  -- from y over 4..6 — the certified store must have y ≠ 5
  let routeAdElim5 := parseOrPanic
    "var 5..5: x;\nvar 4..6: y;\nconstraint all_different([x, y]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElim5 with
  | .error _ => st ← st.check "route: all_different elimination (c=5) compiles" false
  | .ok cp =>
      st ← st.check "route: all_different elimination (c=5) passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: all_different elimination (c=5) SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: all_different elimination store has x = 5, y ≠ 5"
    (match LeanFzn.Integration.solveCertified routeAdElim5 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int xv, .int yv => xv = 5 ∧ yv ≠ 5
         | _, _ => false
     | _ => false)

  -- SAT (c = 0 ∈ {0,1}): the Boolean-shape branch of the reason clause;
  -- x = 0 is eliminated from y over 0..2
  let routeAdElim0 := parseOrPanic
    "var 0..0: x;\nvar 0..2: y;\nconstraint all_different([x, y]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElim0 with
  | .error _ => st ← st.check "route: all_different elimination (c=0) compiles" false
  | .ok cp =>
      st ← st.check "route: all_different elimination (c=0) passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: all_different elimination (c=0) SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: all_different elimination store has x = 0, y ≠ 0"
    (match LeanFzn.Integration.solveCertified routeAdElim0 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int xv, .int yv => xv = 0 ∧ yv ≠ 0
         | _, _ => false
     | _ => false)

  -- SAT (3 slots, elimination + bound interplay): x = 1 eliminates 1
  -- from y and z; y ≤ 2 then pins y = 2, and the distinctness pins z = 3
  let routeAdElim3 := parseOrPanic
    "var 1..1: x;\nvar 1..3: y;\nvar 1..3: z;\nconstraint all_different([x, y, z]);\nconstraint int_le(y, 2);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElim3 with
  | .error _ => st ← st.check "route: all_different elimination (3 slots) compiles" false
  | .ok cp =>
      st ← st.check "route: all_different elimination (3 slots) passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: all_different elimination (3 slots) SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: all_different elimination (3 slots) store has x = 1, y = 2, z = 3"
    (match LeanFzn.Integration.solveCertified routeAdElim3 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get!,
             (store (Ident.mk "z")).get! with
         | .int xv, .int yv, .int zv => xv = 1 ∧ yv = 2 ∧ zv = 3
         | _, _, _ => false
     | _ => false)

  -- UNSAT: x = y = 1 makes the elimination empty y's domain (the
  -- pigeonhole does NOT fire: 3 slots over the 3 values {1, 3, 4})
  let routeAdElimU := parseOrPanic
    "var 1..1: x;\nvar 1..1: y;\nvar 3..4: z;\nconstraint all_different([x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElimU with
  | .error _ => st ← st.check "route: all_different elimination UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: all_different elimination UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: all_different elimination UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: all_different elimination UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  st ← st.check "certified: all_different elimination UNSAT"
    (match LeanFzn.Integration.solveCertified routeAdElimU with
     | .unsat => true
     | _ => false)

  -- UNSAT: two slots pinned to the SAME value 5 (with a third free slot
  -- keeping the pigeonhole count at 3 ≤ 3), so the elimination chain
  -- empties the second pinned slot's domain
  let routeAdElimU2 := parseOrPanic
    "var 5..5: x;\nvar 4..6: y;\nvar 5..5: z;\nconstraint all_different([x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElimU2 with
  | .error _ => st ← st.check "route: all_different elimination UNSAT (two pins) compiles" false
  | .ok cp =>
      st ← st.check "route: all_different elimination UNSAT (two pins) passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check "route: all_different elimination UNSAT (two pins) by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: all_different elimination UNSAT (two pins) on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)
  st ← st.check "certified: all_different elimination UNSAT (two pins)"
    (match LeanFzn.Integration.solveCertified routeAdElimU2 with
     | .unsat => true
     | _ => false)

  -- DIRECT PROPAGATION CHECK (the DoD's "P > 0"): one LCG propagation
  -- loop on the compiled model's initial state must REMOVE 5 from y
  -- (the new `.implied` emission), i.e. y's domain becomes exactly
  -- [.int 4, .int 6]
  match LeanFzn.Compiler.compileModelFull routeAdElim5 with
  | .error _ => st ← st.check "prop: all_different elimination narrows y" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: all_different elimination narrows y to [4, 6]"
        (match st1.domains.getD 1 [] with
         | [.int 4, .int 6] => true
         | _ => false)

  -- CONTROL: a MULTI-valued first slot is no elimination source (the
  -- scan needs a raw singleton), so y stays [.int 4, .int 5, .int 6]
  let routeAdElimCtl := parseOrPanic
    "var 4..5: x;\nvar 4..6: y;\nconstraint all_different([x, y]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeAdElimCtl with
  | .error _ => st ← st.check "prop: all_different multi-valued control" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: all_different multi-valued source does NOT narrow y"
        (match st1.domains.getD 1 [] with
         | [.int 4, .int 5, .int 6] => true
         | _ => false)

  -- ## PLAN C9-remainder: the n-ary `array_int_minimum`/`array_int_maximum`
  -- result propagators `propMinGen`/`propMaxGen` (the `.minGen`/`.maxGen`
  -- families). n ≥ 3 arrays have no binary rewrite, so the compiled
  -- problem keeps the n-ary constraint, and the LCG route now runs the
  -- dedicated attained-operand propagators (the direct propagation
  -- checks below show them firing) instead of the retired `propCheck`.

  -- SAT: r = min(x, y, z) with r pinned to 1 (19 of the 27 triples)
  let routeMinGen3R := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 0..9: r;\nconstraint array_int_minimum(r, [x, y, z]);\nconstraint int_eq(r, 1);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen3R with
  | .error _ => st ← st.check "route: array_int_minimum 3-array compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_minimum 3-array stays on .minGen (n-ary)"
        (cp.constraints.any (fun dc =>
           match dc with | .minGen .. => true | _ => false) ∧
         !(cp.constraints.any (fun dc =>
           match dc with | .minSlot .. => true | _ => false)))
      st ← st.check "route: array_int_minimum 3-array passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_minimum 3-array: r = min x y z at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int yv, .int zv, .int rv] =>
              rv == 1 && rv == min (min xv yv) zv
          | _ => false)
      st ← st.check
        "route: array_int_minimum 3-array: exactly 19 solutions by enumeration"
        (sols.length == 19)
      st ← st.check
        "route: array_int_minimum 3-array SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: array_int_minimum(r, [x, y, z]) with r = 1 store has r = 1"
    (match LeanFzn.Integration.solveCertified routeMinGen3R with
     | .sat store =>
         match (store (Ident.mk "r")).get! with
         | .int rv => rv == 1
         | _ => false
     | _ => false)

  -- UNSAT: r = min(x, y, z) with every operand ≥ 2 but r pinned to 1
  let routeMinGen3RU := parseOrPanic
    "var 2..3: x;\nvar 2..3: y;\nvar 2..3: z;\nvar 1..1: r;\nconstraint array_int_minimum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen3RU with
  | .error _ => st ← st.check "route: array_int_minimum 3-array UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_minimum 3-array UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_minimum 3-array UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: array_int_minimum 3-array UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- SAT: r = max(x, y, z) pinned to 4, coupled with x < y (15 triples)
  let routeMaxGen3R := parseOrPanic
    "var 1..4: x;\nvar 1..4: y;\nvar 1..4: z;\nvar 0..9: r;\nconstraint array_int_maximum(r, [x, y, z]);\nconstraint int_lt(x, y);\nconstraint int_eq(r, 4);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxGen3R with
  | .error _ => st ← st.check "route: array_int_maximum 3-array compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_maximum 3-array stays on .maxGen (n-ary)"
        (cp.constraints.any (fun dc =>
           match dc with | .maxGen .. => true | _ => false) ∧
         !(cp.constraints.any (fun dc =>
           match dc with | .maxSlot .. => true | _ => false)))
      st ← st.check "route: array_int_maximum 3-array passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_maximum 3-array: r = max x y z at EVERY accepted assignment"
        (sols.all fun a =>
          match a with
          | [.int xv, .int yv, .int zv, .int rv] =>
              rv == 4 && rv == max (max xv yv) zv
          | _ => false)
      st ← st.check
        "route: array_int_maximum 3-array: exactly 15 solutions by enumeration"
        (sols.length == 15)
      st ← st.check
        "route: array_int_maximum 3-array SAT witness accepted by the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .sat a => sols.contains a
         | _ => false)
  st ← st.check "certified: array_int_maximum(r, [x, y, z]) with r = 4 store has r = 4"
    (match LeanFzn.Integration.solveCertified routeMaxGen3R with
     | .sat store =>
         match (store (Ident.mk "r")).get! with
         | .int rv => rv == 4
         | _ => false
     | _ => false)

  -- UNSAT: r = max(x, y, z) with every operand ≤ 2 but r pinned to 5
  let routeMaxGen3RU := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nvar 1..2: z;\nvar 5..5: r;\nconstraint array_int_maximum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxGen3RU with
  | .error _ => st ← st.check "route: array_int_maximum 3-array UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: array_int_maximum 3-array UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: array_int_maximum 3-array UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: array_int_maximum 3-array UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- 4-element COUPLED UNSAT: mn = min and mx = max over the SAME four
  -- operands, with mx < mn (impossible: min ≤ max)
  let routeGen4CoupledU := parseOrPanic
    "var 1..5: w;\nvar 1..5: x;\nvar 1..5: y;\nvar 1..5: z;\nvar 0..9: mn;\nvar 0..9: mx;\nconstraint array_int_minimum(mn, [w, x, y, z]);\nconstraint array_int_maximum(mx, [w, x, y, z]);\nconstraint int_lt(mx, mn);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeGen4CoupledU with
  | .error _ => st ← st.check "route: coupled 4-array extremes UNSAT compiles" false
  | .ok cp =>
      st ← st.check "route: coupled 4-array extremes UNSAT passes lcgRouteGateMixed"
        (LeanFzn.Integration.lcgRouteGateMixed cp)
      let sols := (allAssigns cp.domains).filter (accepts cp)
      st ← st.check
        "route: coupled 4-array extremes UNSAT by exhaustive enumeration"
        sols.isEmpty
      st ← st.check "route: coupled 4-array extremes UNSAT on the LCG route"
        (match LeanFzn.Integration.solveCompiledLcg cp with
         | .unsat => true
         | _ => false)

  -- DIRECT PROPAGATION CHECK (the registered `propMinGen` fires): one LCG
  -- propagation loop on the initial state must narrow r = min(x, y, z)
  -- from [0..9] to [1..3] (r ≥ the minimum operand lower bound and
  -- r ≤ the maximum operand upper bound, both `.implied` emissions)
  let routeMinGen3Narrow := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 0..9: r;\nconstraint array_int_minimum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen3Narrow with
  | .error _ => st ← st.check "prop: n-ary array_int_minimum narrowing" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: n-ary array_int_minimum narrows r to [1, 3]"
        (match st1.domains.getD 3 [] with
         | [.int 1, .int 2, .int 3] => true
         | _ => false)

  -- DIRECT PROPAGATION CHECK (`propMaxGen`): the same two arms narrow
  -- r = max(x, y, z) from [0..9] to [1..3]
  let routeMaxGen3Narrow := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 0..9: r;\nconstraint array_int_maximum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxGen3Narrow with
  | .error _ => st ← st.check "prop: n-ary array_int_maximum narrowing" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: n-ary array_int_maximum narrows r to [1, 3]"
        (match st1.domains.getD 3 [] with
         | [.int 1, .int 2, .int 3] => true
         | _ => false)

  -- DIRECT CONFLICT CHECK (`propMinGen`'s lower arm): r = min(x, y, z)
  -- pinned to 0 while every operand is ≥ 1 is a reported conflict
  let routeMinGen3Conflict := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 0..0: r;\nconstraint array_int_minimum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMinGen3Conflict with
  | .error _ => st ← st.check "prop: n-ary array_int_minimum conflict" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: n-ary array_int_minimum reports the r < min conflict"
        st1.conflict.isSome

  -- DIRECT CONFLICT CHECK (`propMaxGen`'s upper arm): r = max(x, y, z)
  -- pinned to 9 while every operand is ≤ 3
  let routeMaxGen3Conflict := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nvar 9..9: r;\nconstraint array_int_maximum(r, [x, y, z]);\nsolve satisfy;"
  match LeanFzn.Compiler.compileModelFull routeMaxGen3Conflict with
  | .error _ => st ← st.check "prop: n-ary array_int_maximum conflict" false
  | .ok cp =>
      let st1 := propagateLoop 100 (LeanFzn.Integration.lcgProps cp)
        (initialStateWithRoots (LeanFzn.Integration.lcgProblem cp))
      st ← st.check "prop: n-ary array_int_maximum reports the r > max conflict"
        st1.conflict.isSome

  if st.failed == 0 then
    IO.println s!"passed {st.passed} solver tests"
    return 0
  else
    IO.eprintln s!"{st.failed} solver tests FAILED ({st.passed} passed)"
    return 1
