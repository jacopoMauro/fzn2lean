import solver.Direct.Correctness
import solver.Direct.Cli
import solver.LCG.Certified

/-!
# Solver test executable (the certified path)

Tests the certified solver stack end to end:

* `allAssigns` on small slot lists (the declarative specification
  shared by the exhaustive reference search and the LCG layer);
* `search` finds and misses assignments (the executable shared
  search);
* the DIRECT certified-fragment compiler (`compileModel`) on SAT,
  UNSAT, and unsupported models, including theorem-level nonvacuity
  of `solve_sat_correct` / `solve_unsat_correct` (the direct
  exhaustive reference solver, retained as internal cross-check);
* the CERTIFIED LCG command path (`solveCertified`) on the singleton
  fragment: SAT stores, emitted text accepted by the verified
  checker, UNSAT verdicts, fragment refusals, and theorem-level
  nonvacuity of `solveCertified_sat_correct` /
  `solveCertified_unsat_correct`.

The legacy checker-mediated solver tests (propagation, MRV,
restarts, NoGood learning, enumeration, optimization) were retired
with the legacy solver stack (PLAN.md §1); Git history keeps them.
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
  match LeanFzn.Solver.Direct.compileModel d1 with
  | .error e => st ← st.check "direct: int_plus model compiles" (false)
  | .ok problem =>
      st ← st.check "direct: int_plus model compiles" (true)
      st ← st.check "direct: problem has two slots"
        (problem.domains.length == 2)
      st ← st.check "direct: problem has one constraint"
        (problem.constraints.length == 1)
      match LeanFzn.Solver.Direct.solveCompiled problem with
      | some a =>
          st ← st.check "direct: int_plus finds a summing pair" (a.length == 2)
          match a[0]!, a[1]! with
          | .int p, .int q =>
              st ← st.check "direct: found pair sums to 5" (p + q == 5)
          | _, _ => st ← st.check "direct: found pair sums to 5" (false)
      | none => st ← st.check "direct: int_plus finds a summing pair" (false)

  -- SAT verification standalone re-check
  match LeanFzn.Solver.Direct.compileModel d1 with
  | .ok problem =>
      match LeanFzn.Solver.Direct.solveCompiled problem with
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
  match LeanFzn.Solver.Direct.compileModel d2 with
  | .error _ => st ← st.check "direct: impossible sum compiles" (false)
  | .ok problem =>
      st ← st.check "direct: impossible sum compiles" (true)
      st ← st.check "direct: impossible sum yields no assignment"
        (LeanFzn.Solver.Direct.solveCompiled problem == none)

  -- UNSAT: contradictory bounds (int_le and int_gt on one slot)
  let d3 := parseOrPanic
    "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.compileModel d3 with
  | .error _ => st ← st.check "direct: contradictory bounds compiles" (false)
  | .ok problem =>
      st ← st.check "direct: contradictory bounds compiles" (true)
      st ← st.check "direct: contradictory bounds yields no assignment"
        (LeanFzn.Solver.Direct.solveCompiled problem == none)

  -- unsupported: unbounded var int is rejected with a reason
  let d4 := parseOrPanic
    "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
  let ok4 := match LeanFzn.Solver.Direct.compileModel d4 with
    | .error e => e.contains "unbounded" || e.contains "outside"
    | .ok _ => false
  st ← st.check "direct: unbounded var rejected" ok4

  -- unsupported: predicate items are outside the certified fragment
  let d5 := parseOrPanic
    "predicate p(int: a);\nvar 1..3: x;\nsolve satisfy;"
  let ok5 := match LeanFzn.Solver.Direct.compileModel d5 with
    | .error e => e.contains "predicate"
    | .ok _ => false
  st ← st.check "direct: predicate items rejected" ok5

  -- unsupported: globals not in the extractable set
  let d6 := parseOrPanic
    "var 1..3: x;\nconstraint fzn_all_different_int([x]);\nsolve satisfy;"
  let ok6 := match LeanFzn.Solver.Direct.compileModel d6 with
    | .error e => e.contains "unsupported"
    | .ok _ => false
  st ← st.check "direct: fzn_ globals rejected" ok6

  -- T1 CAP REMOVAL: a 10,001-value finite domain must COMPILE (the
  -- old per-variable cap was 10,000). Early-witness SAT: the
  -- constraint pins x to a single value, so the search does not
  -- enumerate the huge domain.
  let d7 := parseOrPanic
    "var 0..10000: x;\nconstraint int_eq(x, 7);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.compileModel d7 with
  | .error e =>
      st ← st.check "direct: 10001-value domain compiles (cap removed)" (false)
      IO.eprintln s!"unexpected rejection: {e}"
  | .ok problem =>
      st ← st.check "direct: 10001-value domain compiles (cap removed)" (true)
      st ← st.check "direct: 10001-value domain has 10001 values"
        (problem.domains.length == 1
          && problem.domains[0]!.length == 10001)
      match LeanFzn.Solver.Direct.solveCompiled problem with
      | some a =>
          st ← st.check "direct: 10001-value domain early-witness SAT"
            (a.length == 1 && a[0]! == Value.int 7)
      | none =>
          st ← st.check "direct: 10001-value domain early-witness SAT" (false)

  -- T1 CAP REMOVAL: an enumerated domain above the old cap must
  -- COMPILE (the old per-variable cap was 10,000 on intSet too).
  let d8 := parseOrPanic
    "var {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}: x;\n\
     constraint int_eq(x, 3);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.compileModel d8 with
  | .error _ =>
      st ← st.check "direct: enumerated domain compiles (cap removed)" (false)
  | .ok problem =>
      st ← st.check "direct: enumerated domain compiles (cap removed)" (true)
      match LeanFzn.Solver.Direct.solveCompiled problem with
      | some a =>
          st ← st.check "direct: enumerated domain early-witness SAT"
            (a.length == 1 && a[0]! == Value.int 3)
      | none =>
          st ← st.check "direct: enumerated domain early-witness SAT" (false)

  -- T1 CAP REMOVAL: a domain product above 1,000,000 must COMPILE
  -- (the old leaves cap was 1,000,000). Early-witness SAT: the
  -- constraint pins the first variable, so the search descends one
  -- branch only. 1001 x 1001 = 1,002,001 > 1,000,000.
  let d9 := parseOrPanic
    "var 0..1000: x;\nvar 0..1000: y;\nconstraint int_eq(x, 5);\n\
     constraint int_eq(y, 6);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.compileModel d9 with
  | .error e =>
      st ← st.check "direct: >1M product compiles (cap removed)" (false)
      IO.eprintln s!"unexpected rejection: {e}"
  | .ok problem =>
      st ← st.check "direct: >1M product compiles (cap removed)" (true)
      st ← st.check "direct: >1M product has 1002001 leaves"
        (problem.domains.length == 2
          && problem.domains[0]!.length * problem.domains[1]!.length
            == 1002001)
      match LeanFzn.Solver.Direct.solveCompiled problem with
      | some a =>
          st ← st.check "direct: >1M product early-witness SAT"
            (a.length == 2 && a[0]! == Value.int 5 && a[1]! == Value.int 6)
      | none =>
          st ← st.check "direct: >1M product early-witness SAT" (false)

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
    (LeanFzn.Check.wellFormedFastB_iff dsat).mp (by native_decide)
  match hsolve : LeanFzn.Solver.Direct.solve dsat with
  | .sat store =>
      -- run the certified theorem on the actual verdict
      have _hsat : Satisfies fullSig fullInterp dsat store :=
        LeanFzn.Solver.Direct.solve_sat_correct
          (model := dsat) (store := store) wsat hsolve
      st ← st.check "direct theorem: solve_sat_correct applies" (true)
      -- the satisfying store's constraints hold (executable twin)
      st ← st.check "direct theorem: sat store satisfies constraints"
        (dsat.constraints.all (fun c =>
          LeanFzn.Globals.fullInterpB c.name
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
    (LeanFzn.Check.wellFormedFastB_iff dunsat).mp (by native_decide)
  match hunsolve : LeanFzn.Solver.Direct.solve dunsat with
  | .unsat =>
      have _hunsat : ¬ ∃ store, Satisfies fullSig fullInterp dunsat store ∧
          LeanFzn.Solver.Direct.ParamHonest dunsat store :=
        LeanFzn.Solver.Direct.solve_unsat_correct
          (model := dunsat) wunsat hunsolve
      st ← st.check "direct theorem: solve_unsat_correct applies" (true)
  | _ => st ← st.check "direct theorem: solve_unsat_correct applies" (false)

  -- ## Phase 3: the CERTIFIED LCG command path (nonvacuous tests)

  -- the executable command: SAT on the singleton fragment
  let csat := parseOrPanic
    "var {3}: x;\nvar {2}: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.solveCertified csat with
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
          (LeanFzn.Solver.Direct.emitCertifiedSolution csat store)
          == .accepted)
  | _ => st ← st.check "certified: singleton SAT returns a store" (false)

  -- the executable command: UNSAT on the singleton fragment
  let cunsat := parseOrPanic
    "var {2}: x;\nvar {2}: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
  st ← st.check "certified: singleton UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified cunsat with
     | .unsat => true
     | _ => false)

  -- multi-value domains: ADMITTED by the widened gate; the engine
  -- decides + backtracks (plusSlot propagator coverage)
  let cfrag := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\nconstraint int_plus(x, y, z);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.solveCertified cfrag with
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
          (LeanFzn.Solver.Direct.emitCertifiedSolution cfrag store)
          == .accepted)
  | _ => st ← st.check "certified: multi-value domain solves by decisions" (false)

  -- THEOREM-LEVEL nonvacuity on the widened gate: the SAT theorem
  -- applies to a multi-value model (decisions + backtracking)
  have wcfrag : WellFormed fullSig cfrag :=
    (LeanFzn.Check.wellFormedFastB_iff cfrag).mp (by native_decide)
  match hcres : LeanFzn.Solver.Direct.solveCertified cfrag with
  | .sat cstore =>
      have _hcert : Satisfies fullSig fullInterp cfrag cstore :=
        LeanFzn.Solver.Direct.solveCertified_sat_correct
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
    (match LeanFzn.Solver.Direct.solveCertified cmunsat2 with
     | .unsat => true
     | _ => false)

  -- multi-value UNSAT over int_le/int_lt (le/lt slots): the wide
  -- door's core shape
  let cmunsat3 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nconstraint int_le(x, y);\nconstraint int_lt(y, x);\nsolve satisfy;"
  st ← st.check "certified: multi-value UNSAT (le/lt)"
    (match LeanFzn.Solver.Direct.solveCertified cmunsat3 with
     | .unsat => true
     | _ => false)

  -- End-to-end frontier regressions: a SAT sibling and the K4 UNSAT
  -- model must both finish, with checker/source-theorem applications.
  let cph3 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\nconstraint int_ne(x, y);\nconstraint int_ne(x, z);\nconstraint int_ne(y, z);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.solveCertified cph3 with
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
          (LeanFzn.Solver.Direct.emitCertifiedSolution cph3 store)
          == .accepted)
  | _ => st ← st.check "certified: int_ne pigeonhole (3 slots/3 vals) solves SAT" (false)

  -- Four slots over three values are UNSAT. The pending frontier must
  -- remember exhausted siblings instead of restarting the x=2/1/0 cycle.
  let cph4 := parseOrPanic
    "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\nvar 0..2: w;\nconstraint int_ne(x, y);\nconstraint int_ne(x, z);\nconstraint int_ne(y, z);\nconstraint int_ne(x, w);\nconstraint int_ne(y, w);\nconstraint int_ne(z, w);\nsolve satisfy;"
  st ← st.check "certified: int_ne pigeonhole (4 slots/3 vals) UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified cph4 with
     | .unsat => true
     | _ => false)
  -- THEOREM-LEVEL nonvacuity: the wide-door unsat theorem applies to
  -- the fallback-nogood-refuted pigeonhole
  have wcph4 : WellFormed fullSig cph4 :=
    (LeanFzn.Check.wellFormedFastB_iff cph4).mp (by native_decide)
  match hph4 : LeanFzn.Solver.Direct.solveCertified cph4 with
  | .unsat =>
      have _hph : ¬ ∃ store, Satisfies fullSig fullInterp cph4
          store ∧ LeanFzn.Solver.Direct.ParamHonest cph4 store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
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
  match LeanFzn.Solver.Direct.solveCertified cbooland with
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
          (LeanFzn.Solver.Direct.emitCertifiedSolution cbooland store)
          == .accepted)
  | _ => st ← st.check "certified: bool_and+bool_not model solves SAT" (false)

  let cminmax := parseOrPanic
    "var 0..5: x;\nvar 0..5: y;\nvar 0..5: z;\nconstraint int_min(x, y, z);\nconstraint int_max(x, y, x);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.solveCertified cminmax with
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
  match LeanFzn.Solver.Direct.solveCertified cabs with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let r := (store (Ident.mk "r")).get!
      st ← st.check "certified: int_abs model solves SAT"
        (match x, r with
         | .int a, .int b => LeanFzn.Solver.absValue a == b && b < 3
         | _, _ => false)
  | _ => st ← st.check "certified: int_abs model solves SAT" (false)

  -- the bool UNSAT shape: a ∨ b = c, c = ¬a, a ∧ b = c — jointly
  -- unsatisfiable (c=¬a and a∧b=c force a=b=c and c=¬a)
  let cboolunsat := parseOrPanic
    "var bool: a;\nvar bool: b;\nvar bool: c;\nconstraint bool_or(a, b, c);\nconstraint bool_not(c, a);\nconstraint bool_and(a, b, c);\nsolve satisfy;"
  st ← st.check "certified: bool or+not+and mix is UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified cboolunsat with
     | .unsat => true
     | _ => false)

  -- THE LINLE/LINEQ/TIMES/ALLDIFF FAMILY REGRESSIONS (PLAN §5 item 3
  -- completion, 2026-10-02): the fixed propLinLe2's reasons are
  -- state-free valid, so multi-value linLe UNSAT is now CERTIFIED
  -- through the wide door (the linLeFree gate is GONE)
  let clinleu := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_lin_le([1,1],[x,y],2);\nconstraint int_lin_le([1,-1],[y,x],-2);\nsolve satisfy;"
  st ← st.check "certified: multi-value linLe UNSAT (wide door, no gate)"
    (match LeanFzn.Solver.Direct.solveCertified clinleu with
     | .unsat => true
     | _ => false)
  have wclinleu : WellFormed fullSig clinleu :=
    (LeanFzn.Check.wellFormedFastB_iff clinleu).mp (by native_decide)
  match hleu : LeanFzn.Solver.Direct.solveCertified clinleu with
  | .unsat =>
      have _hlu : ¬ ∃ store, Satisfies fullSig fullInterp clinleu
          store ∧ LeanFzn.Solver.Direct.ParamHonest clinleu store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
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
    (match LeanFzn.Solver.Direct.solveCertified clinles with
     | .sat _ => true
     | _ => false)

  -- linEq (int_plus with a literal result)
  let clineq := parseOrPanic
    "var 0..5: x;\nvar 0..5: y;\nconstraint int_plus(x, y, 7);\nsolve satisfy;"
  st ← st.check "certified: int_plus literal (linEq) SAT"
    (match LeanFzn.Solver.Direct.solveCertified clineq with
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
  match LeanFzn.Solver.Direct.solveCertified clinle2s with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      st ← st.check "certified: general-c linLe SAT (2x+y≤4, y≤0)"
        (match x, y with
        | .int a, .int b => 2 * a + b ≤ 4 ∧ b ≤ 0
        | _, _ => false)
      st ← st.check "certified: general-c linLe SAT text checker-accepted"
        (checkModelSolution clinle2s
          (LeanFzn.Solver.Direct.emitCertifiedSolution clinle2s store)
          == .accepted)
  | _ => st ← st.check "certified: general-c linLe SAT (2x+y≤4, y≤0)" (false)

  -- general-c linLe UNSAT: 2x + y ≤ 0 with x,y ≥ 1 — 2x + y ≥ 3 > 0
  let clinle2u := parseOrPanic
    "var 1..5: x;\nvar 1..5: y;\nconstraint int_lin_le([2,1],[x,y],0);\nsolve satisfy;"
  st ← st.check "certified: general-c linLe UNSAT (2x+y≤0, x,y≥1)"
    (match LeanFzn.Solver.Direct.solveCertified clinle2u with
     | .unsat => true
     | _ => false)
  have wclinle2u : WellFormed fullSig clinle2u :=
    (LeanFzn.Check.wellFormedFastB_iff clinle2u).mp (by native_decide)
  match hle2u : LeanFzn.Solver.Direct.solveCertified clinle2u with
  | .unsat =>
      have _hl2u : ¬ ∃ store, Satisfies fullSig fullInterp clinle2u
          store ∧ LeanFzn.Solver.Direct.ParamHonest clinle2u store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
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
    (match LeanFzn.Solver.Direct.solveCertified clineq2s with
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
    (match LeanFzn.Solver.Direct.solveCertified clineq2u with
     | .unsat => true
     | _ => false)



  -- timesSlot: x·y = z over slots, with a bounding le
  let ctimes := parseOrPanic
    "var 1..4: x;\nvar 1..4: y;\nvar 1..16: z;\nconstraint int_times(x, y, z);\nsolve satisfy;"
  st ← st.check "certified: int_times SAT"
    (match LeanFzn.Solver.Direct.solveCertified ctimes with
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
    (match LeanFzn.Solver.Direct.solveCertified ctimesu with
     | .unsat => true
     | _ => false)

  -- times sign deductions: z < 0 with y > 0 propagates x < 0
  -- (the operand-side sign arm x ≤ 0 narrows x to [-3,-1])
  let ctimessign := parseOrPanic
    "var -3..3: x;\nvar 1..4: y;\nvar -12..12: z;\nconstraint int_times(x, y, z);\nconstraint int_le(z, -1);\nsolve satisfy;"
  st ← st.check "certified: int_times sign UNSAT (z<0, y>0, x≥0)"
    (match LeanFzn.Solver.Direct.solveCertified ctimessign with
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
    (match LeanFzn.Solver.Direct.solveCertified ctimessignu with
     | .unsat => true
     | _ => false)
  -- the dual: z > 0 with y < 0 propagates x ≤ 0
  let ctimessignd := parseOrPanic
    "var -3..3: x;\nvar -4..-1: y;\nvar -12..12: z;\nconstraint int_times(x, y, z);\nconstraint int_le(1, z);\nsolve satisfy;"
  st ← st.check "certified: int_times sign SAT (z>0, y<0 → x<0)"
    (match LeanFzn.Solver.Direct.solveCertified ctimessignd with
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
    (match LeanFzn.Solver.Direct.solveCertified cad with
     | .unsat => true
     | _ => false)
  have wcad : WellFormed fullSig cad :=
    (LeanFzn.Check.wellFormedFastB_iff cad).mp (by native_decide)
  match had : LeanFzn.Solver.Direct.solveCertified cad with
  | .unsat =>
      have _had : ¬ ∃ store, Satisfies fullSig fullInterp cad
          store ∧ LeanFzn.Solver.Direct.ParamHonest cad store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
          (m := cad) wcad had
      st ← st.check "certified theorem: allDiff unsat_correct applies" true
      pure ()
  | _ =>
      st ← st.check "certified theorem: allDiff unsat_correct applies" false
      pure ()

  -- THEOREM-LEVEL nonvacuity: solveCertified_unsat_correct applies
  -- on the WIDE (multi-value, non-linLe) refutation
  have wcm3 : WellFormed fullSig cmunsat3 :=
    (LeanFzn.Check.wellFormedFastB_iff cmunsat3).mp (by native_decide)
  match hcm3 : LeanFzn.Solver.Direct.solveCertified cmunsat3 with
  | .unsat =>
      have _hcm : ¬ ∃ store, Satisfies fullSig fullInterp cmunsat3
          store ∧ LeanFzn.Solver.Direct.ParamHonest cmunsat3 store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
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
  match LeanFzn.Solver.Direct.solveCertified cbad with
  | .unsupported r =>
      st ← st.check "certified: unbounded var refused"
        (r.contains "unbounded")
  | _ => st ← st.check "certified: unbounded var refused" (false)

  -- THEOREM-LEVEL nonvacuity: solveCertified_sat_correct applies to
  -- a real command run (the composed chain, kernel-checked)
  have wcsat : WellFormed fullSig csat :=
    (LeanFzn.Check.wellFormedFastB_iff csat).mp (by native_decide)
  match hcres : LeanFzn.Solver.Direct.solveCertified csat with
  | .sat cstore =>
      have _hcert : Satisfies fullSig fullInterp csat cstore :=
        LeanFzn.Solver.Direct.solveCertified_sat_correct
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
    (LeanFzn.Check.wellFormedFastB_iff cunsat).mp (by native_decide)
  match hcures : LeanFzn.Solver.Direct.solveCertified cunsat with
  | .unsat =>
      have _hcu : ¬ ∃ store, Satisfies fullSig fullInterp cunsat store ∧
          LeanFzn.Solver.Direct.ParamHonest cunsat store :=
        LeanFzn.Solver.Direct.solveCertified_unsat_correct
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
  match LeanFzn.Solver.Direct.compileModel dpar with
  | .error _ => st ← st.check "direct: parameter fallback compiles" (false)
  | .ok problem =>
      st ← st.check "direct: parameter fallback compiles" (true)
      st ← st.check "direct: parameter fallback has one slot"
        (problem.domains.length == 1)
      match LeanFzn.Solver.Direct.solveCompiled problem with
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
  match LeanFzn.Solver.Direct.solveCertified ct1 with
  | .sat store =>
      let x := (store (Ident.mk "x")).get!
      let y := (store (Ident.mk "y")).get!
      st ← st.check "aux: int_times(x,y,6) solves SAT"
        (match x, y with
         | .int a, .int b => a * b == 6
         | _, _ => false)
      st ← st.check "aux: int_times emitted text checker-accepted"
        (checkModelSolution ct1
          (LeanFzn.Solver.Direct.emitCertifiedSolution ct1 store)
          == .accepted)
  | _ => st ← st.check "aux: int_times(x,y,6) solves SAT" (false)

  -- int_times(x, y, 6) + int_le(x, 1): UNSAT (x=1 forces y=6 > 3)
  let ct2 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_times(x, y, 6);\nconstraint int_le(x, 1);\nsolve satisfy;"
  st ← st.check "aux: int_times+int_le UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified ct2 with
     | .unsat => true
     | _ => false)

  -- int_ne(x, 3): SAT
  let ct3 := parseOrPanic
    "var 1..3: x;\nconstraint int_ne(x, 3);\nsolve satisfy;"
  st ← st.check "aux: int_ne(x,3) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct3 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a ≠ 3
         | _ => false
     | _ => false)

  -- int_ne(x, 3) on the singleton {3}: UNSAT
  let ct4 := parseOrPanic
    "var 3..3: x;\nconstraint int_ne(x, 3);\nsolve satisfy;"
  st ← st.check "aux: int_ne(x,3) singleton UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified ct4 with
     | .unsat => true
     | _ => false)

  -- int_ne(3, x): the symmetric form
  let ct5 := parseOrPanic
    "var 1..3: x;\nconstraint int_ne(3, x);\nsolve satisfy;"
  st ← st.check "aux: int_ne(3,x) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct5 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a ≠ 3
         | _ => false
     | _ => false)

  -- bool_and(x, y, true): SAT with checker-accepted output
  let ct6 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, true);\nsolve satisfy;"
  match LeanFzn.Solver.Direct.solveCertified ct6 with
  | .sat store =>
      st ← st.check "aux: bool_and(x,y,true) solves SAT"
        (match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => a && b
         | _, _ => false)
      st ← st.check "aux: bool_and(true) emitted text checker-accepted"
        (checkModelSolution ct6
          (LeanFzn.Solver.Direct.emitCertifiedSolution ct6 store)
          == .accepted)
  | _ => st ← st.check "aux: bool_and(x,y,true) solves SAT" (false)

  -- bool_and(x, y, false) + bool_or(x, y, true): SAT (exactly one true)
  let ct7 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, false);\nconstraint bool_or(x, y, true);\nsolve satisfy;"
  st ← st.check "aux: bool_and(false)+bool_or(true) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct7 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => !(a && b) && (a || b)
         | _, _ => false
     | _ => false)

  -- bool_and(x, y, false) + bool_and(x, y, true): UNSAT
  let ct8 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_and(x, y, false);\nconstraint bool_and(x, y, true);\nsolve satisfy;"
  st ← st.check "aux: bool_and(false)+bool_and(true) UNSAT"
    (match LeanFzn.Solver.Direct.solveCertified ct8 with
     | .unsat => true
     | _ => false)

  -- bool_or(x, y, false): SAT (both false)
  let ct9 := parseOrPanic
    "var bool: x;\nvar bool: y;\nconstraint bool_or(x, y, false);\nsolve satisfy;"
  st ← st.check "aux: bool_or(x,y,false) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct9 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .bool a, .bool b => !(a || b)
         | _, _ => false
     | _ => false)

  -- int_times(x, 3, y): the symmetric literal-middle form
  let ct10 := parseOrPanic
    "var 1..3: x;\nvar 1..9: y;\nconstraint int_times(x, 3, y);\nsolve satisfy;"
  st ← st.check "aux: int_times(x,3,y) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct10 with
     | .sat store =>
         match (store (Ident.mk "x")).get!, (store (Ident.mk "y")).get! with
         | .int a, .int b => a * 3 == b
         | _, _ => false
     | _ => false)

  -- int_times(3, x, y): the symmetric literal-first form
  let ct11 := parseOrPanic
    "var 1..3: x;\nvar 1..9: y;\nconstraint int_times(3, x, y);\nsolve satisfy;"
  st ← st.check "aux: int_times(3,x,y) SAT"
    (match LeanFzn.Solver.Direct.solveCertified ct11 with
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
    (match LeanFzn.Solver.Direct.solveCertified ct12 with
     | .sat store =>
         match (store (Ident.mk "x")).get! with
         | .int a => a * 2 == 6
         | _ => false
     | _ => false)

  -- the aux-slot structure: int_times(x,y,6) has ONE aux slot with
  -- the singleton domain {6}
  match LeanFzn.Solver.Direct.compileModel ct1 with
  | .ok p =>
      st ← st.check "aux: int_times uses one aux slot (3 slots total)"
        (p.domains.length == 3)
      st ← st.check "aux: the aux slot's domain is the singleton {6}"
        (p.domains[2]! == [.int 6])
  | .error _ =>
      st ← st.check "aux: int_times uses one aux slot (3 slots total)" (false)
      st ← st.check "aux: the aux slot's domain is the singleton {6}" (false)

  if st.failed == 0 then
    IO.println s!"passed {st.passed} solver tests"
    return 0
  else
    IO.eprintln s!"{st.failed} solver tests FAILED ({st.passed} passed)"
    return 1
