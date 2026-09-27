import solver.Solver
import solver.Direct

/-!
# Solver test executable (PLAN.md 6.1, 6.2, 6.3, 6.5, 6.7)

Tests the solver stack end to end:

* `allAssigns` on small slot lists (the declarative specification);
* `search` finds and misses assignments (the executable search);
* SAT models — the solver returns `.sat text` and the *verified
  checker* accepts `text` (including a global constraint and an
  initializer-dependent model with an alias array, exercised the
  same way the Gecode suite exercises its reference strings);
* UNSAT models — the solver returns `.unsat`, cross-checked by
  brute force through the checker (every complete assignment of
  the domains is rejected);
* unsupported / out-of-fragment models — the solver refuses with
  `.unsupported` (unbounded `var int`, set variables, an
  unsupported global, oversized domains);
* integration (Round 3) — the propagating solver (`solveModelProp`)
  and the MRV solver (`solveModelHeur`) agree with the reference
  `solveModel` on the verdict for every model above (verdict-level
  agreement; sat texts may differ but must be checker-accepted), a
  pigeonhole-style UNSAT model whose pairwise `int_ne` constraints
  are all extracted (the pruning path), and a model with *no*
  extractable constraints (only `fzn_all_different_int`) proving
  the empty-propagator fallback path;
* final integration (Round 4) — the composed front door
  (`solveModelWith`, `solver/Config.lean`): the config-matrix
  battery runs every supported `SolveConfig` combination (reference,
  prop, MRV, prop+MRV, learning, budget) over the model battery and
  checks verdict-level agreement with `solveModel`, checker
  acceptance of every sat text, the prop+MRV pigeonhole refutation,
  budget-limited runs returning unknown-never-unsat, learning
  agreement on skewed-domain models, and the refusal of the
  documented-unsupported combinations.

The SAT cases re-check the emitted text with `checkModelSolution`
directly: together with `solveModel_sat_sound` (which proves the
re-check always succeeds) this is a redundant end-to-end validation
of the emission format, and it exercises `completedStore`'s filling
of initializer-derived variables on real solver output.
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

  -- ## End-to-end SAT models

  -- int_plus with small domains
  let m1 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  match solveModel m1 with
  | .sat text =>
      st ← st.check "sat: int_plus model accepted by checker"
        (checkModelSolution m1 text == .accepted)
      -- the assignment really satisfies x + y = 5: extract via brute force
      let ok := (allAssigns ([[1, 2, 3], [1, 2, 3]] : List (List Int))).any
        (fun l => match l with
          | [a, b] =>
              checkModelSolution m1
                (emitAssignment ["x", "y"] [Value.int a, Value.int b]) == .accepted
          | _ => false)
      st ← st.check "sat: brute force finds an accepted assignment" ok
  | _ => st ← st.check "sat: int_plus model solved" (false)
  -- confirm the returned text is among the brute-force-accepted ones
  match solveModel m1 with
  | .sat text =>
      let mut hits : List String := []
      for a in [1, 2, 3] do
        for b in [1, 2, 3] do
          let t := emitAssignment ["x", "y"] [Value.int a, Value.int b]
          if checkModelSolution m1 t == .accepted then hits := t :: hits
      st ← st.check "sat: returned text is a brute-force solution" (hits.contains text)
  | _ => pure ()

  -- global constraint (fzn_all_different_int) + a forcing constraint
  let m2 := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
     constraint fzn_all_different_int([x, y, z]);\n\
     constraint int_le(x, 1);\nsolve satisfy;"
  match solveModel m2 with
  | .sat text =>
      st ← st.check "sat: global alldiff model accepted by checker"
        (checkModelSolution m2 text == .accepted)
  | _ => st ← st.check "sat: global alldiff model solved" (false)

  -- initializer-dependent model: alias array completed from the slots
  let m3 := parseOrPanic
    "var 0..9: y1;\nvar 0..9: y2;\n\
     array [1..2] of var 0..9: xs = [y1, y2];\n\
     constraint int_plus(y1, y2, 8);\nsolve satisfy;"
  match solveModel m3 with
  | .sat text =>
      st ← st.check "sat: alias-array model accepted by checker"
        (checkModelSolution m3 text == .accepted)
      -- the checker's store completion fills xs from y1, y2: the
      -- emitted text assigns only y1, y2, yet the completed store
      -- has all three variables
      match parseSolution (stripSeparators text) with
      | .error _ =>
          st ← st.check "sat: emitted text parses" (false)
      | .ok es =>
          let store := completedStore m3 es
          st ← st.check "sat: completion fills xs"
            ((store (Ident.mk "xs")).isSome &&
              (store (Ident.mk "y1")).isSome &&
              (store (Ident.mk "y2")).isSome)
          -- an explicit xs entry consistent with the found y1, y2 is
          -- also accepted (redundant but valid, like Gecode's strings)
          let y1v := match store (Ident.mk "y1") with
            | some (.int i) => i
            | _ => 0
          let y2v := match store (Ident.mk "y2") with
            | some (.int i) => i
            | _ => 0
          let withXs := text.replace "----------"
            s!"xs = array1d(1..2, [{y1v}, {y2v}]);\n----------"
          st ← st.check "sat: explicit xs entry consistent"
            (checkModelSolution m3 withXs == .accepted)
  | _ => st ← st.check "sat: alias-array model solved" (false)

  -- Boolean model
  let m4 := parseOrPanic
    "var bool: a;\nvar bool: b;\nconstraint bool_and(a, b, true);\nsolve satisfy;"
  match solveModel m4 with
  | .sat text =>
      st ← st.check "sat: bool model accepted by checker"
        (checkModelSolution m4 text == .accepted)
      st ← st.check "sat: bool model assigns both true"
        (text.contains "a = true;" && text.contains "b = true;")
  | _ => st ← st.check "sat: bool model solved" (false)

  -- empty search space: all variables initialized
  let m5 := parseOrPanic "var 1..3: x = 2;\nsolve satisfy;"
  match solveModel m5 with
  | .sat text =>
      st ← st.check "sat: fully initialized model accepted by checker"
        (checkModelSolution m5 text == .accepted)
  | _ => st ← st.check "sat: fully initialized model solved" (false)

  -- negative values round-trip through emission and parsing
  let m6 := parseOrPanic
    "var -3..3: x;\nvar -3..3: y;\nconstraint int_plus(x, y, -1);\nsolve satisfy;"
  match solveModel m6 with
  | .sat text =>
      st ← st.check "sat: negative values accepted by checker"
        (checkModelSolution m6 text == .accepted)
  | _ => st ← st.check "sat: negative values model solved" (false)

  -- ## UNSAT models

  -- int_plus impossible on the domains
  let u1 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
  match solveModel u1 with
  | .unsat =>
      st ← st.check "unsat: int_plus impossible" true
      -- brute-force cross-check through the checker
      let ok := (allAssigns ([[1, 2], [1, 2]] : List (List Int))).all
        (fun l => match l with
          | [a, b] =>
              checkModelSolution u1
                (emitAssignment ["x", "y"] [Value.int a, Value.int b]) != .accepted
          | _ => true)
      st ← st.check "unsat: brute force agrees" ok
  | _ => st ← st.check "unsat: int_plus impossible" (false)

  -- contradictory constraints
  let u2 := parseOrPanic
    "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;"
  match solveModel u2 with
  | .unsat => st ← st.check "unsat: contradictory comparisons" true
  | _ => st ← st.check "unsat: contradictory comparisons" (false)

  -- empty domain (reversed range, R1): the slot exists but has no values
  let u3 := parseOrPanic "var 11..10: x;\nsolve satisfy;"
  match solveModel u3 with
  | .unsat => st ← st.check "unsat: empty domain slot" true
  | _ => st ← st.check "unsat: empty domain slot" (false)

  -- initialized variable outside its own domain: no search can fix it
  let u4 := parseOrPanic "var 1..3: x = 5;\nsolve satisfy;"
  match solveModel u4 with
  | .unsat => st ← st.check "unsat: initializer violates domain" true
  | _ => st ← st.check "unsat: initializer violates domain" (false)

  -- global constraint unsatisfiable
  let u5 := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\n\
     constraint fzn_all_different_int([x, y]);\n\
     constraint int_eq(x, y);\nsolve satisfy;"
  match solveModel u5 with
  | .unsat => st ← st.check "unsat: alldiff vs int_eq" true
  | _ => st ← st.check "unsat: alldiff vs int_eq" (false)

  -- ## Unsupported / out of fragment

  -- unbounded var int
  let s1 := parseOrPanic "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
  match solveModel s1 with
  | .unsupported r =>
      st ← st.check "unsupported: unbounded var int"
        (r.contains "finite")
  | _ => st ← st.check "unsupported: unbounded var int" (false)

  -- set variable
  let s2 := parseOrPanic "var set of 1..3: s;\nsolve satisfy;"
  match solveModel s2 with
  | .unsupported r => st ← st.check "unsupported: set variable" (r.contains "set")
  | _ => st ← st.check "unsupported: set variable" (false)
  -- unsupported global (fzn_span needs optional variables)
  let s3 := parseOrPanic
    "var 1..4: u;\nvar 1..4: v;\nconstraint fzn_span([u, v]);\nsolve satisfy;"
  match solveModel s3 with
  | .unsupported r =>
      st ← st.check "unsupported: fzn_span" (r.contains "fzn_span")
  | _ => st ← st.check "unsupported: fzn_span" (false)

  -- ill-formed model (duplicate declaration)
  let s4 := parseOrPanic "var 1..3: x;\nvar 1..3: x;\nsolve satisfy;"
  match solveModel s4 with
  | .unsupported _ => st ← st.check "unsupported: ill-formed model" true
  | _ => st ← st.check "unsupported: ill-formed model" (false)

  -- oversized domain (cap)
  let s5 := parseOrPanic "var 1..200000: x;\nsolve satisfy;"
  match solveModel s5 with
  | .unsupported _ => st ← st.check "unsupported: oversized domain" true
  | _ => st ← st.check "unsupported: oversized domain" (false)

  -- ## Search-order sanity: the first solution is the first in order

  let m7 := parseOrPanic "var 1..3: x;\nvar 1..3: y;\nsolve satisfy;"
  match solveModel m7 with
  | .sat text =>
      st ← st.check "order: first solution is lexicographically first"
        (text == "x = 1;\ny = 1;\n----------")
  | _ => st ← st.check "order: free model solved" (false)

  -- ## Integration (Round 3): the propagating and MRV solvers

  -- verdict-level agreement helper: same sat/unsat classification
  let agree (r1 r2 : SolveResult) : Bool :=
    match r1, r2 with
    | .sat _, .sat _ => true
    | .unsat, .unsat => true
    | .unsupported _, .unsupported _ => true
    | _, _ => false

  -- the three entry points agree on every earlier model (SAT and
  -- UNSAT and unsupported alike); sat texts may differ but the
  -- verdict must not
  let all3 : List String :=
    [ "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
    , "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;"
    , "var bool: a;\nvar bool: b;\nconstraint bool_and(a, b, true);\nsolve satisfy;"
    , "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;"
    , "var 11..10: x;\nsolve satisfy;"
    , "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;"
    , "var 1..3: x;\nvar 1..3: x;\nsolve satisfy;" ]
  let mut idx := 0
  for src in all3 do
    idx := idx + 1
    let m := parseOrPanic src
    st ← st.check s!"integration: prop agrees with reference {idx}"
      (agree (solveModelProp 50 m) (solveModel m))
    st ← st.check s!"integration: heur agrees with reference {idx}"
      (agree (solveModelHeur m) (solveModel m))

  -- sat texts of both new entry points are checker-accepted
  match solveModelProp 50 m1 with
  | .sat text =>
      st ← st.check "integration: prop sat text accepted"
        (checkModelSolution m1 text == .accepted)
  | _ => st ← st.check "integration: prop sat text accepted" (false)
  match solveModelHeur m1 with
  | .sat text =>
      st ← st.check "integration: heur sat text accepted"
        (checkModelSolution m1 text == .accepted)
  | _ => st ← st.check "integration: heur sat text accepted" (false)

  -- a model where extraction finds constraints (int_eq/int_ne/int_le
  -- chains) and pruning still returns the right answer: x = y, x ≠ 1,
  -- x ≤ y on 1..3 (solutions: (2,2),(3,3))
  let mi := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_eq(x, y);\n\
     constraint int_ne(x, 1);\nconstraint int_le(x, y);\nsolve satisfy;"
  -- extraction finds the two slot-slot constraints (int_eq, int_le);
  -- int_ne(x, 1) has a literal argument and is not extracted
  st ← st.check "integration: extraction finds int_eq/le (ne-with-literal skipped)"
    (match extractConstraints mi with
     | .ok cs => cs.length == 2
     | .error _ => false)
  match solveModel mi with
  | .sat _ =>
      match solveModelProp 50 mi with
      | .sat text =>
          st ← st.check "integration: pruned chain model accepted"
            (checkModelSolution mi text == .accepted)
          st ← st.check "integration: pruned chain solution is x = y ≥ 2"
            ((text.contains "x = 2;" && text.contains "y = 2;") ||
              (text.contains "x = 3;" && text.contains "y = 3;"))
      | _ => st ← st.check "integration: pruned chain model solved" (false)
      st ← st.check "integration: prop agrees with reference (chain)"
        (agree (solveModelProp 50 mi) (solveModel mi))
      st ← st.check "integration: heur agrees with reference (chain)"
        (agree (solveModelHeur mi) (solveModel mi))
  | _ => st ← st.check "integration: chain model solved by reference" (false)

  -- pigeonhole-style UNSAT, all constraints extracted: 4 variables 1..3
  -- with all pairwise int_ne (4 pigeons, 3 holes)
  let pigeons := (List.range 4).flatMap (fun i =>
    (List.range 4).filterMap (fun j =>
      if i < j then some (i, j) else none))
  let mut phSrc := ""
  for i in [0, 1, 2, 3] do
    phSrc := phSrc ++ s!"var 1..3: p{i};\n"
  for (i, j) in pigeons do
    phSrc := phSrc ++ s!"constraint int_ne(p{i}, p{j});\n"
  phSrc := phSrc ++ "solve satisfy;"
  let mph := parseOrPanic phSrc
  -- all six pairwise constraints are extracted
  st ← st.check "integration: pigeonhole constraints all extracted"
    (match extractConstraints mph with
     | .ok cs => cs.length == 6
     | .error _ => false)
  match solveModel mph with
  | .unsat =>
      st ← st.check "integration: pigeonhole unsat by reference" true
      match solveModelProp 50 mph with
      | .unsat =>
          st ← st.check "integration: pigeonhole unsat by pruning" true
          -- a very small fuel still suffices: the fixpoint contradicts early
          st ← st.check "integration: pigeonhole unsat with small fuel"
            (agree (solveModelProp 2 mph) .unsat &&
              agree (solveModelProp 0 mph) .unsat)
      | _ => st ← st.check "integration: pigeonhole unsat by pruning" (false)
      st ← st.check "integration: pigeonhole heur agrees"
        (agree (solveModelHeur mph) (solveModel mph))
  | _ => st ← st.check "integration: pigeonhole unsat by reference" (false)

  -- a model with NO extractable constraints (only fzn_all_different_int):
  -- the empty-propagator fallback path (prunedSearch with an empty
  -- constraint set is the reference search)
  let mn := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nvar 1..3: z;\n\
     constraint fzn_all_different_int([x, y, z]);\nsolve satisfy;"
  st ← st.check "integration: no constraints extracted (alldiff only)"
    (match extractConstraints mn with
     | .ok cs => cs.length == 0
     | .error _ => false)
  match solveModel mn with
  | .sat _ =>
      match solveModelProp 50 mn with
      | .sat text =>
          st ← st.check "integration: fallback alldiff accepted"
            (checkModelSolution mn text == .accepted)
      | _ => st ← st.check "integration: fallback alldiff solved" (false)
      st ← st.check "integration: prop agrees with reference (alldiff)"
        (agree (solveModelProp 50 mn) (solveModel mn))
  | _ => st ← st.check "integration: alldiff model solved by reference" (false)

  -- UNSAT via the fallback path too: alldiff + int_eq (the int_eq IS
  -- extracted, the alldiff is not — mixed extraction)
  let mu := parseOrPanic
    "var 1..2: x;\nvar 1..2: y;\n\
     constraint fzn_all_different_int([x, y]);\n\
     constraint int_eq(x, y);\nsolve satisfy;"
  st ← st.check "integration: mixed extraction (alldiff + int_eq)"
    (match extractConstraints mu with
     | .ok cs => cs.length == 1
     | .error _ => false)
  st ← st.check "integration: mixed model unsat by all three"
    (agree (solveModel mu) .unsat && agree (solveModelProp 50 mu) .unsat &&
      agree (solveModelHeur mu) .unsat)

  -- ## Final integration (Round 4): the composed front door
  --
  -- The config-matrix battery: every supported SolveConfig combination
  -- run on SAT/UNSAT/unsupported models, checked for verdict-level
  -- agreement with the reference `solveModel` (sat classification,
  -- checker-accepted texts, unsat classification), plus the
  -- documented-unsupported combos and the budget/learning paths.

  -- verdict helpers on the config level: a config run classifies sat
  -- exactly when the reference does; its sat text is accepted; and
  -- unsat agrees with the reference verdict
  let cfgSat (cfg : SolveConfig) (m : Model) : Bool :=
    match solveModelWith cfg m with
    | .sat text => checkModelSolution m text == .accepted
    | _ => false
  let cfgAgreeSat (cfg : SolveConfig) (m : Model) : Bool :=
    match solveModelWith cfg m, solveModel m with
    | .sat _, .sat _ => true
    | .unsat, .unsat => true
    | .unsupported _, .unsupported _ => true
    | .unknown _, .unsupported _ => true
    | _, _ => false
  let cfgAgreeUnsat (cfg : SolveConfig) (m : Model) : Bool :=
    match solveModelWith cfg m, solveModel m with
    | .unsat, .unsat => true
    | .sat _, .sat _ => true
    | _, _ => false

  -- the six supported configurations
  let cfgRef : SolveConfig := { useProp := false, useMrv := false, budget := none, nogoods := false }
  let cfgProp : SolveConfig := { useProp := true, useMrv := false, budget := none, nogoods := false }
  let cfgMrv : SolveConfig := { useProp := false, useMrv := true, budget := none, nogoods := false }
  let cfgPropMrv : SolveConfig := { useProp := true, useMrv := true, budget := none, nogoods := false }
  let cfgLearn : SolveConfig := { useProp := false, useMrv := false, budget := none, nogoods := true }
  let cfgBud : SolveConfig := { useProp := false, useMrv := false, budget := some 1000, nogoods := false }
  let cfgs : List (String × SolveConfig) :=
    [ ("ref", cfgRef), ("prop", cfgProp), ("mrv", cfgMrv)
    , ("propmrv", cfgPropMrv), ("learn", cfgLearn), ("budget", cfgBud) ]

  -- the battery of models: SAT (mixed constraint shapes), UNSAT,
  -- unsupported (out of fragment), pigeonhole UNSAT (all pairwise
  -- int_ne extracted — the strongest pruning case)
  let cfgModels : List (String × String) :=
    [ ("sat: int_plus", "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;")
    , ("sat: chain", "var 1..3: x;\nvar 1..3: y;\nconstraint int_eq(x, y);\nconstraint int_ne(x, 1);\nconstraint int_le(x, y);\nsolve satisfy;")
    , ("sat: bool", "var bool: a;\nvar bool: b;\nconstraint bool_and(a, b, true);\nsolve satisfy;")
    , ("unsat: int_plus", "var 1..2: x;\nvar 1..2: y;\nconstraint int_plus(x, y, 10);\nsolve satisfy;")
    , ("unsat: contrad", "var 1..3: x;\nconstraint int_le(x, 1);\nconstraint int_gt(x, 2);\nsolve satisfy;")
    , ("unsat: empty dom", "var 11..10: x;\nsolve satisfy;")
    , ("unsupported: unbounded", "var int: x;\nconstraint int_eq(x, 5);\nsolve satisfy;")
    , ("unsupported: dup", "var 1..3: x;\nvar 1..3: x;\nsolve satisfy;")
    , ("pigeonhole", phSrc) ]

  let mut cfgIdx := 0
  for (cfgName, cfg) in cfgs do
    for (mName, src) in cfgModels do
      cfgIdx := cfgIdx + 1
      let m := parseOrPanic src
      -- every config agrees with the reference verdict (modulo
      -- budget turns unsupported into unknown)
      st ← st.check s!"config {cfgName}: agrees with reference [{mName}]"
        (cfgAgreeSat cfg m)
      -- a sat verdict's text is checker-accepted (solveModelWith_sat_sound)
      st ← st.check s!"config {cfgName}: sat text accepted [{mName}]"
        (cfgSat cfg m || (match solveModelWith cfg m with | .sat _ => false | _ => true))

  -- UNSAT classification in isolation, on the UNSAT models
  for (cfgName, cfg) in cfgs do
    st ← st.check s!"config {cfgName}: unsat classification agrees"
      (cfgAgreeUnsat cfg u1 && cfgAgreeUnsat cfg u2 &&
        cfgAgreeUnsat cfg u5)

  -- the strongest pruning combination, prop+mrv, on the pigeonhole
  -- UNSAT model: all six pairwise int_ne constraints are extracted
  -- and pruning refutes the model
  st ← st.check "config propmrv: pigeonhole unsat"
    (match solveModelWith cfgPropMrv mph, solveModel mph with
     | .unsat, .unsat => true
     | _, _ => false)
  -- with small propagation fuel too (the fixpoint contradicts early;
  -- small fuel only weakens pruning, never soundness)
  st ← st.check "config propmrv: pigeonhole unsat with small fuel"
    (match solveModelPropMrv 2 mph, solveModelPropMrv 0 mph with
     | .unsat, .unsat => true
     | _, _ => false)

  -- MRV ordering is observable: the prop+mrv solver still emits in
  -- declaration order (the unpermuted slot order)
  match solveModelWith cfgPropMrv mi with
  | .sat text =>
      st ← st.check "config propmrv: chain model accepted"
        (checkModelSolution mi text == .accepted)
      st ← st.check "config propmrv: chain solution is x = y ≥ 2"
        ((text.contains "x = 2;" && text.contains "y = 2;") ||
          (text.contains "x = 3;" && text.contains "y = 3;"))
  | _ => st ← st.check "config propmrv: chain model solved" (false)
  st ← st.check "config propmrv: agrees with reference (chain)"
    (cfgAgreeSat cfgPropMrv mi)

  -- budget-limited runs: unknown, never unsat, on a hard-enough
  -- instance with a small budget (the schedule [0, 0, 0, 0] is all
  -- budgetOut; the model below has a solution so unsat would be a
  -- false refutation — the safety theorem instantiated)
  let mSmall := parseOrPanic
    "var 1..3: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 5);\nsolve satisfy;"
  let cfgTiny : SolveConfig :=
    { useProp := false, useMrv := false, budget := some 0, nogoods := false }
  st ← st.check "config budget: tiny budget gives unknown on sat model"
    (solveModelWith cfgTiny mSmall == .unknown "no verdict: the budget schedule was exhausted or the model was statically refused")
  -- same via the default schedule on a genuinely hard instance: the
  -- pigeonhole model is UNSAT and big enough that a small total
  -- budget cannot exhaust it
  st ← st.check "config budget: small budget on pigeonhole is not unsat"
    (solveModelWith { cfgBud with budget := some 3 } mph != .unsat)
  -- and a sufficient budget decides the same SAT model
  match solveModelWith cfgBud mSmall with
  | .sat text =>
      st ← st.check "config budget: sufficient budget finds accepted solution"
        (checkModelSolution mSmall text == .accepted)
  | _ => st ← st.check "config budget: sufficient budget finds accepted solution" (false)
  -- an out-of-fragment model under a budget: unknown (no claim)
  st ← st.check "config budget: out-of-fragment model is unknown"
    (solveModelWith cfgBud s1 == .unknown "no verdict: the budget schedule was exhausted or the model was statically refused")
  -- an UNSAT model with a sufficient budget: real unsat
  st ← st.check "config budget: unsat model with sufficient budget"
    (solveModelWith cfgBud u2 == .unsat)

  -- nogood-learning runs: agreement on skewed-domain models (one
  -- slot much larger than the other, where the learning loop's
  -- decision-trail NoGoods prune whole subtrees)
  let mSkew := parseOrPanic
    "var 1..9: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 12);\nsolve satisfy;"
  match solveModelWith cfgLearn mSkew with
  | .sat text =>
      st ← st.check "config learn: skewed-domain model accepted"
        (checkModelSolution mSkew text == .accepted)
  | _ => st ← st.check "config learn: skewed-domain model solved" (false)
  st ← st.check "config learn: agrees with reference (skewed)"
    (cfgAgreeSat cfgLearn mSkew)
  let uSkew := parseOrPanic
    "var 1..9: x;\nvar 1..3: y;\nconstraint int_plus(x, y, 50);\nsolve satisfy;"
  st ← st.check "config learn: skewed-domain unsat agrees"
    (match solveModelWith cfgLearn uSkew, solveModel uSkew with
     | .unsat, .unsat => true
     | _, _ => false)

  -- the documented-unsupported combinations refuse with a reason
  -- naming the configuration
  let badCfgs : List (String × SolveConfig) :=
    [ ("prop+budget", { cfgProp with budget := some 100 })
    , ("mrv+budget", { cfgMrv with budget := some 100 })
    , ("propmrv+budget", { cfgPropMrv with budget := some 100 })
    , ("learn+budget", { cfgLearn with budget := some 100 })
    , ("prop+learn", { cfgProp with nogoods := true })
    , ("mrv+learn", { cfgMrv with nogoods := true })
    , ("propmrv+learn", { cfgPropMrv with nogoods := true })
    , ("all four", { useProp := true, useMrv := true, budget := some 100, nogoods := true }) ]
  for (bName, bcfg) in badCfgs do
    match solveModelWith bcfg mSmall with
    | .unsupported r =>
        st ← st.check s!"config unsupported: {bName} refused with reason"
          (r.contains "not supported")
    | _ => st ← st.check s!"config unsupported: {bName} refused with reason" (false)



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

  if st.failed == 0 then
    IO.println s!"passed {st.passed} solver tests"
    return 0
  else
    IO.eprintln s!"{st.failed} solver tests FAILED ({st.passed} passed)"
    return 1
