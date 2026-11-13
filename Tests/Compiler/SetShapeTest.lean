/-
Purpose: Regression tests for the S4–S6 set-shape pre-pass (PLAN.md tasks
S4, S5 and S6): `set_in`/`set_in_reif` over a declared set variable,
`set_card` with a variable or literal result, `set_union` and
`set_intersect` over declared/literal sets, and `array_var_set_element`
over literal or declared-set arrays are rewritten into scalar
auxiliaries, literal membership rows and per-value Boolean rows before
the S3 set expansion runs.  The pre-pass must be the identity on a model
without those shapes, and a false ground row must be certified UNSAT
rather than dropped.
Dependencies: Compiler.Normalize/SetShape, parser, CLI; no Legacy imports.
DAG: certified set-shape pre-pass -> this regression executable.
-/
import LeanFzn.Compiler.Normalize
import LeanFzn.Parser.Parser
import LeanFzn.Cli.Main

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler

structure St where
  passed : Nat
  failed : Nat

def St.check (st : St) (name : String) (ok : Bool) : IO St := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

def runCli (args : List String) : IO (UInt32 × String) := do
  let (out, code) ← IO.FS.withIsolatedStreams (LeanFzn.Cli.main args)
  return (code, out)

def parse! (text : String) : Model :=
  match Parser.parseModel text with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

def shape! (text : String) : ShapeExpansion :=
  match shapeExpandModel (parse! text) with
  | some sh => sh
  | none => { model := parse! "solve satisfy;", aux := [] }

def constraintNames (m : Model) : List String :=
  m.constraints.map (fun c => c.name.name)

def containsName (m : Model) (n : String) : Bool :=
  (constraintNames m).contains n

def literalMemberRow (c : ConstraintItem) : Bool :=
  c.name.name == "set_in_reif" &&
    match c.args with
    | [.basic (.lit (.int _)), _, _] => true
    | _ => false

def auxBools (sh : ShapeExpansion) : Nat :=
  (sh.aux.filter (fun a => match a.ty with
    | .par .bool => true
    | _ => false)).length

def compileOk (text : String) : Bool :=
  match compileModelFull (parse! text) with
  | .ok _ => true
  | .error _ => false

def runModel (dir : System.FilePath) (name text : String) :
    IO (System.FilePath × UInt32 × String) := do
  let path := dir / s!"{name}.fzn"
  IO.FS.writeFile path text
  let (code, out) ← runCli ["solve", path.toString]
  return (path, code, out)

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }

  -- The pre-pass is the identity on a model without set shapes.
  let scalar := "var 1..3: x :: output_var;\nconstraint int_eq(x, 2);\nsolve satisfy;"
  let sh0 := shape! scalar
  st ← st.check "no set shape leaves no auxiliaries" (sh0.aux.isEmpty)
  st ← st.check "no set shape leaves the rows unchanged"
    (constraintNames sh0.model == constraintNames (parse! scalar))

  -- A variable membership bit is a conjunction of equality bits.
  let member :=
    "var 1..3: x :: output_var;\nvar set of 1..3: S :: output_var;\n\
     var bool: b :: output_var;\nconstraint set_in_reif(x, S, b);\nsolve satisfy;"
  let shm := shape! member
  st ← st.check "variable member allocates one Boolean per universe value"
    (auxBools shm >= 3)
  st ← st.check "variable member leaves only literal set_in_reif rows"
    ((shm.model.constraints.filter (fun c => c.name.name == "set_in_reif")).all
      literalMemberRow &&
     (shm.model.constraints.filter (fun c => c.name.name == "set_in_reif")).length == 3)
  st ← st.check "variable member emits bool_clause link rows"
    (containsName shm.model "bool_clause")
  st ← st.check "compileModelFull accepts a variable member model" (compileOk member)

  -- Q3: a repeated membership shape reuses the canonical auxiliary for each
  -- kind, so two identical constraints allocate no extra Booleans.
  let member2 :=
    "var 1..3: x :: output_var;\nvar set of 1..3: S :: output_var;\n\
     var bool: b1 :: output_var;\nvar bool: b2 :: output_var;\n\
     constraint set_in_reif(x, S, b1);\nconstraint set_in_reif(x, S, b2);\n\
     solve satisfy;"
  let shm2 := shape! member2
  st ← st.check "repeated variable member shares auxiliaries"
    (auxBools shm2 == auxBools shm)
  st ← st.check "repeated variable member keeps both link rows"
    ((shm2.model.constraints.filter (fun c => c.name.name == "bool_clause")).length ==
     2 * (shm.model.constraints.filter (fun c => c.name.name == "bool_clause")).length)

  -- Cardinality: one membership bit and one bool2int alias per value.
  let card :=
    "var set of 1..4: S :: output_var;\nvar 0..4: k :: output_var;\n\
     constraint set_union({1,3}, {}, S);\nconstraint set_card(S, k);\n\
     constraint int_eq(k, 2);\nsolve satisfy;"
  let shc := shape! card
  st ← st.check "set_card is rewritten into an integer row"
    (!containsName shc.model "set_card" && containsName shc.model "int_lin_eq")
  st ← st.check "set_card allocates bool2int aliases"
    (containsName shc.model "bool2int")
  st ← st.check "compileModelFull accepts a union and cardinality model"
    (compileOk card)

  -- Union: one Boolean relation per value in the three universes.
  let union :=
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     var set of 1..3: C :: output_var;\nconstraint set_union(A, B, C);\n\
     solve satisfy;"
  let shu := shape! union
  st ← st.check "set_union is rewritten into Boolean relations"
    (!containsName shu.model "set_union" && containsName shu.model "bool_or")
  st ← st.check "compileModelFull accepts a variable union model" (compileOk union)

  -- S5: an array element over declared set variables becomes one Boolean
  -- element row per value of the target universe.
  let elemVar :=
    "var 1..2: i :: output_var;\nvar set of 1..3: S1 :: output_var;\n\
     var set of 1..3: S2 :: output_var;\nvar set of 1..3: T :: output_var;\n\
     constraint array_var_set_element(i, [S1, S2], T);\nsolve satisfy;"
  let she := shape! elemVar
  let erows := she.model.constraints.filter (fun c => c.name.name == "array_var_bool_element")
  st ← st.check "array element is rewritten into Boolean element rows"
    (!containsName she.model "array_var_set_element" && erows.length == 3)
  st ← st.check "array element rows carry one bit per array position"
    (erows.all (fun c => match c.args with
      | [_, .array bits, _] => bits.length == 2
      | _ => false))
  st ← st.check "compileModelFull accepts a variable array element model"
    (compileOk elemVar)

  -- S5: literal, empty and range element sets are pinned Booleans.
  let elemLit :=
    "var 1..3: i :: output_var;\nvar set of 1..3: T :: output_var;\n\
     constraint array_var_set_element(i, [{1,2}, {}, 2..3], T);\n\
     solve satisfy;"
  let shl := shape! elemLit
  st ← st.check "literal array element is rewritten into Boolean element rows"
    (!containsName shl.model "array_var_set_element" &&
     (shl.model.constraints.filter (fun c => c.name.name == "array_var_bool_element")).length == 3)
  st ← st.check "compileModelFull accepts a literal array element model"
    (compileOk elemLit)

  -- S5: a declared set whose universe is smaller than an element's value
  -- must reject the selection: the outside value is forced false.
  let smallT :=
    "var 1..2: i :: output_var;\nvar set of 1..2: T :: output_var;\n\
     constraint array_var_set_element(i, [{2,3}, {1}], T);\n\
     constraint int_eq(i, 1);\nsolve satisfy;"
  st ← st.check "compileModelFull accepts a smaller-target element model"
    (compileOk smallT)

  let dir : System.FilePath := "/tmp/leanfzn_setshape_test"
  IO.FS.createDirAll dir

  -- S5 CLI: a positive array element witness is accepted by the checker.
  let (elemPosPath, elemPosCode, elemPosOut) ← runModel dir "elem_pos" elemVar
  st ← st.check "CLI solves the variable array element model" (elemPosCode == 0)
  let elemSol := dir / "elem_pos.sol"
  IO.FS.writeFile elemSol elemPosOut
  let (elemChk, _) ← runCli ["check", elemPosPath.toString, elemSol.toString]
  st ← st.check "checker accepts the emitted array element witness" (elemChk == 0)
  IO.FS.writeFile elemSol
    "i = 2;\nS1 = {2, 3};\nS2 = {};\nT = {1};\n----------\n"
  let (elemBad, _) ← runCli ["check", elemPosPath.toString, elemSol.toString]
  st ← st.check "checker rejects a mutated array element witness" (elemBad == 1)

  -- S5 CLI: selecting a set with a value outside the target's declared
  -- universe is false, never dropped.
  let (_, smallCode, smallText) ← runModel dir "elem_small" smallT
  st ← st.check "element value outside the target universe is certified UNSAT"
    (smallCode == 1 && (smallText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S5 CLI: a pinned out-of-range index is false even when every row is
  -- otherwise satisfiable.
  let (_, oorCode, oorText) ← runModel dir "elem_oor"
    "var 1..3: i :: output_var;\nvar set of 1..2: S1 :: output_var;\n\
     var set of 1..2: S2 :: output_var;\nvar set of 1..2: T :: output_var;\n\
     constraint array_var_set_element(i, [S1, S2], T);\n\
     constraint int_eq(i, 3);\nsolve satisfy;"
  st ← st.check "pinned out-of-range element index is certified UNSAT"
    (oorCode == 1 && (oorText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S5 CLI: an empty element selected into a member-containing target is
  -- a false ground row.
  let (_, emptyCode, emptyText) ← runModel dir "elem_empty"
    "var 1..2: i :: output_var;\nvar set of 1..3: T :: output_var;\n\
     constraint array_var_set_element(i, [{}, {}], T);\n\
     constraint set_in(1, T);\n\
     constraint int_eq(i, 1);\nsolve satisfy;"
  st ← st.check "empty element against a required member is certified UNSAT"
    (emptyCode == 1 && (emptyText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S6: a set intersection becomes one Boolean conjunction per value.
  let inter :=
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     var set of 1..3: C :: output_var;\nconstraint set_intersect(A, B, C);\n\
     solve satisfy;"
  let shi := shape! inter
  let andRows := shi.model.constraints.filter (fun c => c.name.name == "bool_and")
  st ← st.check "set_intersect is rewritten into Boolean conjunctions"
    (!containsName shi.model "set_intersect" && andRows.length == 3)
  st ← st.check "compileModelFull accepts a set_intersect model" (compileOk inter)

  -- A positive variable-membership model: the checker accepts the witness.
  let (posPath, posCode, posOut) ← runModel dir "pos" member
  st ← st.check "CLI solves the variable-member model" (posCode == 0)
  let solPath := dir / "pos.sol"
  IO.FS.writeFile solPath posOut
  let (checkCode, _) ← runCli ["check", posPath.toString, solPath.toString]
  st ← st.check "checker accepts the emitted member witness" (checkCode == 0)
  IO.FS.writeFile solPath "x = 2;\nS = {1};\nb = true;\n----------\n"
  let (badCode, _) ← runCli ["check", posPath.toString, solPath.toString]
  st ← st.check "checker rejects a mutated member witness" (badCode == 1)

  -- Q3: the shared auxiliaries must carry one value satisfying both
  -- repeated membership constraints, and the witness must check.
  let (pos2Path, pos2Code, pos2Out) ← runModel dir "pos2" member2
  st ← st.check "CLI solves the repeated membership model" (pos2Code == 0)
  let sol2Path := dir / "pos2.sol"
  IO.FS.writeFile sol2Path pos2Out
  let (check2Code, _) ← runCli ["check", pos2Path.toString, sol2Path.toString]
  st ← st.check "checker accepts the repeated membership witness" (check2Code == 0)

  -- Union with a result universe too small: the outer value is forced false,
  -- contradicting the required membership.  This must be certified UNSAT.
  let (_, outCode, outText) ← runModel dir "out"
    "var set of 1..3: A :: output_var;\nvar set of 1..2: C :: output_var;\n\
     constraint set_union(A, {}, C);\nconstraint set_in_reif(3, A, true);\n\
     solve satisfy;"
  st ← st.check "union outside the result universe is certified UNSAT"
    (outCode == 1 && (outText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- A false ground cardinality row must stay UNSAT, not be dropped.
  let (_, cardCode, cardText) ← runModel dir "card"
    "var set of 1..4: S :: output_var;\n\
     constraint set_union({1,3}, {}, S);\nconstraint set_card(S, 1);\n\
     solve satisfy;"
  st ← st.check "false ground cardinality is certified UNSAT"
    (cardCode == 1 && (cardText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S6 CLI: the warehouse disjointness shape `A ∩ B = ∅` must be certified
  -- UNSAT when both sides require the same member.
  let (_, interDisjCode, interDisjText) ← runModel dir "inter_disj"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     constraint set_intersect(A, B, 1..0);\n\
     constraint set_in(1, A);\nconstraint set_in(1, B);\nsolve satisfy;"
  st ← st.check "disjoint intersection with a shared member is certified UNSAT"
    (interDisjCode == 1 &&
      (interDisjText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S6 CLI: a literal empty intersection with a required member is false.
  let (_, interEmptyCode, interEmptyText) ← runModel dir "inter_empty"
    "var set of 1..3: C :: output_var;\n\
     constraint set_intersect({}, {}, C);\nconstraint set_in(1, C);\n\
     solve satisfy;"
  st ← st.check "empty intersection with a required member is certified UNSAT"
    (interEmptyCode == 1 &&
      (interEmptyText.splitOn "=====UNSATISFIABLE=====").length == 2)

  -- S6 CLI: a positive intersection witness is accepted by the checker and a
  -- mutated witness (a member of both sides missing from the result) is
  -- rejected.
  let (interPosPath, interPosCode, interPosOut) ← runModel dir "inter_pos" inter
  st ← st.check "CLI solves the set_intersect model" (interPosCode == 0)
  let interSol := dir / "inter_pos.sol"
  IO.FS.writeFile interSol interPosOut
  let (interChk, _) ← runCli ["check", interPosPath.toString, interSol.toString]
  st ← st.check "checker accepts the emitted intersection witness" (interChk == 0)
  IO.FS.writeFile interSol
    "A = {1};\nB = {1};\nC = {};\n----------\n"
  let (interBad, _) ← runCli ["check", interPosPath.toString, interSol.toString]
  st ← st.check "checker rejects a mutated intersection witness" (interBad == 1)

  -- S6: a literal result universe limits the intersection to its members.
  let (_, interLitCode, _) ← runModel dir "inter_lit"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     constraint set_intersect(A, B, {1});\n\
     constraint set_in(1, A);\nconstraint set_in(1, B);\nsolve satisfy;"
  st ← st.check "literal intersection result is satisfiable" (interLitCode == 0)

  -- Unhandled shapes stay unsupported (exit 3), never silently accepted.
  let (_, diffCode, _) ← runModel dir "diff"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     var set of 1..3: C :: output_var;\nconstraint set_diff(A, B, C);\n\
     solve satisfy;"
  st ← st.check "unhandled set_diff stays unsupported" (diffCode == 3)

  -- S7: the remaining set predicates have no cohort model.  They stay
  -- honestly unsupported over variable sets and are never dropped.
  let (_, eqCode, _) ← runModel dir "set_eq_var"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     constraint set_eq(A, B);\nsolve satisfy;"
  st ← st.check "set_eq over variable sets stays unsupported" (eqCode == 3)
  let (_, subCode, _) ← runModel dir "set_subset_var"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     constraint set_subset(A, B);\nsolve satisfy;"
  st ← st.check "set_subset over variable sets stays unsupported" (subCode == 3)
  let (_, leCode, _) ← runModel dir "set_le_var"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     constraint set_le(A, B);\nsolve satisfy;"
  st ← st.check "lexicographic set_le stays unsupported" (leCode == 3)
  let (_, symCode, _) ← runModel dir "symdiff_var"
    "var set of 1..3: A :: output_var;\nvar set of 1..3: B :: output_var;\n\
     var set of 1..3: C :: output_var;\nconstraint set_symdiff(A, B, C);\n\
     solve satisfy;"
  st ← st.check "unhandled set_symdiff stays unsupported" (symCode == 3)

  -- S7 ground cases are decided by the certified literal fold: a true
  -- ground predicate is dropped and a false one is certified UNSAT.
  let (_, geqCode, _) ← runModel dir "set_eq_ground_true"
    "constraint set_eq({1,2}, {2,1});\nsolve satisfy;"
  st ← st.check "true ground set_eq is satisfiable" (geqCode == 0)
  let (_, gneCode, gneText) ← runModel dir "set_eq_ground_false"
    "constraint set_eq({1}, {2});\nsolve satisfy;"
  st ← st.check "false ground set_eq is certified UNSAT"
    (gneCode == 1 && (gneText.splitOn "=====UNSATISFIABLE=====").length == 2)

  if st.failed == 0 then
    IO.println s!"set shape: {st.passed}/{st.passed + st.failed} checks passed"
    return 0
  else
    IO.eprintln s!"set shape: {st.failed} failed"
    return 1
