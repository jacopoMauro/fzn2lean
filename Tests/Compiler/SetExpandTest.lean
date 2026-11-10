/-
Purpose: Regression tests for S3 verified set expansion (PLAN.md task S3):
a declared bounded set variable becomes one fresh Boolean per universe value,
the `set_in`/`set_in_reif` literal-element shapes are rewritten, the store
rebuilds an ascending enumeration, and the real CLI compiles and checks the
result.  Out-of-universe members are false, not errors.
Dependencies: Compiler.Normalize/SetExpand, parser, CLI; no Legacy imports.
DAG: certified set-expansion pass -> this regression executable.
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

def expand! (text : String) : SetExpansion :=
  match setExpandModel (parse! text) with
  | some se => se
  | none => { model := parse! "solve satisfy;", sets := [] }

def firstSet! (se : SetExpansion) : SetInfo :=
  match se.sets with
  | [i] => i
  | _ => { name := "", ty := .par .bool, bools := [] }

def constraintNames (se : SetExpansion) : List String :=
  se.model.constraints.map (fun c => c.name.name)

def isFalseRow (c : ConstraintItem) : Bool :=
  c.name.name = "int_lin_le" && c.args.length = 3 &&
    match c.args with
    | [.array [], .array [], .basic (.lit (.int k))] => k == -1
    | _ => false

def storeOf (pairs : List (String × Value)) : Store :=
  fun x => (pairs.find? fun p => p.1 = x.name).map Prod.snd

def runModel (dir : System.FilePath) (name text : String) :
    IO (System.FilePath × UInt32 × String) := do
  let path := dir / s!"{name}.fzn"
  IO.FS.writeFile path text
  let (code, out) ← runCli ["solve", path.toString]
  return (path, code, out)

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  let rangeModel :=
    "var set of 1..3: S :: output_var;\nconstraint set_in(2, S);\nsolve satisfy;"
  let reranged := expand! rangeModel
  st ← st.check "bounded range universe is ascending"
    ((firstSet! reranged).values == [1, 2, 3])
  st ← st.check "set declaration is replaced by one Boolean per value"
    (reranged.model.variables.length == 3)
  st ← st.check "set_in literal pins the matching Boolean"
    (constraintNames reranged == ["bool_not"])
  st ← st.check "out-of-universe set_in is the always-false row"
    (match (expand! "var set of 1..3: S;\nconstraint set_in(9, S);\nsolve satisfy;").model.constraints with
     | [c] => isFalseRow c
     | _ => false)
  st ← st.check "duplicate literal universe is deduplicated and sorted"
    ((firstSet! (expand! "var set of {3, 1, 3, 2}: S;\nconstraint set_in(3, S);\nsolve satisfy;")).values
       == [1, 2, 3])
  st ← st.check "set_in_reif variable result becomes bool_eq"
    (constraintNames (expand!
      "var set of 1..3: S;\nvar bool: b;\nconstraint set_in_reif(2, S, b);\nsolve satisfy;")
       == ["bool_eq"])
  st ← st.check "reified false out-of-universe member is dropped"
    (constraintNames (expand!
      "var set of 1..3: S;\nconstraint set_in_reif(9, S, false);\nsolve satisfy;")
       == [])
  st ← st.check "reified true out-of-universe member is the false row"
    (match (expand!
       "var set of 1..3: S;\nconstraint set_in_reif(9, S, true);\nsolve satisfy;").model.constraints with
     | [c] => isFalseRow c
     | _ => false)
  st ← st.check "setStore rebuilds the ascending true enumeration"
    (match firstSet! reranged with
     | i =>
       let s := storeOf [(i.bools[0]!.1, .bool true), (i.bools[1]!.1, .bool false),
                        (i.bools[2]!.1, .bool true)]
       setStore reranged s (Ident.mk "S") == some (.setOfInt (.enumeration [1, 3])))
  st ← st.check "setStore leaves other names unchanged"
    (setStore reranged (storeOf [("x", .int 7)]) (Ident.mk "x") == some (.int 7))
  st ← st.check "compileModelFull accepts the expanded model"
    (match compileModelFull (parse! rangeModel) with
     | .ok _ => true
     | .error _ => false)
  st ← st.check "compileModelFull rejects an unbounded set variable"
    (match compileModelFull (parse! "var set of int: S;\nsolve satisfy;") with
     | .ok _ => false
     | .error _ => true)

  let dir : System.FilePath := "/tmp/leanfzn_setexpand_test"
  IO.FS.createDirAll dir
  let (posPath, posCode, posOut) ← runModel dir "pos" rangeModel
  st ← st.check "CLI solves the positive membership model" (posCode == 0)
  let solPath := dir / "pos.sol"
  IO.FS.writeFile solPath posOut
  let (checkCode, _) ← runCli ["check", posPath.toString, solPath.toString]
  st ← st.check "checker accepts the emitted membership witness" (checkCode == 0)
  IO.FS.writeFile solPath "S = {3};\n----------\n"
  let (badCode, _) ← runCli ["check", posPath.toString, solPath.toString]
  st ← st.check "checker rejects a non-member witness" (badCode == 1)

  let (_, outCode, outText) ← runModel dir "out"
    "var set of 1..3: S :: output_var;\nconstraint set_in(9, S);\nsolve satisfy;"
  st ← st.check "out-of-universe membership is certified UNSAT"
    (outCode == 1 && (outText.splitOn "=====UNSATISFIABLE=====").length == 2)
  let (_, reifCode, _) ← runModel dir "reif"
    "var set of 1..3: S :: output_var;\nvar bool: b;\nconstraint set_in_reif(9, S, b);\nconstraint bool_not(b, false);\nsolve satisfy;"
  st ← st.check "out-of-universe reified member forces false" (reifCode == 1)
  let (_, bareCode, _) ← runModel dir "bare" "var set of int: S;\nsolve satisfy;"
  st ← st.check "unbounded set variable stays unsupported" (bareCode == 3)

  if st.failed == 0 then
    IO.println s!"set expansion: {st.passed}/{st.passed + st.failed} checks passed"
    return 0
  else
    IO.eprintln s!"set expansion: {st.failed} failed"
    return 1
