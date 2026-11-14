/-
Purpose: Regression tests for S2a set emission (PLAN.md task S2): sets are
printed as ascending, duplicate-free `{...}` (empty `{}`), including inside
`array1d(...)`, and an array value is never silently rendered as scalar text.
Dependencies: Emit.Basic/Emit.Model, parser and checker; no Legacy imports.
DAG: certified emitter -> this regression executable.
-/
import LeanFzn.Integration.Emit
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Cli.Main

open LeanFzn LeanFzn.Semantics LeanFzn.Integration

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

def setText (s : IntSetValue) : String := emitScalar (.setOfInt s)

def storeWith (name : String) (v : Value) : Store :=
  fun x => if x.name = name then some v else none

def setModel : Model :=
  match Parser.parseModel
    "var set of 1..3: S :: output_var;
     constraint set_in(2, S);
     solve satisfy;" with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

def setStore (s : IntSetValue) : Store := storeWith "S" (.setOfInt s)

def setArrayModel : Model :=
  match Parser.parseModel
    "var set of 0..11: s0;
     var set of 0..11: s1;
     var set of 0..11: s2;
     array [1..3] of var set of 0..11: SS :: output_array([1..3]) = [s0, s1, s2];
     solve satisfy;" with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

def setArrayStore : Store := fun x =>
  match x.name with
  | "s0" => some (.setOfInt (.enumeration [0, 11]))
  | "s1" => some (.setOfInt (.enumeration [0, 10]))
  | "s2" => some (.setOfInt (.enumeration []))
  | "SS" => some (.array [.setOfInt (.enumeration [0, 11]),
                         .setOfInt (.enumeration [0, 10]),
                         .setOfInt (.enumeration [])])
  | _ => none

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← st.check "canonical enumeration sorts and deduplicates"
    (setText (.enumeration [3, 1, 3, -2]) == "{-2, 1, 3}")
  st ← st.check "interval prints ascending members"
    (setText (.interval 1 3) == "{1, 2, 3}")
  st ← st.check "reversed interval prints {}"
    (setText (.interval 3 1) == "{}")
  st ← st.check "empty enumeration prints {}"
    (setText (.enumeration []) == "{}")
  st ← st.check "array of sets prints set elements"
    (emitDeclEntry
      (.array ⟨⟨2⟩, .setOfIntRange 1 3⟩ (Ident.mk "SS") [] [])
      (.array [.setOfInt (.enumeration [1]),
               .setOfInt (.interval 2 3)]) ==
     "SS = array1d ( 1 .. 2 , [ { 1 } , { 2 , 3 } ] ) ; ")
  st ← st.check "solution line is readable FlatZinc"
    (emitCertifiedSolution setModel (setStore (.enumeration [3, 1])) ==
     "S = { 1 , 3 } ; \n----------")
  let arrayText := emitCertifiedSolution setArrayModel setArrayStore
  st ← st.check "gt-sort-shaped emitted array preserves set and array commas"
    ((arrayText.splitOn "\n").contains
      "SS = array1d ( 1 .. 3 , [ { 0 , 11 } , { 0 , 10 } , { } ] ) ; ")
  st ← st.check "checker accepts emitted arrays with non-final multi-element sets"
    (match LeanFzn.Checker.checkModelSolution setArrayModel arrayText with
     | .accepted => true
     | _ => false)
  let emptyArrayText := emitDeclEntry
    (.array ⟨⟨-2⟩, .setOfIntRange 0 11⟩ (Ident.mk "SS") [] []) (.array [])
  st ← st.check "empty array output normalizes a negative declared upper bound"
    (emptyArrayText == "SS = array1d ( 1 .. 0 , [ ] ) ; ")
  st ← st.check "checker parser reads normalized empty array output"
    (match LeanFzn.Checker.Solution.parseSolution emptyArrayText with
     | .ok [⟨"SS", .array []⟩] => true
     | _ => false)
  -- The independent checker reads the emitted set text.
  let dir : System.FilePath := "/tmp/leanfzn_setemit_test"
  IO.FS.createDirAll dir
  let modelPath := (dir / "set.fzn").toString
  let solPath := (dir / "set.sol").toString
  IO.FS.writeFile modelPath
    "var set of 1..3: S :: output_var;
     constraint set_in(2, S);
     solve satisfy;"
  IO.FS.writeFile solPath
    (emitCertifiedSolution setModel (setStore (.enumeration [1, 2])))
  let (c1, _) ← runCli ["check", modelPath, solPath]
  st ← st.check "leanfzn check accepts emitted membership witness" (c1 == 0)
  IO.FS.writeFile solPath
    (emitCertifiedSolution setModel (setStore (.enumeration [1, 3])))
  let (c2, _) ← runCli ["check", modelPath, solPath]
  st ← st.check "leanfzn check rejects emitted non-membership" (c2 == 1)
  -- Exercise the actual solve -> text file -> check path, rather than only
  -- rendering a hand-built store. The first array element must be {1, 2}.
  let arrayModelPath := (dir / "array_set.fzn").toString
  let arraySolPath := (dir / "array_set.sol").toString
  IO.FS.writeFile arrayModelPath
    "var set of 1..2: a;
     var set of 1..2: b;
     array [1..2] of var set of int: ss :: output_array([1..2]) = [a, b];
     constraint set_in(1, a);
     constraint set_in(2, a);
     constraint set_in(1, b);
     constraint set_card(b, 1);
     solve satisfy;"
  let (solveCode, solvedText) ← runCli ["solve", arrayModelPath]
  st ← st.check "solver emits non-final multi-element set in an array"
    (solveCode == 0 && (solvedText.splitOn "\n").contains
      "ss = array1d ( 1 .. 2 , [ { 1 , 2 } , { 1 } ] ) ; ")
  IO.FS.writeFile arraySolPath solvedText
  let (checkCode, _) ← runCli ["check", arrayModelPath, arraySolPath]
  st ← st.check "check accepts solve's actual multi-element-set array output"
    (checkCode == 0)
  if st.failed == 0 then
    IO.println s!"set emission: {st.passed}/{st.passed + st.failed} checks passed"
    return 0
  else
    IO.eprintln s!"set emission: {st.failed} failed"
    return 1
