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
     "SS = array1d(1..2, [{1}, {2, 3}]);")
  st ← st.check "solution line is readable FlatZinc"
    (emitCertifiedSolution setModel (setStore (.enumeration [3, 1])) ==
     "S = {1, 3};\n----------")
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
  if st.failed == 0 then
    IO.println s!"set emission: {st.passed}/{st.passed + st.failed} checks passed"
    return 0
  else
    IO.eprintln s!"set emission: {st.failed} failed"
    return 1
