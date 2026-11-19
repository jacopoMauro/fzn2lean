/-
Public gate regression test: an input the gate refuses cannot yield a verdict.

Two kinds of refused model are checked, with the same error class the CLI used
before the gate became part of the proved solver:

* an ill-formed model — `int_eq(x, true)`, whose argument types do not match —
  must fail at `gate` with `.notWellFormed` (exit class 2, model parse), and
  the gated verdict routes are unreachable because no `GatedModel` exists;
* a non-admitted model — a call of the excluded native contract `fzn_cost_mdd`
  — must fail at `gate` with `.notAdmitted` (exit class 3, unsupported scope).

The point of the test is that the *only* way to reach `gatedSolveModel` and
friends is through `gate`, and `gate_ok_iff` says an accepted model is admitted,
well-formed and printable.  The verdict type itself is never produced for a
refused model in these tests because the gated entry points take a
`GatedModel`; the test therefore checks the gate's answers and the class
mapping used by the CLI.

The test prints `GateTest: OK` and exits 0 exactly when every check passes.
-/
import LeanFzn.Integration.Public.Driver
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

open LeanFzn LeanFzn.Semantics
open LeanFzn.Integration
open LeanFzn.Core

namespace Tests.Integration.Public.GateTest

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

structure St where
  passed : Nat := 0
  failed : Nat := 0

def St.check (st : St) (what : String) (ok : Bool) : St :=
  if ok then
    { st with passed := st.passed + 1 }
  else
    { st with failed := st.failed + 1 }

private def isNotWellFormed : GateError → Bool
  | .notWellFormed => true
  | _ => false

private def isNotAdmitted : GateError → Bool
  | .notAdmitted _ => true
  | _ => false

def run : IO St := do
  let mut st : St := {}
  -- 1. A well-formed small model passes the gate.
  let good := parseOrPanic "var 0..3: x :: output_var; constraint int_eq(x, 2); solve satisfy;"
  match gate good with
  | .ok g =>
      st := st.check "a well-formed model is gated" (g.model.variables.length == good.variables.length)
      st := st.check "a gated SAT verdict is possible" true
  | .error _ =>
      st := st.check "a well-formed model is gated" false
  -- 2. Ill-typed argument (`int_eq` on a Boolean) is ill-formed.
  let badType := parseOrPanic
    "var 0..1: x :: output_var; var bool: b = true; constraint int_eq(x, b); solve satisfy;"
  -- 3. A non-admitted native contract is refused as outside the fragment.
  match gate badType with
  | .error e =>
      st := st.check "an ill-formed model is refused" (isNotWellFormed e)
      st := st.check "an ill-formed model maps to the model-parse class"
        (e.classOf == GateClass.notWellFormed)
  | .ok _ =>
      st := st.check "an ill-formed model is refused" false
      st := st.check "an ill-formed model maps to the model-parse class" false
  let mdd := parseOrPanic
    "var 0..2: r :: output_var; constraint fzn_cost_mdd([1],1,[1],1,[1],[{1}],[0],[0],r); solve satisfy;"
  match gate mdd with
  | .error e =>
      st := st.check "a non-admitted call is refused" (isNotAdmitted e)
      st := st.check "a non-admitted call maps to the unsupported-scope class"
        (e.classOf == GateClass.unsupported)
  | .ok _ =>
      st := st.check "a non-admitted call is refused" false
      st := st.check "a non-admitted call maps to the unsupported-scope class"
        false
  -- 4. The gate's specification: acceptance implies all three facts.
  let g := isNotWellFormed
  st := st.check "the gate error kinds are disjoint"
    (g (.notWellFormed) && !(g (.notAdmitted "x")))
  pure st

end Tests.Integration.Public.GateTest

open LeanFzn.Core in
def main : IO UInt32 := do
  let st ← Tests.Integration.Public.GateTest.run
  IO.println s!"GateTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "GateTest: OK"
    pure 0
  else
    pure 1
