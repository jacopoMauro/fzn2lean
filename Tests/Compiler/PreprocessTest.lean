/-
Purpose: Regression tests for the certified duplicate-constraint preprocessing
(P7.1): the preprocessing removes only duplicate constraints, leaves the
search box, objective, source model and reconstruction store untouched, and
Core's verdicts and witnesses are unchanged.
Dependencies: Compiler.Preprocess, public Preprocess entries, parser and checker.
DAG: certified preprocessing -> this regression executable; no Legacy imports.

The test prints `PreprocessTest: OK` and exits 0 exactly when every check
passes.
-/
import LeanFzn.Integration.Public.Preprocess
import LeanFzn.Compiler.Objective
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine
open LeanFzn.Integration
open LeanFzn.Core

namespace Tests.Compiler.PreprocessTest

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

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

/-- A satisfaction model with three syntactically identical `int_le` rows and
two identical `int_eq` rows, so dedup keeps 2 of the 5 constraints. -/
def dupSrc : String :=
"var 1..3: x :: output_var;
var 1..3: y :: output_var;
constraint int_le(x,2);
constraint int_le(x,2);
constraint int_le(x,2);
constraint int_eq(x,y);
constraint int_eq(x,y);
solve satisfy;
"

/-- An optimization model whose objective value is preserved by dedup. -/
def optSrc : String :=
"var 0..4: x :: output_var;
var 0..8: obj :: output_var;
constraint int_le(x,3);
constraint int_le(x,3);
constraint int_eq(obj,x);
constraint int_eq(obj,x);
solve minimize obj;
"

/-- Dedup counts and the acceptance equivalence on every box assignment. -/
def equivalenceTest (st : St) : IO St := do
  let m := parseOrPanic dupSrc
  match compileModelFull m with
  | .error e => st.check s!"dup: compiles ({e})" false
  | .ok p =>
      let mut st := st
      st ← st.check "dup: keeps 2 of 5 constraints"
        (p.constraints.length == 5 &&
          p.preprocess.constraints.length == 2)
      st ← st.check "dup: box unchanged"
        (p.preprocess.domains == p.domains)
      st ← st.check "dup: acceptance agrees on every box assignment"
        ((allAssigns p.domains).all fun a =>
          accepts p.preprocess a == accepts p a)
      st ← st.check "dup: every accepted preprocessed assignment is accepted"
        ((allAssigns p.domains).all fun a =>
          !accepts p.preprocess a || accepts p a)
      pure st

/-- Core with `--presolve=dedup` returns the same SAT witness class as the
unpreprocessed entry, and the emitted store passes the independent checker. -/
def solveTest (st : St) : IO St := do
  let m := parseOrPanic dupSrc
  match compileModelFull m with
  | .error e => st.check s!"solve: compiles ({e})" false
  | .ok p =>
      let mut st := st
      let oNone : SearchConfig := { presolve := .none }
      let oDedup : SearchConfig := { presolve := .dedup }
      match coreSolveFullPre p oNone none coreFuel,
          coreSolveFullPre p oDedup none coreFuel with
      | (.sat a1, _), (.sat a2, _) =>
          st ← st.check "solve: both entries are SAT" true
          st ← st.check "solve: dedup witness fits"
            (fitsB (propagationProblem (presolveProblem oDedup p)) a2)
          st ← st.check "solve: dedup witness is accepted"
            (accepts (presolveProblem oDedup p) a2)
          st ← st.check "solve: dedup witness is accepted by the original"
            (accepts p a2)
          st ← st.check "solve: no-presolve witness is accepted"
            (accepts p a1)
          st ← st.check "solve: solved values agree on x and y"
            (a1[0]? == a2[0]? && a1[1]? == a2[1]?)
          pure st
      | _, _ => st.check "solve: both entries are SAT" false

/-- The objective specification and all solutions keep their meaning: the
preprocessed problem has the same objective slot and the same accepted
assignment set, and `compileModelOpt` still recovers value 3. -/
def objectiveTest (st : St) : IO St := do
  let m := parseOrPanic optSrc
  match compileModelOpt m with
  | .error e => st.check s!"objective: compiles ({e})" false
  | .ok (p, spec) =>
      let mut st := st
      st ← st.check "objective: slot and direction unchanged by dedup"
        (spec.slot < p.preprocess.domains.length &&
          p.preprocess.objective == p.objective)
      st ← st.check "objective: acceptance agrees on every box assignment"
        ((allAssigns p.domains).all fun a =>
          accepts p.preprocess a == accepts p a)
      let oDedup : SearchConfig := { presolve := .dedup }
      match coreSolveFullPre p oDedup none coreFuel with
      | (.sat a, _) =>
          st ← st.check "objective: dedup witness is accepted"
            (accepts p a)
          st ← st.check "objective: witness reads its objective slot"
            (match a[spec.slot]? with
             | some (.int _) => true
             | _ => false)
          st ← st.check "objective: emitted store satisfies the source model"
            (match Checker.checkModelSolutionFast m
                (LeanFzn.Integration.emitCertifiedSolution m (p.toStore a)) with
             | .accepted => true
             | _ => false)
          pure st
      | _ => st.check "objective: dedup entry is SAT" false

def main : IO UInt32 := do
  let st0 : St := { passed := 0, failed := 0 }
  let st ← equivalenceTest st0
  let st ← solveTest st
  let st ← objectiveTest st
  IO.println s!"PreprocessTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "PreprocessTest: OK"
    return 0
  else
    return 1

end Tests.Compiler.PreprocessTest

def main : IO UInt32 := Tests.Compiler.PreprocessTest.main
