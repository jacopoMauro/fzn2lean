/-
Purpose: Regression tests for the Core-only large-neighbourhood primal phase
(PLAN.md P8).  The tests exercise the pure LNS run and the streaming entry on
a small maximization model, an unsatisfiable optimization model and a
zero-attempt fallback; every emitted witness is replayed through the
independent source-model checker.
Dependencies: public LNS entry, parser, checker and configuration parsing.
DAG: certified Core LNS -> this regression executable; no Legacy imports.

The test prints `LnsTest: OK` and exits 0 exactly when every check passes.
-/
import LeanFzn.Integration.Public.Lns
import LeanFzn.Integration.Config.Parse
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

namespace Tests.Integration.Public.LnsTest

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

/-- A model whose first full solution is objective 0 and whose optimum is 10.
The default Core search emits eleven incumbents; LNS starts from an already
improved incumbent and the complete loop still proves optimality. -/
def maxSrc : String :=
"var 0..10: x :: output_var;
var 0..10: obj :: output_var;
constraint int_eq(obj,x);
solve maximize obj;
"

/-- An optimization model with no solution; the LNS phase must fall back to
the complete loop and prove UNSAT rather than claim neighborhood failure. -/
def unsatSrc : String :=
"var 1..3: x :: output_var;
constraint int_eq(x,1);
constraint int_eq(x,2);
solve minimize x;
"

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

/-- The streaming entry emits exactly the pure run's witness stores and its
returned run is the pure LNS run on the maximization model. -/
def streamTest (st : St) : IO St := do
  let m := parseOrPanic maxSrc
  match compileModelOpt m with
  | .error e => st.check s!"stream: compiles ({e})" false
  | .ok (p, spec) =>
      let mut st := st
      let o : SearchConfig := { opt := .linear, primal := .lns, primalTime := 100 }
      let pureRun := (lnsSearch o p spec none).1
      let emitted ← IO.mkRef ([] : List Store)
      let emit : Store → IO Unit := fun s => emitted.modify (fun xs => xs ++ [s])
      match ← optimizeStreamCoreLns o m emit with
      | .error e => st.check s!"stream: entry succeeds ({e})" false
      | .ok (summary, _) =>
          st ← st.check "stream: returned run equals the pure LNS run"
            (summary.run.sols == pureRun.sols &&
              summary.run.complete == pureRun.complete &&
              summary.run.lastBound == pureRun.lastBound)
          let stores ← emitted.get
          st ← st.check "stream: emitted one store per witness"
            (stores.length == summary.run.sols.length)
          st ← st.check "stream: every emitted store passes the checker"
            (stores.all fun store =>
              match Checker.checkModelSolutionFast m
                  (emitCertifiedSolution m store) with
              | .accepted => true
              | _ => false)
          pure st

/-- LNS improves the first incumbent, the complete loop still reaches the
optimum, and every witness passes the independent checker. -/
def improvementTest (st : St) : IO St := do
  let m := parseOrPanic maxSrc
  match compileModelOpt m with
  | .error e => st.check s!"improve: compiles ({e})" false
  | .ok (p, spec) =>
      let mut st := st
      let o : SearchConfig := { opt := .linear, primal := .lns }
      let lnsRun := (lnsSearch o p spec none).1
      let baseRun := optLoopCoreStatsWith { opt := .linear } coreFuel p spec none none
      st ← st.check "improve: LNS run completes"
        (lnsRun.complete)
      st ← st.check "improve: LNS starts from an improved incumbent"
        (match lnsRun.sols.head? with
         | some (_, v) => v > 0
         | none => false)
      st ← st.check "improve: LNS reaches the objective optimum"
        (match lnsRun.sols.getLast? with
         | some (_, v) => v == 10
         | none => false)
      st ← st.check "improve: LNS emits fewer incumbents than the base loop"
        (lnsRun.sols.length < baseRun.1.sols.length)
      st ← st.check "improve: objectives strictly increase"
        (lnsRun.sols.Pairwise (fun s t => decide (s.2 < t.2)))
      st ← st.check "improve: every witness fits and is accepted"
        (lnsRun.sols.all fun s =>
          fitsB (propagationProblem p) s.1 && accepts p s.1)
      st ← st.check "improve: every emitted store passes the checker"
        (lnsRun.sols.all fun s =>
          match Checker.checkModelSolutionFast m
              (emitCertifiedSolution m (p.toStore s.1)) with
          | .accepted => true
          | _ => false)
      pure st

/-- A zero-attempt neighborhood keeps the first full-solve incumbent and the
ordinary complete loop still finishes. -/
def fallbackTest (st : St) : IO St := do
  let m := parseOrPanic maxSrc
  match compileModelOpt m with
  | .error e => st.check s!"fallback: compiles ({e})" false
  | .ok (p, spec) =>
      let mut st := st
      let o : SearchConfig := { opt := .linear, primal := .lns, primalTime := 0 }
      let start := lnsStart o p spec none
      st ← st.check "fallback: start keeps the first full-solve incumbent"
        (match start.1 with
         | some (_, v) => v == 0
         | none => false)
      let run := (lnsSearch o p spec none).1
      st ← st.check "fallback: unrestricted loop still completes"
        (run.complete && run.sols.length > 1)
      pure st

/-- An UNSAT optimization model is decided by the fallback complete loop, not
by a neighborhood verdict. -/
def unsatTest (st : St) : IO St := do
  let m := parseOrPanic unsatSrc
  match compileModelOpt m with
  | .error e => st.check s!"unsat: compiles ({e})" false
  | .ok (p, spec) =>
      let o : SearchConfig := { opt := .linear, primal := .lns, primalTime := 4 }
      let run := (lnsSearch o p spec none).1
      st.check "unsat: the complete loop returns complete UNSAT"
        (run.complete && run.sols.isEmpty)

/-- The option gate accepts `--primal=lns` only with the linear driver and the
`lns` preset selects that implemented configuration. -/
def configTest (st : St) : IO St := do
  let mut st := st
  st ← st.check "config: --primal=lns with --opt=linear is accepted"
    (match parseCoreSolveFlags
        ["--engine=core", "--opt=linear", "--primal=lns", "--primal-time=5",
          "model.fzn"] with
     | .ok (c, _) => c.primal == .lns && c.opt == .linear && c.primalTime == 5
     | .error _ => false)
  st ← st.check "config: --primal=lns with --opt=seeded is rejected"
    (match parseCoreSolveFlags
        ["--engine=core", "--opt=seeded", "--primal=lns", "model.fzn"] with
     | .error _ => true
     | .ok _ => false)
  st ← st.check "config: --primal=dive is still rejected by Core"
    (match parseCoreSolveFlags
        ["--engine=core", "--opt=linear", "--primal=dive", "model.fzn"] with
     | .error _ => true
     | .ok _ => false)
  st ← st.check "config: the lns preset uses the linear driver"
    (match Preset.toConfig .lns with
     | some c => c.primal == .lns && c.opt == .linear
     | none => false)
  pure st

def main : IO UInt32 := do
  let st0 : St := { passed := 0, failed := 0 }
  let st ← streamTest st0
  let st ← improvementTest st
  let st ← fallbackTest st
  let st ← unsatTest st
  let st ← configTest st
  IO.println s!"LnsTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "LnsTest: OK"
    return 0
  else
    return 1

end Tests.Integration.Public.LnsTest

def main : IO UInt32 := Tests.Integration.Public.LnsTest.main
