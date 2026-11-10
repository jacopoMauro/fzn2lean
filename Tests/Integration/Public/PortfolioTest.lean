/-
Public Core integration test: the opt-in parallel portfolio (`--threads=N`).

The test checks the configuration gate (range, strategy conflicts, model
class), ordinary single-worker behavior, and that independent workers agree
on a proof: a completed portfolio may only report UNSAT or an optimum, while
a deliberately capped portfolio reports incompleteness with exit 4.

The test prints `PortfolioTest: OK` and exits 0 exactly when every check
passes.
-/
import LeanFzn.Integration.Public
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Engine
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Core

namespace Tests.Integration.Public.PortfolioTest

private def model (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! e

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

def rejects (args : List String) : Bool :=
  match LeanFzn.Core.parseSolveFlags args with
  | .error _ => true
  | .ok _ => false

/-- Configuration: the worker count parses, stays in 1..8, and the built-in
portfolio refuses flags that would silently replace its strategy mix. -/
def configTest (st : St) : IO St := do
  let mut st := st
  st ← st.check "config: --threads=4 parses"
    (match LeanFzn.Core.parseSolveFlags ["--threads=4"] with
     | .ok (o, _) => o.threads == 4
     | .error _ => false)
  st ← st.check "config: default is one worker"
    (match LeanFzn.Core.parseSolveFlags [] with
     | .ok (o, _) => o.threads == 1
     | .error _ => false)
  st ← st.check "config: zero workers is a usage error" (rejects ["--threads=0"])
  st ← st.check "config: nine workers is a usage error" (rejects ["--threads=9"])
  st ← st.check "config: --threads cannot pick a preset"
    (rejects ["--threads=4", "--strategy=annot"])
  st ← st.check "config: --threads cannot pick a variable order"
    (rejects ["--threads=4", "--var=wdeg"])
  st ← st.check "config: --threads cannot pick a value order"
    (rejects ["--threads=4", "--val=incumbent"])
  st ← st.check "config: --threads requires the linear complete driver"
    (rejects ["--threads=4", "--opt=seeded"])
  st ← st.check "config: --threads cannot use per-round primal slices"
    (rejects ["--threads=4", "--primal=lns"])
  pure st

/-- Small optimization models: the ordinary and portfolio drivers both finish
with a proof, and the UNSAT bound proves infeasibility. -/
def solveTest (st : St) : IO St := do
  let mut st := st
  let minModel := model "var 0..2: x :: output_var; solve minimize x;"
  let maxModel := model "var 0..2: x :: output_var; solve maximize x;"
  let unsatModel :=
    model "var 0..1: x; constraint int_eq(x,0); constraint int_eq(x,1); solve minimize x;"
  let satModel := model "var 0..2: x :: output_var; solve satisfy;"
  st ← st.check "single worker minimizes to a proof"
    ((← runModel { var := .act, val := .incumbent } minModel) == 0)
  st ← st.check "four workers minimize to a proof"
    ((← runModel { threads := 4 } minModel) == 0)
  st ← st.check "eight workers maximize to a proof"
    ((← runModel { threads := 8 } maxModel) == 0)
  st ← st.check "four workers prove the UNSAT bound" ((← runModel { threads := 4 } unsatModel) == 1)
  st ← st.check "four workers solve satisfaction"
    ((← runModel { threads := 4 } satModel) == 0)
  st ← st.check "eight workers solve satisfaction"
    ((← runModel { threads := 8 } satModel) == 0)
  st ← st.check "one worker still solves satisfaction"
    ((← runModel { threads := 1 } satModel) == 0)
  let satUnsat :=
    model "var 0..1: x; constraint int_eq(x,0); constraint int_eq(x,1); solve satisfy;"
  st ← st.check "four workers prove satisfaction UNSAT"
    ((← runModel { threads := 4 } satUnsat) == 1)
  let unsupported := model "var 1..2: x :: output_var; constraint int_pow(x,2,x); solve minimize x;"
  st ← st.check "an unsupported model stays exit 3 with one worker"
    ((← runModel { threads := 1 } unsupported) == 3)
  st ← st.check "an unsupported model stays exit 3 with four workers"
    ((← runModel { threads := 4 } unsupported) == 3)
  st ← st.check "programmatic portfolio rejects seeded optimization"
    ((← runModel { threads := 4, opt := .seeded } minModel) == 2)
  pure st

/-- A conflict-capped portfolio cannot claim a proof: a pigeonhole contradiction
that needs at least two conflicts is reported incomplete under a one-conflict
budget, while the same portfolio proves it UNSAT with two. -/
def incompleteTest (st : St) : IO St := do
  let m := model
    "var bool: x1; var bool: x2; var bool: x3; var bool: x4; var bool: x5;
     var bool: x6; var 0..1: obj :: output_var;
     constraint bool_clause([x1,x2],[]); constraint bool_clause([x3,x4],[]);
     constraint bool_clause([x5,x6],[]);
     constraint bool_clause([],[x1,x3]); constraint bool_clause([],[x1,x5]);
     constraint bool_clause([],[x3,x5]); constraint bool_clause([],[x2,x4]);
     constraint bool_clause([],[x2,x6]); constraint bool_clause([],[x4,x6]);
     solve minimize obj;"
  let mut st := st
  st ← st.check "capped portfolio reports incompleteness"
    ((← runModel { threads := 2, conflictLimit := some 1 } m) == 4)
  st ← st.check "portfolio proves the contradiction with two conflicts"
    ((← runModel { threads := 2, conflictLimit := some 2 } m) == 1)
  pure st

def main : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }
  st ← configTest st
  st ← solveTest st
  st ← incompleteTest st
  IO.println s!"passed {st.passed}, failed {st.failed}"
  if st.failed == 0 then
    IO.println "PortfolioTest: OK"
    return 0
  else
    IO.eprintln "PortfolioTest: FAILED"
    return 1

end Tests.Integration.Public.PortfolioTest

def main : IO UInt32 := Tests.Integration.Public.PortfolioTest.main
