/-
File: Tests/Integration/Public/IncumbentTest.lean

N15 runtime tests for incumbent-guided Core rounds: `seedPhases` maps a
previous incumbent to the saved-phase array, `selectValue` under
`--val=incumbent` tries that phase for every variable strategy, and the
entries `coreSolveFullWith` / `coreSolveWith` / `coreVerdictWith` and
`coreSolveSeed` honour it end to end.  Both the linear and the seeded Core
gate accept `--val=incumbent`.

Run with:
  lake env lean --run Tests/Integration/Public/IncumbentTest.lean
-/
import LeanFzn.Integration.Public.Optimize
import LeanFzn.Engine.Incremental
import LeanFzn.Parser.Parser

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration
open LeanFzn.Core

namespace Tests.Integration.Public.Incumbent

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"IncumbentTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-- A compiled problem with the supplied domains and constraints. -/
def mkProblem (ds : List Dom) (dcs : List DomConstraint) :
    CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := dcs
    objective := ()
    source := default
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray
    toStore := fun _ _ => none }

/-- One free integer slot `0..3`. -/
def freeProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b1111⟩] []

def cfg (v : VarStrategy) (vl : ValStrategy) : SearchConfig :=
  { engine := .core, var := v, val := vl }

def gateOk (c : SearchConfig) : Bool :=
  match c.checkCoreImplemented with
  | .ok _ => true
  | .error _ => false

/-- `selectValue` under `--val=incumbent` and the seeded entries. -/
def unitChecks : IO Unit := do
  check "selectValue: incumbent tries the saved maximum"
    (selectValue 0 (.bounds 0 3) (cfg .minc .incumbent) .none (some (.int 3)) ==
      some (negLe 0 2))
  check "selectValue: incumbent tries an interior value"
    (selectValue 0 (.bounds 0 3) (cfg .annot .incumbent) .none (some (.int 2)) ==
      some (negNe 0 2))
  check "selectValue: incumbent ignores a value outside the domain"
    (selectValue 0 (.bounds 0 1) (cfg .minc .incumbent) .none (some (.int 3)) ==
      some (posLe 0 0))
  check "selectValue: incumbent booleans use the saved value"
    (selectValue 0 (.bool 0b11) (cfg .minc .incumbent) .none (some (.bool true)) ==
      some (posBool 0 true))
  check "selectValue: act/minc still ignores the saved phase"
    (selectValue 0 (.bounds 0 3) (cfg .minc .act) .none (some (.int 3)) ==
      some (posLe 0 0))

/-- The entry and the verdict plumbing observe the seeded phase. -/
def entryChecks : IO Unit := do
  match coreSolveFullWith freeProblem (cfg .minc .incumbent) (some [.int 3]) 100,
        coreSolveFullWith freeProblem (cfg .minc .min) (some [.int 3]) 100,
        coreSolveFullWith freeProblem (cfg .minc .incumbent) none 100 with
  | (.sat a, _), (.sat b, _), (.sat c, _) =>
      check s!"entry: incumbent picks 3, got {repr a}" (a == [.int 3])
      check s!"entry: min ignores the seed, got {repr b}" (b == [.int 0])
      check s!"entry: first round without a seed picks 0, got {repr c}" (c == [.int 0])
  | _, _, _ => fail "entry: free problem did not return SAT"
  match coreSolveSeed freeProblem (cfg .minc .incumbent) (some [.int 3]) 100
      (CoreSeed.initial freeProblem) with
  | (.sat a, _, _) =>
      check s!"seeded entry: incumbent phase picks 3, got {repr a}" (a == [.int 3])
  | _ => fail "seeded entry: free problem did not return SAT"
  match coreVerdictWith (some [.int 3]) freeProblem (cfg .minc .incumbent) with
  | .sat a =>
      check s!"verdict: seeded verdict returns the incumbent, got {repr a}"
        (a == [.int 3])
  | _ => fail "verdict: seeded verdict is not SAT"
  let S : CertSolver := coreSolver (cfg .minc .incumbent)
  match S.solveWith (some [.int 3]) freeProblem with
  | .sat a =>
      check s!"solver: solveWith returns the incumbent, got {repr a}"
        (a == [.int 3])
  | _ => fail "solver: solveWith is not SAT"

/-- The option gate: both drivers accept the incumbent route. -/
def gateChecks : IO Unit := do
  check "gate: linear core accepts --val=incumbent"
    (gateOk { engine := .core, val := .incumbent, opt := .linear })
  check "gate: seeded core accepts --val=incumbent"
    (gateOk { engine := .core, val := .incumbent, opt := .seeded })

/-- A small optimization model runs end to end under the incumbent route and
reaches the same optimum as the incumbent-free minimum route. -/
def optChecks : IO Unit := do
  let src := "var 0..4: x; var 0..4: y; constraint int_lin_le([-1,-1],[x,y],-4); solve minimize y;"
  match Parser.parseModel src with
  | .error e => fail s!"opt: parse {e}"
  | .ok m =>
      match optimizeCore m (cfg .minc .incumbent),
            optimizeCore m (cfg .minc .min) with
      | .ok (_, run), .ok (_, base) =>
          check "opt: incumbent run completes" run.complete
          check "opt: incumbent run is nonempty" (!run.sols.isEmpty)
          check "opt: incumbent run matches the min run"
            (run.complete == base.complete &&
              run.sols.getLast?.map (fun s => s.2) ==
                base.sols.getLast?.map (fun s => s.2))
      | _, _ => fail "opt: optimizeCore failed"

end Tests.Integration.Public.Incumbent

open Tests.Integration.Public.Incumbent in
def main : IO UInt32 := do
  unitChecks
  entryChecks
  gateChecks
  optChecks
  IO.println "IncumbentTest: OK"
  return 0
