/-
Purpose: Regress Core-only satisfaction, partial optimization, streaming and option rejection.
Dependencies: Public Core APIs and the independent solution checker; no Legacy imports.
DAG: public Core entry points -> native regression executable.
-/
import LeanFzn.Integration.Public
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Engine
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

namespace Tests.Integration.Public.Runtime

private def model (s : String) : Model :=
  match LeanFzn.Parser.parseModel s with
  | .ok m => m
  | .error e => panic! e

private def expect (label : String) (b : Bool) : IO Unit := do
  if !b then throw (IO.userError s!"FAIL: {label}")
  IO.println s!"ok {label}"

private def config : SearchConfig := { var := .act, val := .min }

/-- A deliberately partial certified oracle: one accepted incumbent, then stop.
This exercises the real generic optimizer's preservation of partial progress. -/
def stopVerdict (prev : Option (List Value)) (p : CompiledProblem DomConstraint) : CertVerdict :=
  if prev.isSome then .fail
  else if h : [.int 0] ∈ allAssigns p.domains ∧ accepts p [.int 0] = true then
    .sat [.int 0]
  else .fail

def stoppedSolver : LeanFzn.Integration.PartialCertSolver where
  solveWith := stopVerdict
  sat_sound := by
    intro p prev a h
    unfold stopVerdict at h
    split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
  unsat_sound := by
    intro p prev h
    unfold stopVerdict at h
    split at h
    · cases h
    · split at h <;> cases h

private def checkRun (m : Model) (p : CompiledProblem DomConstraint) (run : OptRun) : Bool :=
  run.sols.all fun t =>
    accepts p t.1 &&
      LeanFzn.Checker.checkModelSolutionFast m (emitCertifiedSolution m (p.toStore t.1)) == .accepted

def main : IO UInt32 := do
  match LeanFzn.Core.parseSolveFlags [] with
  | .error e => throw (IO.userError e)
  | .ok (o, _) => expect "Core act/min default" (o.engine == .core && o.var == .act && o.val == .min)
  expect "removed certified option is unknown"
    (match LeanFzn.Core.parseSolveFlags ["--certified"] with
     | .error msg => msg == "unknown option '--certified'"
     | .ok _ => false)
  for args in [["--engine=kernel"], ["--time-limit=10"], ["--var=obj"],
      ["--opt=bisect"], ["--primal=dive"], ["--heur-act"],
      ["--portfolio=opt-fast:1,opt-fast"], ["--opt=seeded", "--val=incumbent"]] do
    expect s!"reject legacy-only flags {args}" (match LeanFzn.Core.parseSolveFlags args with | .error _ => true | _ => false)
  let sat := model "var 0..2: x :: output_var; solve satisfy;"
  match LeanFzn.Core.solveModel sat config with
  | .sat store =>
      expect "source SAT witness checked"
        (LeanFzn.Checker.checkModelSolutionFast sat (emitCertifiedSolution sat store) == .accepted)
  | _ => throw (IO.userError "expected Core SAT")
  let unsat := model "var 0..1: x; constraint int_eq(x,0); constraint int_eq(x,1); solve satisfy;"
  expect "certified UNSAT" (match LeanFzn.Core.solveModel unsat config with | .unsat => true | _ => false)
  let sparse := model "var {0,1000000}: x :: output_var; solve satisfy;"
  let (r, st) := LeanFzn.Core.solveModelWithStats sparse config coreFuel
  expect "wide sparse input stays unknown without fallback"
    ((match r with | .unknown _ => true | _ => false) && st.gaveUp == 1)
  for direction in ["minimize", "maximize"] do
    let m := model s!"var 0..2: x :: output_var; solve {direction} x;"
    let expected : Int := if direction == "minimize" then 0 else 2
    match LeanFzn.Core.optimizeCore m config with
    | .error e => throw (IO.userError e)
    | .ok (p, run) =>
        expect s!"linear {direction} completion" run.complete
        expect s!"linear {direction} witnesses" (checkRun m p run)
        expect s!"linear {direction} optimum" (run.sols.getLast?.map (·.2) == some expected)
    match LeanFzn.Core.optimizeCoreSeed config m with
    | .error e => throw (IO.userError e)
    | .ok sum =>
        expect s!"seeded {direction} completion" sum.run.complete
        expect s!"seeded {direction} witnesses" (checkRun m sum.p sum.run)
        expect s!"seeded {direction} optimum" (sum.run.sols.getLast?.map (·.2) == some expected)
        expect "seed trace matches rounds" (sum.seeds.length == sum.run.sols.length + 1)
  let sparseOpt := model "var {0,1000000}: x :: output_var; solve minimize x;"
  match LeanFzn.Core.optimizeCore sparseOpt config, LeanFzn.Core.optimizeCoreSeed config sparseOpt with
  | .ok (_, run), .ok sum =>
      expect "both optimizers preserve give-up"
        (!run.complete && !sum.run.complete && run.sols.isEmpty && sum.run.sols.isEmpty)
  | _, _ => throw (IO.userError "expected compiled incomplete optimization")
  match compileModelFull sat with
  | .error e => throw (IO.userError e)
  | .ok p =>
      expect "zero-fuel satisfaction is unknown" (match LeanFzn.Core.solveCompiled p config 0 with | .unknown => true | _ => false)
      expect "zero-fuel seeded verdict is incomplete"
        ((LeanFzn.Core.coreSeedVerdict config 0 none p (CoreSeed.initial p)).1 matches .fail)
  let maxModel := model "var 0..3: x :: output_var; solve maximize x;"
  let oracle := stoppedSolver.asCertSolver
  match optimizeCertified oracle maxModel with
  | .error e => throw (IO.userError e)
  | .ok (p, run) =>
      expect "partial optimizer retains first incumbent" (!run.complete && run.sols.length == 1 && checkRun maxModel p run)
  let emitted ← IO.mkRef ([] : List String)
  match ← optimizeStream oracle maxModel (fun store => emitted.modify (· ++ [emitCertifiedSolution maxModel store])) with
  | .error e => throw (IO.userError e)
  | .ok sum =>
      expect "streamed incumbent retained on later give-up" (!sum.run.complete && (← emitted.get).length == 1)
  let seedModel := model "var 0..2: x :: output_var; var bool: b; constraint bool_clause([b],[]); solve maximize x;"
  match LeanFzn.Core.optimizeCoreSeed config seedModel with
  | .error e => throw (IO.userError e)
  | .ok sum =>
      expect "seeded optimizer carries learned/seeded clauses"
        (sum.run.complete && sum.seeds.length > 1 && (sum.seeds.drop 1).all (· > 0))
  IO.println "Core-only public regressions: PASS"
  return 0

end Tests.Integration.Public.Runtime

def main : IO UInt32 := Tests.Integration.Public.Runtime.main
