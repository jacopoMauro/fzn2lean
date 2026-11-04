/-
Purpose: Core-only public CLI execution and output classification.
Dependencies: Public solve/linear/seeded APIs, common option parsing and checker gates.
DAG: Core source APIs -> this IO driver -> Cli.Main. Legacy imports are forbidden.
Unknown/incomplete runs use exit 4 and never emit UNSAT or optimum markers.
-/
import LeanFzn.Integration.Public.Solve
import LeanFzn.Integration.Public.Optimize
import LeanFzn.Integration.Public.Seed
import LeanFzn.Integration.Config.Parse
import LeanFzn.Integration.Emit.Model
import LeanFzn.Checker.Runtime.Check

namespace LeanFzn.Core
open LeanFzn LeanFzn.Engine LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration

/-- Public parsing never converts unsupported Core options into a legacy run. -/
def parseSolveFlags := LeanFzn.Integration.parseCoreSolveFlags

private def emitStats (o : SearchConfig) (complete : Bool)
    (rounds incumbents : Nat) (st : Option EngineStats := none)
    (seeds : Option (List Nat) := none) : IO Unit := do
  if !o.stats then return
  let counter (f : EngineStats → Nat) := match st with
    | some s => toString (f s)
    | none => "-"
  let gaveUp := match st with
    | some s => s.gaveUp
    | none => if complete then 0 else 1
  let seedField := match seeds with
    | none => ""
    | some xs => s!" seeds={",".intercalate (xs.map toString)}"
  IO.eprintln s!"leanfzn: stats: steps=- decisions={counter (·.decisions)} conflicts={counter (·.conflicts)} learned={counter (·.learned)} propagations={counter (·.propagations)} rounds={rounds} incumbents={incumbents} restarts=- complete={if complete then 1 else 0} gaveUp={gaveUp}{seedField}"

private def emitSolution (model : Model) (store : Store) : IO Unit := do
  IO.println (emitCertifiedSolution model store)
  (← IO.getStdout).flush

/-- Report only certified terminal results; an incomplete optimization keeps
all previously streamed incumbents and makes no terminal proof claim. -/
private def finishOptimization (o : SearchConfig) (run : OptRun) (rounds : Nat)
    (seeds : Option (List Nat) := none) : IO UInt32 := do
  emitStats o run.complete rounds run.sols.length none seeds
  if !run.complete then
    IO.eprintln "leanfzn: Core optimization incomplete (gaveUp); incumbents retained"
    return 4
  if run.sols.isEmpty then
    IO.println "=====UNSATISFIABLE====="
    return 1
  IO.println optimumMarker
  return 0

private def runSatisfaction (o : SearchConfig) (model : Model) : IO UInt32 := do
  let (r, st) := solveModelWithStats model o coreFuel
  match r with
  | .sat store =>
      emitSolution model store
      emitStats o true 0 0 (some st)
      return 0
  | .unsat =>
      IO.println "=====UNSATISFIABLE====="
      emitStats o true 0 0 (some st)
      return 1
  | .unsupported reason =>
      IO.eprintln s!"leanfzn: unsupported model: {reason}"
      emitStats o false 0 0 (some st)
      return 3
  | .unknown reason =>
      IO.eprintln s!"leanfzn: {reason}"
      emitStats o false 0 0 (some st)
      return 4

private def runOptimization (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.opt == .seeded then
    match ← optimizeStreamCoreSeed o model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok summary =>
        finishOptimization o summary.run summary.seeds.length (some summary.seeds)
  else
    match ← optimizeStream (coreSolver o) model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok summary => finishOptimization o summary.run (summary.run.sols.length + 1)

/-- Public programmatic entry also validates Core-only options, so callers
cannot bypass CLI checks to select a different implementation. -/
def runModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.engine != .core then
    IO.eprintln "leanfzn: the legacy kernel is unavailable in the public Core-only driver"
    return 2
  match o.checkImplemented with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      return 2
  | .ok _ => pure ()
  if !LeanFzn.Checker.wellFormedFastB model then
    IO.eprintln "leanfzn: model is not well-formed"
    return 2
  match model.solve with
  | .satisfy _ => runSatisfaction o model
  | .minimize _ _ | .maximize _ _ => runOptimization o model

end LeanFzn.Core
