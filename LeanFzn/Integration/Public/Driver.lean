/-
Purpose: Core-only public CLI execution and output classification.
Dependencies: Public solve/linear/seeded APIs, common option parsing and checker gates.
DAG: Core source APIs -> this IO driver -> Cli.Main. Legacy imports are forbidden.
Unknown/incomplete runs use exit 4 and never emit UNSAT or optimum markers.
-/
import LeanFzn.Integration.Public.Solve
import LeanFzn.Integration.Public.Optimize
import LeanFzn.Integration.Public.PhaseStats
import LeanFzn.Integration.Public.Seed
import LeanFzn.Integration.Public.Lns
import LeanFzn.Integration.Config.Parse
import LeanFzn.Integration.Emit.Model
import LeanFzn.Checker.Runtime.Check
import Std.Sync.Mutex

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
  let causeField := match st with
    | some s => if s.gaveUpCause.isEmpty then "" else s!" cause=\"{s.gaveUpCause}\""
    | none => ""
  IO.eprintln s!"leanfzn: stats: steps=- decisions={counter (·.decisions)} maxLevel={counter (·.maxLevel)} conflicts={counter (·.conflicts)} learned={counter (·.learned)} learnedLitsBefore={counter (·.learnedLitsBefore)} learnedLitsAfter={counter (·.learnedLitsAfter)} learnedUnits={counter (·.learnedUnits)} reductions={counter (·.reductions)} reducedClauses={counter (·.reducedClauses)} reasonsTrimmed={counter (·.reasonsTrimmed)} propagations={counter (·.propagations)} rounds={rounds} incumbents={incumbents} restarts=- complete={if complete then 1 else 0} gaveUp={gaveUp}{causeField}{seedField}"

private def emitSolution (model : Model) (store : Store) : IO Unit := do
  IO.println (emitCertifiedSolution model store)
  (← IO.getStdout).flush

/-- Report only certified terminal results; an incomplete optimization keeps
all previously streamed incumbents and makes no terminal proof claim. -/
private def finishOptimization (o : SearchConfig) (run : OptRun) (rounds : Nat)
    (st : Option EngineStats := none) (seeds : Option (List Nat) := none) : IO UInt32 := do
  emitStats o run.complete rounds run.sols.length st seeds
  if !run.complete then
    IO.eprintln "leanfzn: Core optimization incomplete (gaveUp); incumbents retained"
    return 4
  if run.sols.isEmpty then
    IO.println "=====UNSATISFIABLE====="
    return 1
  IO.println optimumMarker
  return 0

private def runSatisfactionWith (o : SearchConfig) (model : Model)
    (run : IO (Result × EngineStats)) : IO UInt32 := do
  let (r, st) ← run
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

private def runSatisfaction (o : SearchConfig) (model : Model) : IO UInt32 :=
  runSatisfactionWith o model (pure (solveModelWithStats model o coreFuel))

/-! ## Parallel portfolio (`--threads=N`)

Each worker is an ordinary certified Core optimization run with its own
compiled problem and its own search state; nothing but the parsed model is
shared.  The driver prints only strictly improving checker-accepted
incumbents, and a completed proof is accepted only when its optimum matches
the best checked incumbent already printed.  The first completed proof stops
the portfolio; the CLI exits immediately afterwards. -/

/-- One completed worker's terminal data. -/
private structure WorkerReport where
  /-- The proved optimum; `none` means a completed UNSAT proof. -/
  optimal : Option Int
  rounds : Nat
  stats : EngineStats
  deriving Inhabited

/-- Shared portfolio state.  Every field is guarded by one mutex. -/
private structure PortfolioState where
  /-- Workers that have not reported a terminal state yet. -/
  running : Nat := 0
  /-- Best objective value actually printed (and checker-accepted). -/
  best : Option Int := none
  /-- Number of printed incumbents. -/
  printed : Nat := 0
  /-- First completed proof. -/
  report : Option WorkerReport := none
  /-- Stop printing new incumbents. -/
  stop : Bool := false
  /-- A witness/compile failure; suppresses every terminal claim. -/
  error : Option String := none
  /-- Whether the failure is an unsupported-model compile error (exit 3)
  rather than an inconsistent witness (exit 4). -/
  unsupported : Bool := false

private structure PortfolioContext where
  mutex : Std.Mutex PortfolioState
  cond : Std.Condvar
  model : Model
  maximize : Bool

private def objectiveImproves (maximize : Bool) (prev next : Int) : Bool :=
  if maximize then next > prev else next < prev

/-- The built-in portfolio: the four measured strategies, then a second copy
of each with the alternative after-incumbent Luby base.  An explicit
`--restart`/`--restart-base` pins the schedule for every worker instead. -/
private def portfolioConfigs (o : SearchConfig) : List SearchConfig :=
  let strategies : List (VarStrategy × ValStrategy) :=
    [(.act, .incumbent), (.minc, .incumbent), (.wdeg, .incumbent), (.annot, .annot)]
  let customBase := o.restartExplicit || o.restartBase != 100
  (List.range o.threads).map fun i =>
    let (var, val) := strategies.getD (i % 4) (.act, .incumbent)
    let base := if customBase then o.restartBase else if i < 4 then 100 else 50
    -- Worker timing/counter lines would interleave; the driver prints one
    -- aggregate diagnostic line after the portfolio finishes instead.
    { o with var := var, val := val, restartBase := base, threads := 1, stats := false }

private def portfolioEmit (ctx : PortfolioContext) (store : Store) : IO Unit := do
  let text := emitCertifiedSolution ctx.model store
  let checked := LeanFzn.Checker.checkModelSolutionFast ctx.model text == .accepted
  let value? := ctx.model.solve.objective store
  let failed ← ctx.mutex.atomically do
    let st ← get
    if st.stop then return false
    if !checked then
      let st' : PortfolioState :=
        { st with
            stop := true,
            error := some "a portfolio worker produced a witness the checker rejected" }
      set st'
      return true
    else
      match value? with
      | none =>
          let st' : PortfolioState :=
            { st with
                stop := true,
                error := some "a portfolio worker produced a solution without an objective value" }
          set st'
          return true
      | some v =>
          let improves :=
            match st.best with
            | none => true
            | some prev => objectiveImproves ctx.maximize prev v
          if improves then
            IO.println text
            (← IO.getStdout).flush
            set ({ st with best := some v, printed := st.printed + 1 })
          return false
  if failed then ctx.cond.notifyAll

private def portfolioWorker (ctx : PortfolioContext) (o : SearchConfig) : IO Unit := do
  match ← optimizeStreamCoreStats o ctx.model (portfolioEmit ctx) with
  | .error reason =>
      ctx.mutex.atomically do
        let st ← get
        let st' : PortfolioState :=
          { st with
              running := st.running - 1,
              stop := true,
              error := if st.error.isSome then st.error
                else some s!"unsupported model: {reason}",
              unsupported := st.unsupported || st.error.isNone }
        set st'
      ctx.cond.notifyAll
  | .ok (summary, st) =>
      let run := summary.run
      ctx.mutex.atomically do
        let s ← get
        let r : WorkerReport :=
          { optimal := run.sols.getLast?.map (fun p => p.2)
            rounds := run.sols.length + 1
            stats := st }
        let s' : PortfolioState :=
          { s with
              running := s.running - 1,
              report := if s.report.isNone && run.complete then some r else s.report,
              stop := s.stop || run.complete }
        set s'
      ctx.cond.notifyAll

/-- Independent-worker portfolio optimization.  The first completed proof is
the only terminal claim; all other workers are requested to stop and the CLI
exits, so a long-running round cannot delay the answer. -/
def runPortfolioOptimization (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.threads ≤ 1 || o.threads > 8 then
    IO.eprintln "leanfzn: the portfolio requires 2..8 workers"
    return 2
  match model.solve with
  | .satisfy _ =>
      IO.eprintln "leanfzn: option '--threads' is supported only for optimization models"
      return 2
  | _ => pure ()
  let maximize :=
    match model.solve with
    | .maximize _ _ => true
    | _ => false
  let mutex ← Std.Mutex.new ({ running := o.threads } : PortfolioState)
  let cond ← Std.Condvar.new
  let ctx : PortfolioContext := { mutex, cond, model, maximize }
  let tasks ← (portfolioConfigs o).mapM fun cfg =>
    IO.asTask (prio := Task.Priority.dedicated) do
      try
        portfolioWorker ctx cfg
      catch e =>
        -- A worker must always decrement `running` and wake the driver; an
        -- uncaught I/O failure would otherwise leave the portfolio waiting.
        ctx.mutex.atomically do
          let st ← get
          let st' : PortfolioState :=
            { st with
                running := st.running - 1,
                stop := true,
                error := if st.error.isSome then st.error
                  else some s!"worker failure: {e}" }
          set st'
        ctx.cond.notifyAll
  let st ← mutex.atomicallyOnce cond
    (fun s => do
      let st ← s.get
      return st.report.isSome || st.error.isSome || st.running == 0)
    (fun s => s.get)
  for t in tasks do IO.cancel t
  if let some err := st.error then
    if st.unsupported then
      IO.eprintln s!"leanfzn: {err}"
      emitStats o false 0 st.printed none
      return 3
    IO.eprintln s!"leanfzn: portfolio: {err}"
    emitStats o false 0 st.printed none
    return 4
  match st.report with
  | none =>
      IO.eprintln "leanfzn: Core optimization incomplete (gaveUp); incumbents retained"
      emitStats o false 0 st.printed none
      return 4
  | some report =>
      match report.optimal with
      | none =>
          if st.printed == 0 then
            IO.println "=====UNSATISFIABLE====="
            emitStats o true report.rounds 0 (some report.stats)
            return 1
          else
            IO.eprintln "leanfzn: portfolio: a worker proved UNSAT after another printed an incumbent"
            emitStats o false report.rounds st.printed (some report.stats)
            return 4
      | some v =>
          if st.best == some v then
            IO.println optimumMarker
            emitStats o true report.rounds st.printed (some report.stats)
            return 0
          else
            IO.eprintln
              s!"leanfzn: portfolio: proof optimum {v} does not match the best checked incumbent {st.best}"
            emitStats o false report.rounds st.printed (some report.stats)
            return 4

/-! ## Parallel satisfaction (`--threads=N`)

A satisfaction model has no incumbents: each worker runs one ordinary certified
Core search, and the first completed verdict stops the portfolio.  A SAT
witness is checker-verified before it is accepted; an UNSAT verdict is a
completed proof.  Unknown workers are ignored while any worker is still
running. -/

/-- A completed satisfaction verdict and its counters. -/
private inductive SatOutcome where
  | sat (text : String) (stats : EngineStats)
  | unsat (stats : EngineStats)

/-- Shared satisfaction portfolio state, guarded by one mutex. -/
private structure SatState where
  running : Nat := 0
  verdict : Option SatOutcome := none
  stop : Bool := false
  error : Option String := none
  unsupported : Bool := false

private structure SatContext where
  mutex : Std.Mutex SatState
  cond : Std.Condvar
  model : Model

/-- Satisfaction workers use one value presentation per variable strategy;
the optimization `incumbent` presentations need an objective incumbent. -/
private def satConfigs (o : SearchConfig) : List SearchConfig :=
  let strategies : List (VarStrategy × ValStrategy) :=
    [(.act, .act), (.minc, .min), (.wdeg, .act), (.annot, .annot)]
  let customBase := o.restartExplicit || o.restartBase != 100
  (List.range o.threads).map fun i =>
    let (var, val) := strategies.getD (i % 4) (.act, .act)
    let base := if customBase then o.restartBase else if i < 4 then 100 else 50
    { o with var := var, val := val, restartBase := base, threads := 1, stats := false }

private def satWorker (ctx : SatContext) (o : SearchConfig) : IO Unit := do
  let (r, stats) := solveModelWithStats ctx.model o coreFuel
  match r with
  | .sat store =>
      let text := emitCertifiedSolution ctx.model store
      let checked := LeanFzn.Checker.checkModelSolutionFast ctx.model text == .accepted
      ctx.mutex.atomically do
        let st ← get
        if st.stop then return ()
        if !checked then
          let st' : SatState :=
            { st with
                stop := true,
                error := some "a portfolio worker produced a witness the checker rejected" }
          set st'
        else
          let st' : SatState :=
            { st with verdict := some (.sat text stats), stop := true }
          set st'
      ctx.cond.notifyAll
  | .unsat =>
      ctx.mutex.atomically do
        let st ← get
        if st.stop then return ()
        let st' : SatState :=
          { st with verdict := some (.unsat stats), stop := true }
        set st'
      ctx.cond.notifyAll
  | .unsupported reason =>
      ctx.mutex.atomically do
        let st ← get
        if st.stop then return ()
        let st' : SatState :=
          { st with
              stop := true,
              error := some s!"unsupported model: {reason}",
              unsupported := true }
        set st'
      ctx.cond.notifyAll
  | .unknown _ =>
      ctx.mutex.atomically do
        let st ← get
        let st' : SatState := { st with running := st.running - 1 }
        set st'
      ctx.cond.notifyAll

/-- Independent-worker satisfaction search.  The first completed verdict is
the only terminal claim; a SAT witness is printed only after the checker
accepts it. -/
def runPortfolioSatisfaction (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.threads ≤ 1 || o.threads > 8 then
    IO.eprintln "leanfzn: the portfolio requires 2..8 workers"
    return 2
  let mutex ← Std.Mutex.new ({ running := o.threads } : SatState)
  let cond ← Std.Condvar.new
  let ctx : SatContext := { mutex, cond, model }
  let tasks ← (satConfigs o).mapM fun cfg =>
    IO.asTask (prio := Task.Priority.dedicated) do
      try
        satWorker ctx cfg
      catch e =>
        ctx.mutex.atomically do
          let st ← get
          let st' : SatState :=
            { st with
                running := st.running - 1,
                stop := true,
                error := if st.error.isSome then st.error
                  else some s!"worker failure: {e}" }
          set st'
        ctx.cond.notifyAll
  let st ← mutex.atomicallyOnce cond
    (fun s => do
      let st ← s.get
      return st.verdict.isSome || st.error.isSome || st.running == 0)
    (fun s => s.get)
  for t in tasks do IO.cancel t
  if let some err := st.error then
    if st.unsupported then
      IO.eprintln s!"leanfzn: {err}"
      emitStats o false 0 0 none
      return 3
    IO.eprintln s!"leanfzn: portfolio: {err}"
    emitStats o false 0 0 none
    return 4
  match st.verdict with
  | some (.sat text stats) =>
      IO.println text
      (← IO.getStdout).flush
      emitStats o true 0 0 (some stats)
      return 0
  | some (.unsat stats) =>
      IO.println "=====UNSATISFIABLE====="
      emitStats o true 0 0 (some stats)
      return 1
  | none =>
      IO.eprintln "leanfzn: Core satisfaction incomplete (gaveUp)"
      emitStats o false 0 0 none
      return 4

private def runOptimization (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.threads > 1 then
    runPortfolioOptimization o model
  else if o.primal == .lns then
    match ← optimizeStreamCoreLns o model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok (summary, st) =>
        finishOptimization o summary.run (summary.run.sols.length + 1) (some st)
  else if o.opt == .seeded then
    match ← optimizeStreamCoreSeed o model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok summary =>
        finishOptimization o summary.run summary.seeds.length none (some summary.seeds)
  else
    match ← optimizeStreamCoreStats o model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok (summary, st) =>
        finishOptimization o summary.run (summary.run.sols.length + 1) (some st)

/-- Shared option/model validation; `some rc` is the terminal CLI result. -/
private def validateRun (o : SearchConfig) (model : Model) : IO (Option UInt32) := do
  if o.engine != .core then
    IO.eprintln "leanfzn: the legacy kernel is unavailable in the public Core-only driver"
    return some 2
  match o.checkCoreImplemented with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      return some 2
  | .ok _ => pure ()
  match o.checkImplemented with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      return some 2
  | .ok _ => pure ()
  if !LeanFzn.Checker.wellFormedFastB model then
    IO.eprintln "leanfzn: model is not well-formed"
    return some 2
  return none

/-- Public programmatic entry also validates Core-only options, so callers
cannot bypass CLI checks to select a different implementation. -/
def runModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  match ← validateRun o model with
  | some rc => return rc
  | none =>
      match model.solve with
      | .satisfy _ =>
          if o.primal != .none then
            IO.eprintln "leanfzn: a primal heuristic requires an optimization model"
            return 2
          if o.threads > 1 then
            runPortfolioSatisfaction o model
          else
            runSatisfaction o model
      | .minimize _ _ | .maximize _ _ => runOptimization o model

/-- Phased optimization for the instrumented `--phase-stats` run.  The
specialized seeded/LNS/portfolio paths are not instrumented internally; they
run unchanged after a note (their stdout, exit code and counters are
identical). -/
private def runOptimizationPhased (ps : PhaseCtx) (o : SearchConfig)
    (model : Model) : IO UInt32 := do
  if o.threads > 1 || o.primal == .lns || o.opt == .seeded then
    IO.eprintln
      "leanfzn: phase stats: specialized optimization path is not instrumented; running the ordinary driver"
    runOptimization o model
  else
    match ← optimizeStreamCoreStatsPhased ps o model (emitSolution model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return 3
    | .ok (summary, st) =>
        finishOptimization o summary.run (summary.run.sols.length + 1) (some st)

/-- `runModel` with the dev `--phase-stats` lines.  Every phase line goes to
stderr; stdout, exit codes and counters are exactly those of `runModel` on
the same model and options. -/
def runModelPhased (ps : PhaseCtx) (o : SearchConfig) (model : Model) : IO UInt32 := do
  match ← validateRun o model with
  | some rc => return rc
  | none =>
      match model.solve with
      | .satisfy _ =>
          if o.primal != .none then
            IO.eprintln "leanfzn: a primal heuristic requires an optimization model"
            return 2
          if o.threads > 1 then
            IO.eprintln
              "leanfzn: phase stats: the satisfaction portfolio is not instrumented; running the ordinary driver"
            runPortfolioSatisfaction o model
          else
            runSatisfactionWith o model (solveModelWithPhaseStats ps model o coreFuel)
      | .minimize _ _ | .maximize _ _ => runOptimizationPhased ps o model

end LeanFzn.Core
