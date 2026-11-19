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
import LeanFzn.Integration.Report.Runtime
import Std.Sync.Mutex

namespace LeanFzn.Core
open LeanFzn LeanFzn.Engine LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Integration.Report

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

/-- Feed a store to the sink, discarding the per-solution `Bool`; the sink
    records the failure and later calls become no-ops. -/
private def sinkEmit (sink : ReportSink) (model : Model) : Store → IO Unit :=
  fun store => do
    let _ ← sink.solution model store
    pure ()

/-- A report-internal failure: stderr diagnostics stay; JSONL gets a typed
    `internal` error and text mode keeps stdout empty.  Returns the exit code. -/
private def reportInternal (sink : ReportSink) (message : String) : IO UInt32 := do
  IO.eprintln s!"leanfzn: report internal error: {message}"
  sink.finishError .reportInternal message

/-- Report only certified terminal results; an incomplete optimization keeps
all previously streamed incumbents and makes no terminal proof claim. -/
private def finishOptimization (sink : ReportSink) (o : SearchConfig) (run : OptRun)
    (rounds : Nat) (st : Option EngineStats := none)
    (seeds : Option (List Nat) := none) : IO UInt32 := do
  emitStats o run.complete rounds run.sols.length st seeds
  let failed ← sink.failed
  let emitted ← sink.emitted
  let last ← sink.lastId
  match classifyOptimization run with
  | .incomplete =>
      if failed then
        return (← reportInternal sink "the report sink failed during an incomplete optimization run")
      IO.eprintln "leanfzn: Core optimization incomplete (gaveUp); incumbents retained"
      return (← sink.finishTerminal .incomplete none none)
  | .unsat =>
      if failed || emitted != 0 then
        return (← reportInternal sink "inconsistent report state for an UNSAT optimization run")
      return (← sink.finishTerminal .unsat none none)
  | .optimal _ =>
      if failed then
        return (← reportInternal sink "the report sink failed during optimization")
      if emitted != run.sols.length then
        return (← reportInternal sink
          s!"the report sink emitted {emitted} solutions for a run with {run.sols.length}")
      match last with
      | none =>
          return (← reportInternal sink "an optimal run has no emitted solution id")
      | some id =>
          return (← sink.finishTerminal .optimal (some id) none)

private def runSatisfactionWith (sink : ReportSink) (o : SearchConfig) (model : Model)
    (run : IO (Result × EngineStats)) : IO UInt32 := do
  let (r, st) ← run
  match classifySatisfaction r with
  | .sat store =>
      let ok ← sink.solution model store
      emitStats o true 0 0 (some st)
      if !ok then
        return (← reportInternal sink "the report sink failed on the satisfaction witness")
      return (← sink.finishTerminal .sat none none)
  | .unsat =>
      emitStats o true 0 0 (some st)
      return (← sink.finishTerminal .unsat none none)
  | .unsupported reason =>
      IO.eprintln s!"leanfzn: unsupported model: {reason}"
      emitStats o false 0 0 (some st)
      return (← sink.finishTerminal .unsupported none (some reason))
  | .unknown reason =>
      IO.eprintln s!"leanfzn: {reason}"
      emitStats o false 0 0 (some st)
      return (← sink.finishTerminal .incomplete none (some reason))

private def runSatisfaction (sink : ReportSink) (o : SearchConfig)
    (g : GatedModel) : IO UInt32 :=
  runSatisfactionWith sink o g.model (pure (solveModelWithStats g.model o coreFuel))

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
  /-- A witness/compile/sink failure; suppresses every terminal claim. -/
  error : Option String := none
  /-- The typed class of `error`: a worker compile rejection is
  `unsupportedScope` (exit 3); an inconsistent witness, sink failure or
  worker exception is `reportInternal` (exit 2). -/
  errorKind : Option ErrorKind := none

private structure PortfolioContext where
  mutex : Std.Mutex PortfolioState
  cond : Std.Condvar
  model : GatedModel
  maximize : Bool
  sink : ReportSink

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
  let text := emitCertifiedSolution ctx.model.model store
  let checked := LeanFzn.Checker.checkModelSolutionFast ctx.model.model text == .accepted
  let value? := ctx.model.model.solve.objective store
  let failed ← ctx.mutex.atomically do
    let st ← get
    if st.stop then return false
    if !checked then
      let st' : PortfolioState :=
        { st with
            stop := true,
            error := some "a portfolio worker produced a witness the checker rejected",
            errorKind := some .reportInternal }
      set st'
      return true
    else
      match value? with
      | none =>
          let st' : PortfolioState :=
            { st with
                stop := true,
                error := some "a portfolio worker produced a solution without an objective value",
                errorKind := some .reportInternal }
          set st'
          return true
      | some v =>
          let improves :=
            match st.best with
            | none => true
            | some prev => objectiveImproves ctx.maximize prev v
          if improves then
            let ok ← ctx.sink.solution ctx.model.model store
            if ok then
              set ({ st with best := some v, printed := st.printed + 1 })
              return false
            else
              let st' : PortfolioState :=
                { st with
                    stop := true,
                    error := some "the report sink rejected a portfolio solution",
                    errorKind := some .reportInternal }
              set st'
              return true
          return false
  if failed then ctx.cond.notifyAll

private def portfolioWorker (ctx : PortfolioContext) (o : SearchConfig) : IO Unit := do
  match ← optimizeStreamCoreStats o ctx.model.model (portfolioEmit ctx) with
  | .error reason =>
      ctx.mutex.atomically do
        let st ← get
        let st' : PortfolioState :=
          { st with
              running := st.running - 1,
              stop := true,
              error := if st.error.isSome then st.error
                else some s!"unsupported model: {reason}",
              errorKind := if st.errorKind.isSome then st.errorKind
                else some .unsupportedScope }
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
def runPortfolioOptimization (sink : ReportSink) (o : SearchConfig)
    (model : GatedModel) : IO UInt32 := do
  if o.threads ≤ 1 || o.threads > 8 then
    IO.eprintln "leanfzn: the portfolio requires 2..8 workers"
    return (← sink.finishError .usage "the portfolio requires 2..8 workers")
  match model.model.solve with
  | .satisfy _ =>
      IO.eprintln "leanfzn: option '--threads' is supported only for optimization models"
      return (← sink.finishError .usage "option '--threads' is supported only for optimization models")
  | _ => pure ()
  let maximize :=
    match model.model.solve with
    | .maximize _ _ => true
    | _ => false
  let mutex ← Std.Mutex.new ({ running := o.threads } : PortfolioState)
  let cond ← Std.Condvar.new
  let ctx : PortfolioContext := { mutex, cond, model, maximize, sink }
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
                  else some s!"worker failure: {e}",
                errorKind := if st.errorKind.isSome then st.errorKind
                  else some .reportInternal }
          set st'
        ctx.cond.notifyAll
  let st ← mutex.atomicallyOnce cond
    (fun s => do
      let st ← s.get
      return st.report.isSome || st.error.isSome || st.running == 0)
    (fun s => s.get)
  for t in tasks do IO.cancel t
  if let some err := st.error then
    let kind := st.errorKind.getD .reportInternal
    if kind == .unsupportedScope then
      IO.eprintln s!"leanfzn: {err}"
      emitStats o false 0 st.printed none
      return (← sink.finishTerminal .unsupported none (some err))
    IO.eprintln s!"leanfzn: portfolio: {err}"
    emitStats o false 0 st.printed none
    return (← sink.finishError kind err)
  match st.report with
  | none =>
      IO.eprintln "leanfzn: Core optimization incomplete (gaveUp); incumbents retained"
      emitStats o false 0 st.printed none
      return (← sink.finishTerminal .incomplete none none)
  | some report =>
      let failed ← sink.failed
      let emitted ← sink.emitted
      match report.optimal with
      | none =>
          if st.printed == 0 then
            if failed || emitted != 0 then
              return (← reportInternal sink "inconsistent report state for a portfolio UNSAT proof")
            emitStats o true report.rounds 0 (some report.stats)
            return (← sink.finishTerminal .unsat none none)
          else
            IO.eprintln "leanfzn: portfolio: a worker proved UNSAT after another printed an incumbent"
            emitStats o false report.rounds st.printed (some report.stats)
            return (← reportInternal sink
              "a worker proved UNSAT after another printed an incumbent")
      | some v =>
          if st.best == some v then
            let last ← sink.lastId
            if failed || emitted != st.printed then
              return (← reportInternal sink "the portfolio report sink is inconsistent with its incumbents")
            match last with
            | none =>
                return (← reportInternal sink "an optimal portfolio run has no emitted solution id")
            | some id =>
                emitStats o true report.rounds st.printed (some report.stats)
                return (← sink.finishTerminal .optimal (some id) none)
          else
            IO.eprintln
              s!"leanfzn: portfolio: proof optimum {v} does not match the best checked incumbent {st.best}"
            emitStats o false report.rounds st.printed (some report.stats)
            return (← reportInternal sink
              "portfolio proof optimum does not match the best checked incumbent")

/-! ## Parallel satisfaction (`--threads=N`)

A satisfaction model has no incumbents: each worker runs one ordinary certified
Core search, and the first completed verdict stops the portfolio.  A SAT
witness is checker-verified before it is accepted; an UNSAT verdict is a
completed proof.  Unknown workers are ignored while any worker is still
running. -/

/-- A completed satisfaction verdict and its counters.  The accepted witness
is kept as a `Store`; the driver renders it only when it emits the report
solution. -/
private inductive SatOutcome where
  | sat (store : Store) (stats : EngineStats)
  | unsat (stats : EngineStats)

/-- Shared satisfaction portfolio state, guarded by one mutex. -/
private structure SatState where
  running : Nat := 0
  verdict : Option SatOutcome := none
  stop : Bool := false
  error : Option String := none
  /-- The typed class of `error`: a worker compile rejection is
  `unsupportedScope` (exit 3); an inconsistent witness or worker exception is
  `reportInternal` (exit 2). -/
  errorKind : Option ErrorKind := none

private structure SatContext where
  mutex : Std.Mutex SatState
  cond : Std.Condvar
  model : GatedModel

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
  let (r, stats) := solveModelWithStats ctx.model.model o coreFuel
  match r with
  | .sat store =>
      let text := emitCertifiedSolution ctx.model.model store
      let checked := LeanFzn.Checker.checkModelSolutionFast ctx.model.model text == .accepted
      ctx.mutex.atomically do
        let st ← get
        if st.stop then return ()
        if !checked then
          let st' : SatState :=
            { st with
                stop := true,
                error := some "a portfolio worker produced a witness the checker rejected",
                errorKind := some .reportInternal }
          set st'
        else
          let st' : SatState :=
            { st with verdict := some (.sat store stats), stop := true }
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
              errorKind := some .unsupportedScope }
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
def runPortfolioSatisfaction (sink : ReportSink) (o : SearchConfig)
    (model : GatedModel) : IO UInt32 := do
  if o.threads ≤ 1 || o.threads > 8 then
    IO.eprintln "leanfzn: the portfolio requires 2..8 workers"
    return (← sink.finishError .usage "the portfolio requires 2..8 workers")
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
                  else some s!"worker failure: {e}",
                errorKind := if st.errorKind.isSome then st.errorKind
                  else some .reportInternal }
          set st'
        ctx.cond.notifyAll
  let st ← mutex.atomicallyOnce cond
    (fun s => do
      let st ← s.get
      return st.verdict.isSome || st.error.isSome || st.running == 0)
    (fun s => s.get)
  for t in tasks do IO.cancel t
  if let some err := st.error then
    let kind := st.errorKind.getD .reportInternal
    if kind == .unsupportedScope then
      IO.eprintln s!"leanfzn: {err}"
      emitStats o false 0 0 none
      return (← sink.finishTerminal .unsupported none (some err))
    IO.eprintln s!"leanfzn: portfolio: {err}"
    emitStats o false 0 0 none
    return (← sink.finishError kind err)
  match st.verdict with
  | some (.sat store stats) =>
      let ok ← sink.solution model.model store
      emitStats o true 0 0 (some stats)
      if !ok then
        return (← reportInternal sink "the report sink failed on the portfolio satisfaction witness")
      return (← sink.finishTerminal .sat none none)
  | some (.unsat stats) =>
      let failed ← sink.failed
      let emitted ← sink.emitted
      if failed || emitted != 0 then
        return (← reportInternal sink "inconsistent report state for a portfolio UNSAT proof")
      emitStats o true 0 0 (some stats)
      return (← sink.finishTerminal .unsat none none)
  | none =>
      IO.eprintln "leanfzn: Core satisfaction incomplete (gaveUp)"
      emitStats o false 0 0 none
      return (← sink.finishTerminal .incomplete none none)

private def runOptimization (sink : ReportSink) (o : SearchConfig)
    (g : GatedModel) : IO UInt32 := do
  let model := g.model
  if o.threads > 1 then
    runPortfolioOptimization sink o g
  else if o.primal == .lns then
    match ← optimizeStreamCoreLns o model (sinkEmit sink model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return (← sink.finishError .compileReject reason)
    | .ok (summary, st) =>
        finishOptimization sink o summary.run (summary.run.sols.length + 1) (some st)
  else if o.opt == .seeded then
    match ← optimizeStreamCoreSeed o model (sinkEmit sink model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return (← sink.finishError .compileReject reason)
    | .ok summary =>
        finishOptimization sink o summary.run summary.seeds.length none (some summary.seeds)
  else
    match ← optimizeStreamCoreStats o model (sinkEmit sink model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return (← sink.finishError .compileReject reason)
    | .ok (summary, st) =>
        finishOptimization sink o summary.run (summary.run.sols.length + 1) (some st)

/-- The CLI class of a gate failure, keeping the driver's exit codes: an
admission failure or an unprintable name is unsupported scope (3), an
ill-formed model is a model-parse failure (2). -/
private def GateError.kind : GateError → ErrorKind
  | .notAdmitted _ => .unsupportedScope
  | .notWellFormed => .modelParse
  | .unprintableName => .unsupportedScope

/-- The driver's stderr line for a gate failure (unchanged text). -/
private def GateError.stderrLine : GateError → String
  | .notAdmitted reason => s!"leanfzn: unsupported model: {reason}"
  | .notWellFormed => "leanfzn: model is not well-formed"
  | .unprintableName =>
      "leanfzn: unsupported model: a variable name cannot be printed as a solution identifier (reserved word or invalid characters)"

/-- Shared option/model validation.  Option checks report the terminal CLI
error class; the model checks are exactly `gate`, so the driver and the proved
verdict theorems share one admission/well-formedness/printable-name decision.
The stderr lines and exit classes are unchanged. -/
private def validateRun (o : SearchConfig) (model : Model) :
    IO (Except (ErrorKind × String) GatedModel) := do
  if o.engine != .core then
    let message := "the legacy kernel is unavailable in the public Core-only driver"
    IO.eprintln s!"leanfzn: {message}"
    return .error (.usage, message)
  if o.threads > 1 &&
      !((o.var == .minc && o.val == .act) ||
        (o.var == .act && o.val == .incumbent)) then
    let message :=
      "the thread portfolio selects its own strategies; do not combine it with a non-default var/val"
    IO.eprintln s!"leanfzn: {message}"
    return .error (.usage, message)
  match o.checkCoreImplemented with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      return .error (.usage, reason)
  | .ok _ => pure ()
  match o.checkImplemented with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      return .error (.usage, reason)
  | .ok _ => pure ()
  match gate model with
  | .ok g => return .ok g
  | .error e =>
      IO.eprintln e.stderrLine
      return .error (e.kind, e.message)

/-- Public programmatic entry also validates Core-only options, so callers
cannot bypass CLI checks to select a different implementation. -/
def runModelWithSink (sink : ReportSink) (o : SearchConfig)
    (model : Model) : IO UInt32 := do
  match ← validateRun o model with
  | .error (kind, message) =>
      return (← sink.finishError kind message)
  | .ok g =>
      sink.model model
      let modelFailed ← sink.failed
      if modelFailed then
        return (← reportInternal sink "the report sink failed on the model event")
      match model.solve with
      | .satisfy _ =>
          if o.primal != .none then
            let message := "a primal heuristic requires an optimization model"
            IO.eprintln s!"leanfzn: {message}"
            return (← sink.finishError .usage message)
          if o.threads > 1 then
            runPortfolioSatisfaction sink o g
          else
            runSatisfaction sink o g
      | .minimize _ _ | .maximize _ _ => runOptimization sink o g

/-- Public programmatic entry: the default text sink. -/
def runModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  let sink ← ReportSink.new .text
  runModelWithSink sink o model

/-- Phased optimization for the instrumented `--phase-stats` run.  The
specialized seeded/LNS/portfolio paths are not instrumented internally; they
run unchanged after a note (their stdout, exit code and counters are
identical). -/
private def runOptimizationPhased (sink : ReportSink) (ps : PhaseCtx)
    (o : SearchConfig) (g : GatedModel) : IO UInt32 := do
  if o.threads > 1 || o.primal == .lns || o.opt == .seeded then
    IO.eprintln
      "leanfzn: phase stats: specialized optimization path is not instrumented; running the ordinary driver"
    runOptimization sink o g
  else
    match ← optimizeStreamGatedCoreStatsPhased ps o g (sinkEmit sink g.model) with
    | .error reason =>
        IO.eprintln s!"leanfzn: unsupported model: {reason}"
        emitStats o false 0 0 (some {})
        return (← sink.finishError .compileReject reason)
    | .ok (summary, st) =>
        finishOptimization sink o summary.run (summary.run.sols.length + 1) (some st)

/-- `runModelWithSink` with the dev `--phase-stats` lines.  Every phase line
goes to stderr; stdout, exit codes and counters are exactly those of
`runModelWithSink` on the same model and options. -/
def runModelPhasedWithSink (sink : ReportSink) (ps : PhaseCtx) (o : SearchConfig)
    (model : Model) : IO UInt32 := do
  match ← validateRun o model with
  | .error (kind, message) =>
      return (← sink.finishError kind message)
  | .ok g =>
      sink.model model
      let modelFailed ← sink.failed
      if modelFailed then
        return (← reportInternal sink "the report sink failed on the model event")
      match model.solve with
      | .satisfy _ =>
          if o.primal != .none then
            let message := "a primal heuristic requires an optimization model"
            IO.eprintln s!"leanfzn: {message}"
            return (← sink.finishError .usage message)
          if o.threads > 1 then
            IO.eprintln
              "leanfzn: phase stats: the satisfaction portfolio is not instrumented; running the ordinary driver"
            runPortfolioSatisfaction sink o g
          else
            runSatisfactionWith sink o g.model (solveGatedModelWithPhaseStats ps g o coreFuel)
      | .minimize _ _ | .maximize _ _ => runOptimizationPhased sink ps o g

/-- `runModelPhased` with the default text sink. -/
def runModelPhased (ps : PhaseCtx) (o : SearchConfig) (model : Model) : IO UInt32 := do
  let sink ← ReportSink.new .text
  runModelPhasedWithSink sink ps o model

end LeanFzn.Core
