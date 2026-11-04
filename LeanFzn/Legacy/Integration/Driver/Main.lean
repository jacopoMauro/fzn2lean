/-
File: LeanFzn/Integration/Driver/Main.lean

Purpose:
  The IO-level strategy driver (PLAN §2.1 and §3 F1). It owns the output and
  exit-code policy of `leanfzn solve`, including `--time-limit` and `--stats`.
  In F1 it runs the same complete certified routes as before; later strategy
  items replace the configuration passed to those routes, never the claim
  discipline below.

Claim discipline (PLAN §2.1). Every printed item maps to a theorem:
  * a satisfaction store is printed only from `solveCertified ... = .sat s`
    (`solveCertified_sat_correct` at the source level) or, on the Core route
    (the default since N14), from `solveCertifiedCore ... = .sat s`
    (`solveCertifiedCore_sat_correct`);
  * an optimization incumbent is printed only from
    `optimizeStream`/`optimizeStreamTimed`, whose `emit` is called on the SAT
    result of a certified round (`optimizeStream_eq`; the timed loop is the
    same recursion with a deadline checked before each round);
  * `==========` is printed only after the streaming run reports
    `complete = true`, i.e. the strict improving bound was certified
    infeasible (`optimizeCertified_optimal`); `=====UNSATISFIABLE=====` for an
    optimization model is printed only after a completed run with no
    incumbent (`optimizeCertified_unsat`);
  * the F4 bisection route streams each certified SAT-probe witness before
    the next probe (`optimizeBisectStream_eq`); every streamed store of the
    bounded trace is a source-satisfying incumbent
    (`bisectLoopEmitSpec_solution_sound`), and the missing-root-bounds
    fallback is the complete linear route; markers are printed only when
    `summary.run.complete = true` (`optimizeBisect_optimal` /
    `optimizeBisect_unsat`), and an incomplete run makes no claim;
  * a satisfaction `=====UNSATISFIABLE=====` is printed only from
    `solveCertified ... = .unsat` (`solveCertified_unsat_correct`) or
    `solveCertifiedCore ... = .unsat` (`solveCertifiedCore_unsat_correct`).

Time limits (R1, approved 2026-10-28):
  * optimization checks the absolute deadline before each certified round;
    a stopped run prints the incumbents already found, no `==========`, and
    exits 0;
  * satisfaction is one atomic complete certified slice; if it finishes past
    the deadline its verdict is suppressed and the driver exits 4 ("unknown
    within budget", documented in the CLI header);
  * an unsupported model (compile error or failed gate) is reported as such
    even under a zero budget; a budget never turns an error into a claim.

DAG:
  CertifiedSolve + Optimize + LcgOptimize + OptimizeBisect + SearchConfig
  + OptimizeBudget + CoreSolve + CoreOptimize + CoreSeed -> StrategyDriver
  -> Cli.Main
-/

import LeanFzn.Legacy.Integration.Solve.Certified
import LeanFzn.Legacy.Integration.Solve.Core
import LeanFzn.Legacy.Integration.Optimization.Kernel
import LeanFzn.Legacy.Integration.Optimization.Core
import LeanFzn.Legacy.Integration.Optimization.CoreSeed
import LeanFzn.Legacy.Integration.Optimization.KernelSeedConfig
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Optimization.Chronological
import LeanFzn.Legacy.Integration.Optimization.Bisect
import LeanFzn.Legacy.Integration.Optimization.Budget
import LeanFzn.Legacy.Integration.Optimization.Primal
import LeanFzn.Legacy.Integration.SearchConfig

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

/-- Monotonic wall clock in milliseconds. -/
def monoMsNow : IO Nat :=
  IO.monoMsNow

/-! ## Driver counters -/

/-- Driver-level counters. The engine counters are `Option`s: `none` prints
    `-` rather than fabricating zeros (the optimization route keeps them unset
    until its per-round stats plumbing lands; the satisfaction route fills them
    from `solveCertifiedStats` or `solveCertifiedCoreStats`). -/
structure RunStats where
  steps : Option Nat := none
  decisions : Option Nat := none
  conflicts : Option Nat := none
  learned : Option Nat := none
  propagations : Option Nat := none
  rounds : Nat := 0
  incumbents : Nat := 0
  restarts : Nat := 0
  complete : Bool := false
  /-- The seeded route's per-round learned-database sizes (F4). -/
  seeds : Option (List Nat) := none
  /-- Primal slices that ran (F6). -/
  primalSlices : Nat := 0
  /-- Checked primal candidates admitted (F6). -/
  primalCandidates : Nat := 0
  /-- The primal phase was skipped because the mixed gate failed (F6). -/
  primalSkipped : Bool := false
  /-- Core-engine give-up count.  Kernel routes leave this unset (`-`);
      a positive value means the Core attempt fell back to the kernel. -/
  gaveUp : Option Nat := none
  deriving Repr, Inhabited

/-- Render an optional engine counter. -/
def showCounter : Option Nat → String
  | some n => toString n
  | none => "-"

/-- The engine part of a run's terminal counters. -/
def engineRunStats (st : SearchStats) : RunStats :=
  { steps := some st.steps, decisions := some st.decisions,
    conflicts := some st.conflicts, learned := some st.learnedClauses,
    propagations := some st.propagations }

/-- The Core-engine part of a run's terminal counters.  Core has no
    scheduler-transition count, so `steps` stays unset (`-`); `gaveUp`
    records the number of internal Core give-ups (0 on a Core verdict,
    1 when the seam fell back to the kernel). -/
def coreRunStats (st : LeanFzn.Engine.EngineStats) : RunStats :=
  { decisions := some st.decisions
    propagations := some st.propagations
    conflicts := some st.conflicts
    learned := some st.learned
    gaveUp := some st.gaveUp }

/-- Print one stable stats line to stderr (stdout is never touched). -/
def emitStats (s : RunStats) : IO Unit :=
  let seedField :=
    match s.seeds with
    | none => ""
    | some xs => s!" seeds={",".intercalate (xs.map toString)}"
  let primalField :=
    if s.primalSlices == 0 && !s.primalSkipped then ""
    else s!" primal-slices={s.primalSlices} primal-candidates={s.primalCandidates} primal-skipped={if s.primalSkipped then 1 else 0}"
  let gaveUpField :=
    match s.gaveUp with
    | none => ""
    | some n => s!" gaveUp={n}"
  IO.eprintln
    s!"leanfzn: stats: steps={showCounter s.steps} decisions={showCounter s.decisions} conflicts={showCounter s.conflicts} learned={showCounter s.learned} propagations={showCounter s.propagations} rounds={s.rounds} incumbents={s.incumbents} restarts={s.restarts} complete={if s.complete then 1 else 0}{seedField}{primalField}{gaveUpField}"

/-! ## The timed streaming branch-and-bound loop -/

/-- A streaming run with its accounting: `rounds` is the number of certified
    solves actually performed, and `stopped` records that the deadline was
    reached before a round (so no claim follows from this run). -/
structure TimedRun where
  run : OptRun
  rounds : Nat
  stopped : Bool

/-- `optimizeStreamLoop` with an absolute wall-clock deadline checked before
    every certified round, threading the previous incumbent (F3 phase saving).
    The recursion is the same one; a stopped prefix returns the empty run at
    the current bound. -/
def optimizeStreamTimedWith {α : Type} (S : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) (deadline : Option Nat) :
    Option (List Value) → Option Int → IO TimedRun
  | prev, bo => do
      if let some d := deadline then
        if (← monoMsNow) ≥ d then
          return ⟨⟨[], false, bo⟩, 0, true⟩
      match hs : S.solveWith prev (curP p0 spec bo) with
      | .unsat => pure ⟨⟨[], true, bo⟩, 1, false⟩
      | .fail => pure ⟨⟨[], false, bo⟩, 1, false⟩
      | .sat a =>
          match hv : a[spec.slot]? with
          | some (.int v) =>
              emit (f a) >>= fun _ =>
                optimizeStreamTimedWith S p0 spec f emit deadline (some a) (some v) >>= fun r =>
                  pure ⟨⟨(a, v) :: r.run.sols, r.run.complete, r.run.lastBound⟩,
                    r.rounds + 1, r.stopped⟩
          | _ => pure ⟨⟨[], false, bo⟩, 1, false⟩
termination_by prev bo => meas p0 spec bo
decreasing_by
  have h := S.solveWith_sat _ _ _ hs
  rw [curP_domains] at h
  exact meas_decr h.1 h.2 hv

/-- The root timed run (no previous incumbent). -/
def optimizeStreamTimed {α : Type} (S : CertSolver)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) (deadline : Option Nat) :
    Option Int → IO TimedRun :=
  optimizeStreamTimedWith S p0 spec f emit deadline none

/-! ## Engine dispatch -/

/-- The certified per-round solver of the configured engine. -/
def SearchConfig.certSolver (o : SearchConfig) : CertSolver :=
  match o.engine with
  | .core => coreSolver o
  | .kernel => lcgSolver o

/-- Whether the kernel's F5 restart/portfolio driver owns the run.  Core runs
its restarts inside each search, so only the kernel route needs the driver. -/
def SearchConfig.usesF5Driver (o : SearchConfig) : Bool :=
  o.portfolio.isSome || (o.restart != .none && o.engine == .kernel)

/-! ## Source-model runs -/

/-- Emit one improving solution and flush, exactly as the pre-F1 CLI did. -/
private def emitOptimizationSolution (model : Model) (store : Store) : IO Unit := do
  IO.println (emitCertifiedSolution model store)
  (← IO.getStdout).flush

/-- Whether an atomic run that started at `start` has exceeded the configured
    satisfaction wall budget. -/
private def budgetExceeded (o : SearchConfig) (start : Nat) : IO Bool :=
  match o.timeLimit with
  | some limit => return (← monoMsNow) - start > limit
  | none => return false

/-- The satisfaction route: one atomic certified slice. -/
def runSatisfyModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  let start ← monoMsNow
  -- Core (the default since N14) always runs the stats twin: `coreSolve` is
  -- the first component of `coreSolveFull`, so the counters cost nothing and
  -- `solveCertifiedCoreStats_fst` makes the verdict that of
  -- `solveCertifiedCore`.  On the kernel the no-stats route keeps the pre-K0
  -- scheduled entry (`solveCertified`); `--stats` uses the K0b scheduled
  -- DB/stats twin (`solveCertifiedStats`), the same propagation recursion.
  let (res, engine) ←
    if o.engine == .core then do
      let r := solveCertifiedCoreStats model o
      pure (r.1, if o.stats then coreRunStats r.2 else ({} : RunStats))
    else if o.stats then do
      let r := solveCertifiedStats model o
      pure (r.1, engineRunStats r.2)
    else
      pure (solveCertified model o, ({} : RunStats))
  match res with
  | .sat store =>
      let overBudget ← budgetExceeded o start
      if overBudget then
        if o.stats then emitStats { engine with complete := false }
        return 4
      else
        IO.println (emitCertifiedSolution model store)
        if o.stats then emitStats { engine with complete := true }
        return 0
  | .unsat =>
      let overBudget ← budgetExceeded o start
      if overBudget then
        if o.stats then emitStats { engine with complete := false }
        return 4
      else
        IO.println "=====UNSATISFIABLE====="
        if o.stats then emitStats { engine with complete := true }
        return 1
  | .unknown reason =>
      IO.eprintln s!"leanfzn: internal: {reason}"
      if o.stats then emitStats { engine with complete := false }
      return 2
  | .unsupported reason =>
      IO.eprintln s!"leanfzn: {reason}"
      if o.stats then emitStats { engine with complete := false }
      return 3

/-- F5's deterministic slice calibration: one nominal portfolio millisecond
is 1000 certified kernel steps.  This is a step budget, not a wall-clock
guarantee (adapter note §6.2). -/
def portfolioMsToFuel (ms : Nat) : Nat := ms * 1000

/-- Emit a completed restart/portfolio summary under the F5 claim discipline:
every printed incumbent is certified, only the final complete segment may
print `==========`/`=====UNSATISFIABLE=====`, and an incomplete run makes no
completeness claim. -/
private def emitPortfolioSummary (o : SearchConfig) (model : Model)
    (summary : PortfolioSummary) : IO UInt32 := do
  for t in summary.sols do
    emitOptimizationSolution model (summary.p.toStore t.1)
  -- `summary.seeds` is the final complete segment's trace, so `rounds` is
  -- the actually attempted probe segments plus the final segment's rounds;
  -- `restarts` is the number of probe segments actually run (the schedule
  -- stops early when a probe proves the bound infeasible).
  let rounds := summary.probes + summary.seeds.length
  if summary.complete then
    if summary.sols.isEmpty then
      IO.println "=====UNSATISFIABLE====="
      if o.stats then
        emitStats { rounds := rounds
                    restarts := summary.probes
                    seeds := some summary.seeds
                    complete := true }
      return 1
    else
      IO.println optimumMarker
      if o.stats then
        emitStats { rounds := rounds
                    incumbents := summary.sols.length
                    restarts := summary.probes
                    seeds := some summary.seeds
                    complete := true }
      return 0
  else
    IO.eprintln
      "leanfzn: optimization incomplete: the model is outside the certified gate"
    if o.stats then
      emitStats { rounds := rounds
                  incumbents := summary.sols.length
                  restarts := summary.probes
                  seeds := some summary.seeds
                  complete := false }
    return 3

/-- The F5 restart/portfolio route.  Both flags run a pure, completed driver;
the process prints only after the call returns, so an externally killed run
prints no claim (adapter note §6.1). -/
private def runPortfolioModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  let result : Except String PortfolioSummary ←
    match o.portfolio with
    | some value =>
        match parsePortfolio value with
        | .error reason => pure (.error reason)
        | .ok spec =>
            let entries := spec.probes.map
              (fun (c, ms) =>
                ({ config := c, budgets := [portfolioMsToFuel ms] } : BudgetSegment))
            pure (optimizePortfolioConfig entries spec.final model)
    | none => pure (optimizeRestartConfigOf o model)
  match result with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      if o.stats then emitStats { complete := false }
      return 3
  | .ok summary => emitPortfolioSummary o model summary

/-- The F4 bisection route.  `optimizeBisectStream` emits each SAT-probe
incumbent immediately, before the next probe, so an externally killed process
still prints the certified incumbents it found; the process prints no marker
until the run returns complete.  A missing root-bound fallback is the complete
linear route and is emitted when that run returns. -/
private def runBisectModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  match ← optimizeBisectStream o model (emitOptimizationSolution model) with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      if o.stats then emitStats { complete := false }
      return 3
  | .ok summary =>
      if summary.run.complete then
        if summary.run.sols.isEmpty then
          IO.println "=====UNSATISFIABLE====="
          if o.stats then
            emitStats { rounds := summary.probes, complete := true }
          return 1
        else
          IO.println optimumMarker
          if o.stats then
            emitStats
              { rounds := summary.probes
                incumbents := summary.run.sols.length
                complete := true }
          return 0
      else
        IO.eprintln
          "leanfzn: optimization incomplete: the model is outside the certified gate"
        if o.stats then
          emitStats
            { rounds := summary.probes
              incumbents := summary.run.sols.length
              complete := false }
        return 3

/-- The F6.1 dive route.  It compiles once, runs the deterministic
    witness-checked dive on the configured presentation, prints a candidate
    only after `checkedObjective` accepted it (`diveSlice_sound`), and then
    runs the same certified linear B&B with the checked value as the strict
    initial bound.  The B&B alone prints `==========`/`=====UNSATISFIABLE=====`:
    its last solution is optimal by `optLoopWith_optimal` (T2), and a
    completed empty B&B is optimal at the primal witness by
    `primalBound_optimal` (T4).  A skipped dive is reported on stderr; the
    route never falls back silently. -/
private def runDiveModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  match compileModelOpt model with
  | .error reason =>
      IO.eprintln s!"leanfzn: {reason}"
      if o.stats then emitStats { complete := false }
      return 3
  | .ok (p, spec) =>
      let S := lcgSolver o
      if S.gate p then
        let gateOk := lcgRouteGateMixed (lcgConfigProblem p o)
        let hit := diveSlice model p o spec (primalMsToFuel o.primalTime)
        if !gateOk then
          IO.eprintln
            "leanfzn: primal heuristic skipped: model outside the mixed route gate"
        if let some h := hit then
          IO.println h.text
          (← IO.getStdout).flush
        let result ←
          optimizeStreamLoopWith S p spec (fun a => p.toStore a)
            (emitOptimizationSolution model) none (hit.map (fun h => h.value))
        let run := result.1
        let stats : RunStats :=
          { rounds := run.sols.length + 1
            incumbents := run.sols.length
            complete := run.complete
            primalSlices := if gateOk then 1 else 0
            primalCandidates := if hit.isSome then 1 else 0
            primalSkipped := !gateOk }
        if run.complete then
          if run.sols.isEmpty then
            if hit.isSome then
              IO.println optimumMarker
              if o.stats then emitStats stats
              return 0
            else
              IO.println "=====UNSATISFIABLE====="
              if o.stats then emitStats stats
              return 1
          else
            IO.println optimumMarker
            if o.stats then emitStats stats
            return 0
        else
          IO.eprintln
            "leanfzn: optimization incomplete: the model is outside the certified gate"
          if o.stats then emitStats stats
          return 3
      else
        IO.eprintln
          "leanfzn: optimization incomplete: the model is outside the certified gate"
        if o.stats then emitStats { complete := false }
        return 3

/-- The optimization route. Without `--time-limit` this is exactly the
    pre-F1 `optimizeStream` path. With a limit it compiles first (so an
    unsupported model is still an error), checks the gate, and then runs the
    timed recursion. -/
def runOptimizeModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.primal != .none then
    -- F6.1 opens exactly this combination; every other primal driver is
    -- rejected here as well as in `SearchConfig.checkImplemented`, so a
    -- programmatic caller cannot silently ignore the option.
    if o.primal == .dive && o.opt == .linear && o.timeLimit.isNone &&
        o.portfolio.isNone && o.restart == .none then
      return (← runDiveModel o model)
    else
      IO.eprintln
        "leanfzn: '--primal=dive' supports '--opt=linear' only and is incompatible with '--time-limit', '--restart', '--portfolio', '--opt=seeded', '--opt=bisect' and '--primal=lns'"
      if o.stats then emitStats { complete := false }
      return 2
  if o.opt == .bisect then
    if o.portfolio.isSome || o.restart != .none || o.timeLimit.isSome then
      IO.eprintln
        "leanfzn: '--opt=bisect' is incompatible with '--time-limit', '--restart' and '--portfolio'"
      if o.stats then emitStats { complete := false }
      return 2
    return (← runBisectModel o model)
  if o.usesF5Driver then
    return (← runPortfolioModel o model)
  match o.timeLimit with
  | none =>
      if o.opt == .seeded then
        -- `--engine=core` runs the stateful Core branch and bound that
        -- carries the learned clause database across bound rounds
        -- (`optimizeStreamCoreSeed`); the kernel route keeps its seeded
        -- driver.  Both produce the same per-round seed trace shape.
        let seedRun : Except String (OptRun × List Nat) ←
          if o.engine == .core then
            pure ((← optimizeStreamCoreSeed o model
              (emitOptimizationSolution model)).map (fun s => (s.run, s.seeds)))
          else
            pure ((← optimizeStreamSeedConfig o model
              (emitOptimizationSolution model)).map (fun s => (s.run, s.seeds)))
        match seedRun with
        | .error reason =>
            IO.eprintln s!"leanfzn: {reason}"
            if o.stats then emitStats { complete := false }
            return 3
        | .ok (run, seeds) =>
            if run.complete then
              if run.sols.isEmpty then
                IO.println "=====UNSATISFIABLE====="
                if o.stats then
                  emitStats { rounds := seeds.length
                              seeds := some seeds
                              complete := true }
                return 1
              else
                IO.println optimumMarker
                if o.stats then
                  emitStats
                    { rounds := seeds.length
                      incumbents := run.sols.length
                      seeds := some seeds
                      complete := true }
                return 0
            else
              IO.eprintln
                "leanfzn: optimization incomplete: the model is outside the certified gate"
              if o.stats then
                emitStats
                  { rounds := seeds.length
                    incumbents := run.sols.length
                    seeds := some seeds
                    complete := false }
              return 3
      else
        match ← optimizeStream o.certSolver model (emitOptimizationSolution model) with
        | .error reason =>
            IO.eprintln s!"leanfzn: {reason}"
            if o.stats then emitStats { complete := false }
            return 3
        | .ok summary =>
            let run := summary.run
            if run.complete then
              if run.sols.isEmpty then
                IO.println "=====UNSATISFIABLE====="
                if o.stats then
                  emitStats { rounds := run.sols.length + 1, complete := true }
                return 1
              else
                IO.println optimumMarker
                if o.stats then
                  emitStats
                    { rounds := run.sols.length + 1
                      incumbents := run.sols.length
                      complete := true }
                return 0
            else
              IO.eprintln
                "leanfzn: optimization incomplete: the model is outside the certified gate"
              if o.stats then
                emitStats
                  { rounds := run.sols.length + 1
                    incumbents := run.sols.length
                    complete := false }
              return 3
  | some limit =>
      let start ← monoMsNow
      let deadline := start + limit
      match compileModelOpt model with
      | .error reason =>
          IO.eprintln s!"leanfzn: {reason}"
          if o.stats then emitStats { complete := false }
          return 3
      | .ok (p, spec) =>
          let S := o.certSolver
          if S.gate p then
            let result ←
              optimizeStreamTimed S p spec (fun a => p.toStore a)
                (emitOptimizationSolution model) (some deadline) none
            if result.run.complete then
              if result.run.sols.isEmpty then
                IO.println "=====UNSATISFIABLE====="
                if o.stats then
                  emitStats { rounds := result.rounds, complete := true }
                return 1
              else
                IO.println optimumMarker
                if o.stats then
                  emitStats
                    { rounds := result.rounds
                      incumbents := result.run.sols.length
                      complete := true }
                return 0
            else if result.stopped then
              -- budget exhausted between rounds: keep the printed certified
              -- incumbents, make no completeness claim, exit 0 (PLAN §2.2)
              if o.stats then
                emitStats
                  { rounds := result.rounds
                    incumbents := result.run.sols.length
                    complete := false }
              return 0
            else
              IO.eprintln
                "leanfzn: optimization incomplete: the model is outside the certified gate"
              if o.stats then
                emitStats
                  { rounds := result.rounds
                    incumbents := result.run.sols.length
                    complete := false }
              return 3
          else
            IO.eprintln
              "leanfzn: optimization incomplete: the model is outside the certified gate"
            if o.stats then emitStats { complete := false }
            return 3

/-- The strategy-driver entry: check well-formedness, dispatch, and report. -/
def runModel (o : SearchConfig) (model : Model) : IO UInt32 := do
  if o.var == .annot && o.actBump then
    IO.eprintln
      "leanfzn: warning: --var=annot disables --heur-act conflict bumping (the exact-halving rescale would destroy the annotation group order)"
  if LeanFzn.Checker.wellFormedFastB model then
    match model.solve with
    | .minimize _ _ | .maximize _ _ =>
        runOptimizeModel o model
    | .satisfy _ =>
        if o.primal != .none then do
          IO.eprintln
            "leanfzn: '--primal' is an optimization driver; this model has no objective"
          return 2
        else if o.usesF5Driver || o.opt == .bisect then do
          IO.eprintln
            "leanfzn: '--restart', '--portfolio' and '--opt=bisect' are optimization drivers; this model has no objective"
          return 2
        else
          runSatisfyModel o model
  else
    IO.eprintln "leanfzn: model is not well-formed"
    return 2

end LeanFzn.Integration
