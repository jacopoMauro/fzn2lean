/-
File: Tests/E1/DbScanCounts.lean

Purpose (PLAN tasks P1b and P3, TEST-ONLY, UNCERTIFIED): native, compiled
measurement of the learned-database scan chain
(`scanDatabase` -> `clauseRemaining` -> `literalImpossible`) on the wired
public route, plus the deep per-phase profile of the challenge instances that
still time out (`proteindesign12`).

Modes:

  --battery            the 43-instance harness battery (`LcgHarness.battery`):
                       native best-window timing of
                         base  = `LcgPhaseKernel.solve` (the certified kernel)
                         sched = `lcgRunSched` (the wired scheduled route)
                       per instance, with verdict equality, plus the DB-scan
                       counts of the real run (visited clauses, unit/skip/
                       conflict classification) and the number of steps.
  --files FILE...      per file: front-end phases (parse / compile / gate),
                       then a fuel-bounded walk of the WIRED dispatcher
                       (`phaseNextSched`) with per-phase timings of the scan
                       chain: the database scan (`scanDatabase`) in isolation,
                       the scheduled propagator scan, the whole event prompt
                       (`nextPruningEventSched`) and the whole step
                       (`phaseNextSched`); plus DB sizes and scan counts.

The timings are in-process wall clocks (`IO.monoNanosNow`) around calls to the
REAL certified functions; the counted quantities are obtainable by re-running
the real scans on the real configurations (identical inputs, so identical
work modulo the instrumentation call itself).

Run compiled:  .lake/build/bin/tests_dbscan --battery
               .lake/build/bin/tests_dbscan --files FILE...
-/
import Tests.UIP.LcgHarnessBattery
import LeanFzn.Legacy.Integration.Lcg
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepSched
open LeanFzn.Solver.Propagation LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.Core LeanFzn

namespace Tests.E1.DbScan

/-! ## 1. Counters -/

structure DbStat where
  steps : Nat := 0
  activeSteps : Nat := 0
  propagates : Nat := 0
  decides : Nat := 0
  jumps : Nat := 0
  conflicts : Nat := 0
  consumes : Nat := 0
  visited : Nat := 0
  cConflict : Nat := 0
  cUnit : Nat := 0
  cSkip : Nat := 0
  litTotal : Nat := 0
  dbTotal : Nat := 0        -- Σ db size over active steps
  maxDb : Nat := 0
  slotsTotal : Nat := 0     -- Σ `Frame.domains` length over active steps
  qRuns : Nat := 0          -- E1 queue twin: propagator runs the early-exit scan performs
  qSkips : Nat := 0         -- E1 queue twin: dirty units reused via the quiet certificate
  qReplays : Nat := 0       -- E1 queue twin: clean units replayed from their records
  qSteps : Nat := 0         -- E1 queue twin: steps whose queued prompt scanned
  deriving Repr

def DbStat.add (a b : DbStat) : DbStat :=
  { steps := a.steps + b.steps, activeSteps := a.activeSteps + b.activeSteps,
    propagates := a.propagates + b.propagates, decides := a.decides + b.decides,
    jumps := a.jumps + b.jumps, conflicts := a.conflicts + b.conflicts,
    consumes := a.consumes + b.consumes, visited := a.visited + b.visited,
    cConflict := a.cConflict + b.cConflict, cUnit := a.cUnit + b.cUnit,
    cSkip := a.cSkip + b.cSkip, litTotal := a.litTotal + b.litTotal,
    dbTotal := a.dbTotal + b.dbTotal, maxDb := max a.maxDb b.maxDb,
    slotsTotal := a.slotsTotal + b.slotsTotal,
    qRuns := a.qRuns + b.qRuns, qSkips := a.qSkips + b.qSkips,
    qReplays := a.qReplays + b.qReplays, qSteps := a.qSteps + b.qSteps }

/-- Classify + count every clause of the db the way `scanDatabase` does (the
counts are of the REAL work; the recursion short-circuits only at the same
points as the real scan, so `visited` equals the real visited count when the
event is stable pre-checked — here we count ALL clauses of the db, which is an
upper bound when the real scan exits early on an event). -/
def visitDb (f : BranchFrame) : List Clause → DbStat → DbStat
  | [], st => st
  | c :: rest, st =>
    let rem := clauseRemaining f c
    let st := { st with visited := st.visited + 1, litTotal := st.litTotal + c.length }
    let st :=
      match rem with
      | [] => { st with cConflict := st.cConflict + 1 }
      | [_] => { st with cUnit := st.cUnit + 1 }
      | _ => { st with cSkip := st.cSkip + 1 }
    visitDb f rest st

/-! ## 2. The bounded walk of the WIRED dispatcher, with timings -/

structure Samples where
  dbScan : List Nat := []
  propScan : List Nat := []
  prompt : List Nat := []
  step : List Nat := []
  jumpPerf : List Nat := []
  deciding : List Nat := []

/-- The per-unit counting mirror of the certified early-exit scan: walks the
real propagator list with the real queue state and counts (runs, certificate
skips, record replays) up to the reference early exit. TEST-ONLY. -/
def queueScanCount (f : BranchFrame) (i : Nat) :
    List Propagator → List (Option (BranchFrame × PropagationResult)) → List Nat →
      Nat × Nat × Nat
  | [], _, _ => (0, 0, 0)
  | p :: ps, s :: ss, pend =>
      let dirty := pend.contains i
      let cert := match s with
        | some (fr, _) => quietB p fr f
        | none => false
      let runIt := dirty && !cert
      let skipIt := dirty && cert
      let replays := !dirty
      let stop := match queueUnitResult f i p s pend with
        | .stable => false
        | .conflict _ => true
        | .implied l _ => productive l f
      if stop then
        (if runIt then 1 else 0, if skipIt then 1 else 0, if replays then 1 else 0)
      else
        let cnt := queueScanCount f (i + 1) ps ss pend
        (cnt.1 + (if runIt then 1 else 0), cnt.2.1 + (if skipIt then 1 else 0),
          cnt.2.2 + (if replays then 1 else 0))
  | _, _, _ => (0, 0, 0)

/-- E1 queue twin for one step (TEST-ONLY): thread an INDEPENDENT queue whose
sync frame advances at every DB-stable viewed active step and count the
certified early-exit scan's runs, certificate skips and record replays. This
measures the queue's run efficiency on every eligible step, independent of
which prompt the runtime policy picked. -/
def queueTwinStep {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (q : WorkQueue) (qframe : BranchFrame) :
    Nat × Nat × Nat × Nat × WorkQueue × BranchFrame :=
  if cfg.conflict.isNone && cfg.status == .active then
    match scanDatabaseFast cfg.original cfg.branch.frame cfg.branch.learned with
    | .stable =>
        if frameViewedB cfg.branch.frame then
          let q1 := q.enqueueEvents cfg.props qframe cfg.branch.frame
          let c := queueScanCount cfg.branch.frame 0 cfg.props q1.seen q1.pending
          let q2 := (q1.scanQueue cfg.props cfg.branch.frame).2
          (c.1, c.2.1, c.2.2, 1, q2, cfg.branch.frame)
        else (0, 0, 0, 0, q, qframe)
    | _ => (0, 0, 0, 0, q, qframe)
  else (0, 0, 0, 0, q, qframe)

/-- Pure bounded walk (counts only, no clocks) — the battery mode. The E1
queue twin threads the certified queued prompt's sync+drain on the side and
counts the propagator runs it WOULD perform at each active step (the real
route is the watch-stamp scan; the twin needs no clock and no extra scan
beyond the certified DB probe, `scanDatabaseFast`). -/
partial def walkPure {leaf : Assignment → Bool} (fuel : Nat) (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (twinQ : WorkQueue) (twinFrame : BranchFrame)
    (acc : DbStat) (s : Samples) :
    DbStat × Samples × Option (DriverResult leaf) :=
  match fuel with
  | 0 => (acc, s, none)
  | fuel + 1 =>
    let pr := phaseNextSched cfg sched
    let acc := { acc with steps := acc.steps + 1 }
    let qt := queueTwinStep cfg twinQ twinFrame
    let acc := { acc with qRuns := acc.qRuns + qt.1, qSkips := acc.qSkips + qt.2.1, qReplays := acc.qReplays + qt.2.2.1, qSteps := acc.qSteps + qt.2.2.2.1 }
    let twinQ := qt.2.2.2.2.1
    let twinFrame := qt.2.2.2.2.2
    let acc :=
      match pr.1 with
      | .propagate _ => { acc with propagates := acc.propagates + 1 }
      | .decide _ _ => { acc with decides := acc.decides + 1 }
      | .learnBackjumpAssert _ _ _ => { acc with jumps := acc.jumps + 1 }
      | .analyzeConflict _ _ => { acc with conflicts := acc.conflicts + 1 }
      | .chronologicalFallback _ => { acc with consumes := acc.consumes + 1 }
      | _ => acc
    let acc :=
      match cfg.conflict, cfg.status with
      | none, .active =>
        let f := cfg.branch.frame
        let db := cfg.branch.learned
        visitDb f db { acc with activeSteps := acc.activeSteps + 1, dbTotal := acc.dbTotal + db.length, maxDb := max acc.maxDb db.length, slotsTotal := acc.slotsTotal + (Frame.domains f).length }
      | _, _ => acc
    match pr.1 with
    | .sat _ => (acc, s, some (.sat []))
    | .unsat => (acc, s, some .unsat)
    | _ =>
      match pr.1.successor with
      | some n => walkPure fuel n pr.2 twinQ twinFrame acc s
      | none => (acc, s, none)

/-- The timed sub-phases of one ACTIVE step: the database scan chain
(`scanDatabase`), the scheduled propagator scan, and the whole event prompt
(`nextPruningEventSched`) are called on the REAL (frame, db) of the step and
clocked; the step itself is clocked by the caller. The db is visited for the
counts. -/
def sampleActive {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (acc : DbStat) (s : Samples) : IO (DbStat × Samples) := do
  let f := cfg.branch.frame
  let db := cfg.branch.learned
  let tdb0 ← IO.monoNanosNow
  let _ := scanDatabase cfg.original f db
  let tdb1 ← IO.monoNanosNow
  let s : Samples := { s with dbScan := (tdb1 - tdb0) :: s.dbScan }
  let tps0 ← IO.monoNanosNow
  let _ := scanPropagatorsSched f sched cfg.props
  let tps1 ← IO.monoNanosNow
  let s : Samples := { s with propScan := (tps1 - tps0) :: s.propScan }
  let tpr0 ← IO.monoNanosNow
  let _ := nextPruningEventSched cfg.original cfg.props sched f db
  let tpr1 ← IO.monoNanosNow
  let s : Samples := { s with prompt := (tpr1 - tpr0) :: s.prompt }
  let acc := visitDb f db { acc with activeSteps := acc.activeSteps + 1, dbTotal := acc.dbTotal + db.length, maxDb := max acc.maxDb db.length, slotsTotal := acc.slotsTotal + (Frame.domains f).length }
  return (acc, s)

/-- Timed bounded walk over the REAL scheduled dispatcher `phaseNextSched`. -/
partial def walkTimed {leaf : Assignment → Bool} (fuel : Nat) (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (acc : DbStat) (s : Samples) :
    IO (DbStat × Samples × Option (DriverResult leaf)) := do
  match fuel with
  | 0 => return (acc, s, none)
  | fuel + 1 =>
    let tstep0 ← IO.monoNanosNow
    let pr := phaseNextSched cfg sched
    let tstep1 ← IO.monoNanosNow
    let s : Samples := { s with step := (tstep1 - tstep0) :: s.step }
    let acc := { acc with steps := acc.steps + 1 }
    let acc :=
      match pr.1 with
      | .propagate _ => { acc with propagates := acc.propagates + 1 }
      | .decide _ _ => { acc with decides := acc.decides + 1 }
      | .learnBackjumpAssert _ _ _ => { acc with jumps := acc.jumps + 1 }
      | .analyzeConflict _ _ => { acc with conflicts := acc.conflicts + 1 }
      | .chronologicalFallback _ => { acc with consumes := acc.consumes + 1 }
      | _ => acc
    let (acc, s) ←
      if cfg.conflict.isNone && cfg.status == .active then
        sampleActive cfg sched acc s
      else
        pure (acc, s)
    match pr.1 with
    | .sat _ => return (acc, s, some (.sat []))
    | .unsat => return (acc, s, some .unsat)
    | _ =>
      match pr.1.successor with
      | some n => walkTimed fuel n pr.2 acc s
      | none => return (acc, s, none)

def median (xs : List Nat) : Nat :=
  let sorted := xs.mergeSort (· ≤ ·)
  sorted.getD (sorted.length / 2) 0

def total (xs : List Nat) : Nat := xs.foldl (· + ·) 0

def us (ns : Nat) : String := s!"{ns / 1000}.{(ns / 100) % 10}"

/-! ## 3. Mode: `--files` (deep profile of one instance) -/

/-- Flushed print (piped stdout is block-buffered; a killed run must not lose
the phases already measured). -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def profileFile (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  let t0 ← IO.monoNanosNow
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let t1 ← IO.monoNanosNow
    say s!"STAGE {path} parseMs={(t1-t0)/1000000}"
    let wf := LeanFzn.Checker.wellFormedFastB m
    let t1b ← IO.monoNanosNow
    say s!"STAGE {path} wfMs={(t1b-t1)/1000000} wf={wf} constraints={m.constraints.length}"
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let t2 ← IO.monoNanosNow
      say s!"STAGE {path} compileMs={(t2-t1b)/1000000} domains={p.domains.length} dcs={p.constraints.length}"
      let sd0 ← IO.monoNanosNow
      let seeds0 := LeanFzn.Compiler.seedClauses p.constraints
      let sd1 ← IO.monoNanosNow
      say s!"STAGE {path} seedClausesMs={(sd1-sd0)/1000000} seeds={seeds0.length}"
      let lcgp := LeanFzn.Integration.toLCG p
      let sd2 ← IO.monoNanosNow
      let domN := lcgp.domains.length
      let domSum := lcgp.domains.foldl (fun a d => a + d.length) 0
      let domMax := lcgp.domains.foldl (fun a d => max a d.length) 0
      say s!"STAGE {path} toLCGMs={(sd2-sd1)/1000000} domN={domN} domSum={domSum} domMax={domMax}"
      let ta ← IO.monoNanosNow
      let gOk := LeanFzn.Solver.Propagation.gateOk lcgp
      let tb ← IO.monoNanosNow
      let dpOk := LeanFzn.Solver.Propagation.domPruningOkB lcgp
      let tc ← IO.monoNanosNow
      let mkOk := LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB lcgp
      let td ← IO.monoNanosNow
      let routed := gOk && dpOk && mkOk
      let te ← IO.monoNanosNow
      say s!"STAGE {path} gateOkMs={(tb-ta)/1000000} domPruningOkMs={(tc-tb)/1000000} mixedKitFastMs={(td-tc)/1000000} (route={routed}; gate = gateOk&&domPruningOkB&&mixedKitGateFastB by definition (P3b fast twin of mixedKitGateB, equal by mixedKitGateFastB_eq)) ok={gOk}/{dpOk}/{mkOk}"
      let t3 ← IO.monoNanosNow
      let props := LeanFzn.Integration.lcgProps p
      let tf ← IO.monoNanosNow
      let seeds := LeanFzn.Compiler.seedClauses lcgp.constraints
      let t3b ← IO.monoNanosNow
      say s!"STAGE {path} gateMs={(t3-t2)/1000000} propsMs={(tf-t3)/1000000} seedsMs={(t3b-tf)/1000000} props={props.length} seeds={seeds.length}"
      let leaf := LeanFzn.Integration.lcgLeaf p
      let cfg : SchedulerConfig leaf := SchedulerConfig.init lcgp.domains seeds props
      let sched := PropScheduler.init props
      let t4 ← IO.monoNanosNow
      let (st, s, r) ← walkTimed fuel cfg sched {} {}
      let t5 ← IO.monoNanosNow
      let v := match r with | some (.sat _) => "sat" | some .unsat => "unsat" | none => "fuel"
      let steps := st.steps
      let per (x : Nat) : String := if steps == 0 then "-" else s!"{x / steps}"
      say s!"FILE {path} wf={wf} route={if routed then "lcg" else "chrono"} gateOk={gOk} domPruningOkB={dpOk} mixedKitGateFastB={mkOk} slots={lcgp.domains.length} constraints={lcgp.constraints.length} props={props.length}"
      say s!"PHASES {path} parseMs={(t1-t0)/1000000} wfMs={(t1b-t1)/1000000} compileMs={(t2-t1b)/1000000} gateMs={(t3-t2)/1000000} propsMs={(t3b-t3)/1000000} walkMs={(t5-t4)/1000000} verdict={v} fuel={fuel}"
      say s!"WALK {path} steps={steps} active={st.activeSteps} propagates={st.propagates} decides={st.decides} jumps={st.jumps} conflicts={st.conflicts} consumes={st.consumes} dbTotal={st.dbTotal} maxDb={st.maxDb} slotsTotal={st.slotsTotal} visited={st.visited} cConflict={st.cConflict} cUnit={st.cUnit} cSkip={st.cSkip} litTotal={st.litTotal}"
      say s!"PERSTEP {path} dbClauses={per st.dbTotal} visited={per st.visited} unit={per st.cUnit} skip={per st.cSkip} conflict={per st.cConflict} avgDb={per st.maxDb} avgSlots={per st.slotsTotal} avgLits={per st.visited}"
      say s!"TIME {path} nsPerStep={per (total s.step)} dbScanPerStep={per (total s.dbScan)} propScanPerStep={per (total s.propScan)} promptPerStep={per (total s.prompt)} dbMedNs={median s.dbScan} propMedNs={median s.propScan} stepMedNs={median s.step} promptMedNs={median s.prompt}"
      let pct (x y : Nat) : String := if y == 0 then "-" else s!"{100 * x / y}"
      say s!"SHARE {path} dbScan={pct (total s.dbScan) (total s.step)}% propScan={pct (total s.propScan) (total s.step)}% prompt={pct (total s.prompt) (total s.step)}% (other = jump/decide/analyze arms + gates)"

/-! ## 4. Mode: `--battery` -/

def verdictTag {leaf : Assignment → Bool} : DriverResult leaf → Nat
  | .sat _ => 1
  | .unsat => 2

/-- Best (minimum) timed window in ns over `reps` runs, with the result. -/
def bestNs {α : Type} (reps : Nat) (act : Unit → α) (init : α) : IO (Nat × α) := do
  let mut best := 0
  let mut res := init
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure act
    let t1 ← IO.monoNanosNow
    res := r
    let ns := t1 - t0
    if best == 0 || ns < best then best := ns
  return (best, res)

structure BatTotal where
  instances : Nat := 0
  baseNs : Nat := 0
  schedNs : Nat := 0
  noWatchNs : Nat := 0
  noWatchDisagree : Nat := 0
  steps : Nat := 0
  visited : Nat := 0
  cUnit : Nat := 0
  cSkip : Nat := 0
  cConflict : Nat := 0
  litTotal : Nat := 0
  disagree : Nat := 0
  sat : Nat := 0
  unsat : Nat := 0
  qRuns : Nat := 0
  qSkips : Nat := 0
  qReplays : Nat := 0
  qSteps : Nat := 0
  qFullRuns : Nat := 0      -- Σ over queue-twin steps of props.length (the full scan's runs)
  qPropagates : Nat := 0
  watched : Nat := 0        -- Σ over instances of props with a declared footprint
  props : Nat := 0          -- Σ over instances of props.length
  deriving Repr

/-- The same propagator list with every declared watch footprint stripped:
the scheduled scan then refuses every table entry (the pre-watch-footprint
behaviour of the unwatched families), giving a same-binary ablation of the
watch-footprint extension. -/
def stripWatches (props : List Propagator) : List Propagator :=
  props.map fun p => { p with watches := [] }

/-- Stripped lists are vacuously locally sound (no member declares a footprint). -/
theorem stripWatches_local (props : List Propagator) : PropLocal (stripWatches props) := by
  intro p hp hne
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  simp at hne

/-- The scheduled entry over the stripped (no-footprint) propagator list. -/
def lcgRunSchedNoWatch (p : LeanFzn.Compiler.CompiledProblem
    LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint)
    (hroute : lcgRouteGateMixed p = true) :
    DriverResult (LeanFzn.Integration.lcgLeaf p) :=
  let props := stripWatches (LeanFzn.Integration.lcgProps p)
  solve_sched p.domains (LeanFzn.Compiler.seedClauses p.constraints) props
    (LeanFzn.Integration.lcgSeedEntailed p) (PropScheduler.init props)
    (stripWatches_local (LeanFzn.Integration.lcgProps p))
    (PropSchedulerOK.init props) (LcgHarness.frameGate_of_routeGate hroute)

def runBatteryOne (reps fuel : Nat) (name src : String) (t : BatTotal) : IO BatTotal := do
  match LcgHarness.ofSource name src with
  | .error e => IO.eprintln s!"{name}: {e}"; return t
  | .ok inst =>
    match inst.compiled with
    | none => return t
    | some p =>
      if hroute : lcgRouteGateMixed p = true then
        let leaf := lcgLeaf p
        let (baseNs, r0) ← bestNs reps
          (fun _ => LcgPhaseKernel.solve p.domains (seedClauses p.constraints) (lcgProps p)
            (lcgSeedEntailed p) (LcgHarness.frameGate_of_routeGate hroute))
          (.sat [] : DriverResult leaf)
        let (schedNs, r1) ← bestNs reps (fun _ => lcgRunSched p (LcgHarness.frameGate_of_routeGate hroute)) (.sat [] : DriverResult leaf)
        let (noWatchNs, r2) ← bestNs reps
          (fun _ => lcgRunSchedNoWatch p hroute) (.sat [] : DriverResult leaf)
        let dis2 := if verdictTag r1 == verdictTag r2 then 0 else 1
        if dis2 == 1 then
          IO.eprintln s!"{name}: WATCH-ABLATION VERDICT MISMATCH sched={verdictTag r1} noWatch={verdictTag r2}"
        let cfg : SchedulerConfig leaf :=
          SchedulerConfig.init p.domains (seedClauses p.constraints) (lcgProps p)
        let (st, _, _) ← IO.lazyPure (fun _ => walkPure fuel cfg (PropScheduler.init (lcgProps p))
          (PropScheduler.init (lcgProps p)).work (PropScheduler.init (lcgProps p)).qframe {} {})
        let dis := if verdictTag r0 == verdictTag r1 then 0 else 1
        if dis == 1 then
          IO.eprintln s!"{name}: VERDICT MISMATCH base={verdictTag r0} sched={verdictTag r1}"
        let wc := (lcgProps p).foldl (fun a q => if q.watches.isEmpty then a else a + 1) 0
        IO.println s!"{name} base={baseNs / 1000}us sched={schedNs / 1000}us watched={wc}/{(lcgProps p).length} steps={st.steps} \
visited={st.visited} unit={st.cUnit} skip={st.cSkip} conflict={st.cConflict} maxDb={st.maxDb}"
        return { t with instances := t.instances + 1, baseNs := t.baseNs + baseNs, schedNs := t.schedNs + schedNs, noWatchNs := t.noWatchNs + noWatchNs, noWatchDisagree := t.noWatchDisagree + dis2, steps := t.steps + st.steps, visited := t.visited + st.visited, cUnit := t.cUnit + st.cUnit, cSkip := t.cSkip + st.cSkip, cConflict := t.cConflict + st.cConflict, litTotal := t.litTotal + st.litTotal, disagree := t.disagree + dis, sat := t.sat + (if verdictTag r1 == 1 then 1 else 0), unsat := t.unsat + (if verdictTag r1 == 2 then 1 else 0), qRuns := t.qRuns + st.qRuns, qSkips := t.qSkips + st.qSkips, qReplays := t.qReplays + st.qReplays, qSteps := t.qSteps + st.qSteps, watched := t.watched + wc, props := t.props + (lcgProps p).length, qFullRuns := t.qFullRuns + st.qSteps * (lcgProps p).length, qPropagates := t.qPropagates + st.propagates }
      else
        IO.println s!"{name}: NOT ROUTED (gate off)"
        return t

def run (args : List String) : IO UInt32 := do
  match args with
  | "--files" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 20000
    for f in files do
      profileFile fuel f
    return 0
  | _ =>
    let (reps, fuel) :=
      match args with
      | "--battery" :: "--reps" :: r :: "--fuel" :: fl :: _ =>
          (r.toNat?.getD 3, fl.toNat?.getD 400000)
      | _ => (3, 400000)
    let t0 ← IO.monoMsNow
    let mut t : BatTotal := {}
    for (name, src) in LcgHarness.battery do
      t ← runBatteryOne reps fuel name src t
    let t1 ← IO.monoMsNow
    IO.println s!"\nBATTERY instances={t.instances} sat={t.sat} unsat={t.unsat} \
disagreeVerdicts={t.disagree} wallMs={t1 - t0}"
    IO.println s!"BATTERY baseMs={t.baseNs / 1000000} schedMs={t.schedNs / 1000000} \
ratio={(t.baseNs * 100) / (t.schedNs + 1)}% (base/sched, >100 = sched faster, reps={reps})"
    IO.println s!"BATTERY noWatchMs={t.noWatchNs / 1000000} \
watchGain={(t.noWatchNs * 100) / (t.schedNs + 1)}% (noWatch/sched, >100 = watches faster) \
noWatchVerdictDisagreements={t.noWatchDisagree}"
    IO.println s!"BATTERY steps={t.steps} visited={t.visited} unit={t.cUnit} skip={t.cSkip} \
conflict={t.cConflict} litTotal={t.litTotal}"
    IO.println s!"WATCHRATIO watched={t.watched}/{t.props}"
    IO.println s!"E1QUEUE (twin, test-only) qRuns={t.qRuns} qSkips={t.qSkips} qReplays={t.qReplays} \
qSteps={t.qSteps} fullScanRunsAtSameSteps={t.qFullRuns} productiveDeductions={t.qPropagates} \
qRunsPerDeduction={if t.qPropagates == 0 then 0 else t.qRuns / t.qPropagates} \
(compare with the stamp twin's schedVisits in Tests/E1/SchedCounts.lean)"
    return 0

end Tests.E1.DbScan

def main (args : List String) : IO UInt32 := Tests.E1.DbScan.run args
