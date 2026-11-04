/-
File: Tests/E1/HeurTiming.lean

Purpose (PLAN task B0, TEST-ONLY, UNCERTIFIED): strict phase attribution of the
PUBLIC heuristic LCG route on one input file. The existing `tests_dbscan
--files` timings use `let _ := expr` inside `do`, which the compiler may
dead-code-eliminate; this runner wraps every timed expression in `IO.lazyPure`
so the work is forced inside the clock window.

Measured per file:

  heurMs          `LcgHeur.heurDomains` (the activity presentation of the whole
                  box, exactly what the public route feeds `lcgRunHeur`);
  heurPartsMs     `dcConsts` (constraint constant list) and the summed
                  `pinHits` over one sampled domain's values, to separate the
                  two activity components;
  then a bounded walk of the WIRED dispatcher on the HEURISTIC box:
    frameMs       `Frame.domains f` (the projection, rebuilt per step)
    viewedMs      `frameViewedB f`
    massMs        `Frame.mass f`
    dbScanMs      `scanDatabaseFast cfg.original f db`
    propScanMs    `scanPropagatorsSched f sched cfg.props`
    propRunMs     summed `p.run (frameState f)` over `cfg.props`
    promptMs      `nextPruningEventSched cfg.original cfg.props sched f db`
    stepMs        `phaseNextSched cfg sched` (the whole step)

Run compiled:  .lake/build/bin/tests_heur_timing FILE FUEL SAMPLES
-/
import LeanFzn.Legacy.Integration.LcgHeur
import LeanFzn.Solver.Propagation.CompactDomain
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch
import LeanFzn.Legacy.Solver.Propagation.VersionWatch
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepSched
import LeanFzn.Legacy.Solver.Propagation.EventScan
import LeanFzn.Checker.Check
import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Objective
import LeanFzn.Legacy.Integration.LcgOptimize
import Tests.UIP.LcgHarnessBattery
open LeanFzn.Solver.Propagation LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.Core LeanFzn

namespace Tests.E1.HeurTiming

/-- Human-readable constructor name of a compiled constraint family. -/
def dcName : LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint → String
  | .eqSlot .. => "eqSlot"
  | .neSlot .. => "neSlot"
  | .leSlot .. => "leSlot"
  | .constEq .. => "constEq"
  | .plusSlot .. => "plusSlot"
  | .leConstHi .. => "leConstHi"
  | .leConstLo .. => "leConstLo"
  | .allDiff .. => "allDiff"
  | .timesSlot .. => "timesSlot"
  | .minSlot .. => "minSlot"
  | .maxSlot .. => "maxSlot"
  | .absSlot .. => "absSlot"
  | .linEq .. => "linEq"
  | .linLe .. => "linLe"
  | .linNe .. => "linNe"
  | .ltSlot .. => "ltSlot"
  | .ltConstHi .. => "ltConstHi"
  | .ltConstLo .. => "ltConstLo"
  | .boolNotSlot .. => "boolNotSlot"
  | .boolAndSlot .. => "boolAndSlot"
  | .boolOrSlot .. => "boolOrSlot"
  | .boolClauseSlot .. => "boolClauseSlot"
  | .arrayBoolAndSlot .. => "arrayBoolAndSlot"
  | .bool2intSlot .. => "bool2intSlot"
  | .boolEqSlot .. => "boolEqSlot"
  | .arrayIntElementSlot .. => "arrayIntElementSlot"
  | .arrayVarIntElementSlot .. => "arrayVarIntElementSlot"
  | .arrayVarBoolElementSlot .. => "arrayVarBoolElementSlot"
  | .eqReifSlot .. => "eqReifSlot"
  | .leReifSlot .. => "leReifSlot"
  | .neReifSlot .. => "neReifSlot"
  | .linEqReif .. => "linEqReif"
  | .linLeReif .. => "linLeReif"
  | .linNeReif .. => "linNeReif"
  | .maxGen .. => "maxGen"
  | .minGen .. => "minGen"
  | .divGen .. => "divGen"
  | .modGen .. => "modGen"
  | .minPair .. => "minPair"
  | .maxPair .. => "maxPair"
  | .setInSlot .. => "setInSlot"
  | .setInReifSlot .. => "setInReifSlot"

/-- Family histogram of the constraints that HAVE a registered propagator,
    plus the total family histogram. -/
def famHist (dcs : List LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) :
    List (String × Nat) :=
  dcs.foldl (fun h dc =>
    let n := dcName dc
    if h.any (·.1 == n) then h.map (fun p => if p.1 == n then (p.1, p.2+1) else p)
    else h ++ [(n, 1)]) []

/-- The family histogram of the constraints with a registered propagator. -/
def propFamHist (dcs : List LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) :
    List (String × Nat) :=
  famHist (dcs.filter fun dc => (propagatorOfProved dc).isSome)


/-- Flushed print. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Force `act` inside the clock window (`IO.lazyPure` prevents dead-code
elimination of unused pure expressions). -/
def timeIt {α : Type} (act : Unit → α) : IO (Nat × α) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (t1 - t0, a)

/-- Clock an IO action (for recursive drivers with IO sampling). -/
def timeItIO {α : Type} (act : Unit → IO α) : IO (Nat × α) := do
  let t0 ← IO.monoNanosNow
  let a ← act ()
  let t1 ← IO.monoNanosNow
  return (t1 - t0, a)

structure Acc where
  steps : Nat := 0
  frameMs : Nat := 0
  viewedMs : Nat := 0
  massMs : Nat := 0
  dbScanMs : Nat := 0
  dbRefMs : Nat := 0
  propScanMs : Nat := 0
  propRunMs : Nat := 0
  promptMs : Nat := 0
  stepMs : Nat := 0
  sampled : Nat := 0
  propagates : Nat := 0
  active : Nat := 0
  dbSize : Nat := 0
  jumps : Nat := 0
  conflicts : Nat := 0
  consumes : Nat := 0
  propSteps : Nat := 0
  propMs : Nat := 0
  jumpSteps : Nat := 0
  jumpMs : Nat := 0
  decSteps : Nat := 0
  decMs : Nat := 0
  consSteps : Nat := 0
  consMs : Nat := 0
  othSteps : Nat := 0
  othMs : Nat := 0
  jumpSampled : Nat := 0
  jPromptMs : Nat := 0
  jAnaMs : Nat := 0
  jNovMs : Nat := 0
  jAna2Ms : Nat := 0
  jNovFastMs : Nat := 0
  jAnaFastMs : Nat := 0
  jPerfMs : Nat := 0
  jumpMax : Nat := 0
  jTrail : Nat := 0
  jDb : Nat := 0
  jLearned : Nat := 0

def sampleJump {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (plan : BackjumpPlan leaf) (an : ConflictAnalysis)
    (acc : Acc) : IO Acc := do
  let (tPrompt, ev) ← timeIt (fun _ =>
    nextPruningEventSched cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned)
  match ev.1 with
  | .conflict cs =>
    let c := cs.headD []
    let (tA1, _) ← timeIt (fun _ =>
      (analyzeAtAllowance cfg.orig cfg.branch.trail cfg.branch.level c).map (fun p => p.1.length))
    let (tNov, _) ← timeIt (fun _ => learnedRepeats cfg an.learned)
    let (tA2, _) ← timeIt (fun _ =>
      analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)
    let (tNovF, _) ← timeIt (fun _ => learnedRepeatsFast cfg an.learned)
    let (tAnaF, _) ← timeIt (fun _ => (countedAnalysisFast cfg c).2)
    let (tPerf, _) ← timeIt (fun _ =>
      (plan.perform cfg.branch cfg.orig cfg.original cfg.props).map (fun s => s.level))
    return { acc with
      jumpSampled := acc.jumpSampled + 1,
      jPromptMs := acc.jPromptMs + tPrompt,
      jAnaMs := acc.jAnaMs + tA1, jNovMs := acc.jNovMs + tNov,
      jAna2Ms := acc.jAna2Ms + tA2,
      jNovFastMs := acc.jNovFastMs + tNovF,
      jAnaFastMs := acc.jAnaFastMs + tAnaF,
      jPerfMs := acc.jPerfMs + tPerf,
      jTrail := acc.jTrail + cfg.branch.trail.length,
      jDb := acc.jDb + cfg.branch.learned.length,
      jLearned := acc.jLearned + an.learned.length }
  | _ => return { acc with jumpSampled := acc.jumpSampled + 1 }

def sample {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (acc : Acc) : IO Acc := do
  let f := cfg.branch.frame
  let db := cfg.branch.learned
  let (tFrame, _) ← timeIt (fun _ => Frame.domains f)
  let (tView, _) ← timeIt (fun _ => frameViewedB f)
  let (tMass, _) ← timeIt (fun _ => Frame.mass f)
  let (tDb, _) ← timeIt (fun _ => scanDatabaseFast cfg.original f db)
  let (tDbRef, _) ← timeIt (fun _ => scanDatabase cfg.original f db)
  let (tProp, _) ← timeIt (fun _ => scanPropagatorsSched f sched cfg.props)
  let (tRun, _) ← timeIt (fun _ =>
    cfg.props.foldl (fun n p => n + match p.run (frameState f) with
      | .stable => 0 | .conflict _ => 1 | .implied _ _ => 2) 0)
  let (tPrompt, _) ← timeIt (fun _ => nextPruningEventSched cfg.original cfg.props sched f db)
  return { acc with
    frameMs := acc.frameMs + tFrame, viewedMs := acc.viewedMs + tView,
    massMs := acc.massMs + tMass, dbScanMs := acc.dbScanMs + tDb,
    propScanMs := acc.propScanMs + tProp, propRunMs := acc.propRunMs + tRun,
    dbRefMs := acc.dbRefMs + tDbRef,
    promptMs := acc.promptMs + tPrompt, sampled := acc.sampled + 1,
    dbSize := max acc.dbSize db.length }

partial def walk {leaf : Assignment → Bool} (maxSamples : Nat) (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : Acc) : IO Acc := do
  let jumpMax := acc.jumpMax
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let (tStep, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
    let acc : Acc := { acc with steps := acc.steps + 1, stepMs := acc.stepMs + tStep }
    let acc :=
      match pr.1 with
      | .propagate _ => { acc with propagates := acc.propagates + 1, propSteps := acc.propSteps + 1, propMs := acc.propMs + tStep }
      | .analyzeConflict _ _ => { acc with conflicts := acc.conflicts + 1 }
      | .learnBackjumpAssert _ _ _ => { acc with jumps := acc.jumps + 1, jumpSteps := acc.jumpSteps + 1, jumpMs := acc.jumpMs + tStep }
      | .chronologicalFallback _ => { acc with consumes := acc.consumes + 1, consSteps := acc.consSteps + 1, consMs := acc.consMs + tStep }
      | .decide _ _ => { acc with decSteps := acc.decSteps + 1, decMs := acc.decMs + tStep }
      | .localExclude _ => { acc with consSteps := acc.consSteps + 1, consMs := acc.consMs + tStep }
      | _ => { acc with othSteps := acc.othSteps + 1, othMs := acc.othMs + tStep }
    let acc ←
      if acc.sampled < maxSamples && cfg.conflict.isNone && cfg.status == .active
          && acc.active % 1500 == 1 then
        let a ← sample cfg sched acc
        pure { a with active := a.active + 1 }
      else
        (if cfg.conflict.isNone && cfg.status == .active then pure { acc with active := acc.active + 1 }
         else pure acc)
    let acc ←
      match pr.1 with
      | .learnBackjumpAssert next plan an =>
        if acc.jumps % 300 == 1 && acc.jumpSampled < jumpMax then
          sampleJump cfg sched plan an acc
        else pure acc
      | _ => pure acc
    match pr.1 with
    | .sat _ => return acc
    | .unsat => return acc
    | _ =>
      match pr.1.successor with
      | some n => walk maxSamples fuel n pr.2 acc
      | none => return acc

/-- Optimization mode: time the public heuristic verdict on the base problem
and under a trial bound, then walk the bounded search with no sampling to
count steps. -/
def runOpt (bound : Int) (fuel samples : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    match LeanFzn.Compiler.compileModelOpt m with
    | .error e => say s!"FILE {path} compileOpt=ERROR {e.take 120}"
    | .ok (po, spec) =>
      let p1 := curP po spec none
      let p2 := curP po spec (some bound)
      let (tH, _) ← timeIt (fun _ => LcgHeur.heurDomains p2)
      let (t1, r1) ← timeIt (fun _ => LcgHeur.solveCompiledLcgHeur p1)
      let (t2, r2) ← timeIt (fun _ => LcgHeur.solveCompiledLcgHeur p2)
      say s!"OPT {path} heurMs={tH/1000000} baseMs={t1/1000000} base={repr r1} boundMs={t2/1000000} bound={repr r2}"
      let hd := LcgHeur.heurDomains p2
      let props := LcgHeur.heurProps p2
      let leaf := lcgLeaf p2
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p2.constraints) props
      let sched := PropScheduler.init props
      let t3 ← IO.monoNanosNow
      let acc ← walk samples fuel cfg sched { jumpMax := 4 }
      let t4 ← IO.monoNanosNow
      let per (x : Nat) : String := if acc.steps == 0 then "-" else s!"{x/acc.steps}"
      let perS (x : Nat) : String := if acc.sampled == 0 then "-" else s!"{x/acc.sampled}"
      let avg (x n : Nat) : String := if n == 0 then "-" else s!"{x / n}"
      say s!"OPTWALK {path} steps={acc.steps} propagates={acc.propagates} conflicts={acc.conflicts} jumps={acc.jumps} consumes={acc.consumes} walkMs={(t4-t3)/1000000} stepPerNs={per acc.stepMs}"
      let js := if acc.jumpSampled == 0 then 1 else acc.jumpSampled
      say s!"OPTJUMP {path} jumpSampled={acc.jumpSampled} promptNs={acc.jPromptMs/js} anaNs={acc.jAnaMs/js} novNs={acc.jNovMs/js} ana2Ns={acc.jAna2Ms/js} novFastNs={acc.jNovFastMs/js} anaFastNs={acc.jAnaFastMs/js} performNs={acc.jPerfMs/js} trailAvg={acc.jTrail/js} dbAvg={acc.jDb/js} learnedAvg={acc.jLearned/js}"
      say s!"OPTKIND {path} propSteps={acc.propSteps} propAvgNs={avg acc.propMs acc.propSteps} jumpSteps={acc.jumpSteps} jumpAvgNs={avg acc.jumpMs acc.jumpSteps} decSteps={acc.decSteps} decAvgNs={avg acc.decMs acc.decSteps} consSteps={acc.consSteps} consAvgNs={avg acc.consMs acc.consSteps} othMs={acc.othMs}"
      say s!"OPTTIME {path} frame={perS acc.frameMs} viewed={perS acc.viewedMs} mass={perS acc.massMs} dbScan={perS acc.dbScanMs} dbScanRef={perS acc.dbRefMs} propScan={perS acc.propScanMs} propRun={perS acc.propRunMs} prompt={perS acc.promptMs} sampled={acc.sampled}"
      let share (x : Nat) : String :=
        if acc.stepMs == 0 then "-" else s!"{100 * x / acc.stepMs}%"
      say s!"OPTSHARE {path} propRun={share acc.propRunMs} propScan={share acc.propScanMs} prompt={share acc.promptMs} viewed={share acc.viewedMs} mass={share acc.massMs} dbScan={share acc.dbScanMs}"

/-! ## Diagnostic: per-step cost decomposition (TEST-ONLY, UNCERTIFIED)

Times, at every step: the pruning prompt (`promptOf`: DB scan + frame gates +
propagator scan), the deduction selection (`explainedDeductionOf`: trail
redundancy + `filterFrame` + mass), and the three pieces of `stepPropagate`
the prompt does not cover (`narrowState`, `syncSlot`, the learned-clause
caches). `promptOf` is evaluated twice per step (once here, once inside
`phaseNextSched`), so the component numbers — not the absolute step time —
are the output. -/

structure DAcc where
  steps : Nat := 0
  promptNs : Nat := 0
  dbNs : Nat := 0
  viewNs : Nat := 0
  pscanNs : Nat := 0
  entries : Nat := 0
  dedNs : Nat := 0
  narrowNs : Nat := 0
  syncNs : Nat := 0
  cacheNs : Nat := 0
  stepNs : Nat := 0
  trailMax : Nat := 0
  trailSum : Nat := 0
  learnedMax : Nat := 0
  dedSome : Nat := 0
  keySum : Nat := 0

/-- K2 measurement twin of `promptOf`: identical policy switch, but the
non-queue branch uses the fused stamp scan `nextPruningEventFastSched`
(equal to `nextPruningEventSched` by `nextPruningEventFastSched_eq`). Used
ONLY by `--diagk2`; the default `--diag` path is unchanged. -/
def promptOfK2 (original : List Clause) (props : List Propagator) (sched : PropScheduler)
    (f : BranchFrame) (db : List Clause) : PruningEvent × PropScheduler :=
  if queuePolicy props f then
    nextPruningEventQueuedSched original props sched f db
  else
    nextPruningEventFastSched original props sched f db

partial def dwalk {leaf : Assignment → Bool} (k2 : Bool) (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : DAcc) : IO DAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let (tp, pr0) ← timeIt (fun _ =>
      if k2 then
        promptOfK2 cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned
      else
        promptOf cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned)
    let (tdb, _) ← timeIt (fun _ =>
      scanDatabaseFast cfg.original cfg.branch.frame cfg.branch.learned)
    let (tview, _) ← timeIt (fun _ => frameViewedB cfg.branch.frame)
    let (tps, _) ← timeIt (fun _ =>
      if k2 then
        scanPropagatorsSchedFast cfg.branch.frame sched cfg.props
      else
        scanPropagatorsSched cfg.branch.frame sched cfg.props)
    let nseen := (sched.seen.filter (fun e => e.isSome)).length
    let (td, dd) ← timeIt (fun _ =>
      explainedDeductionOf cfg.original cfg.props cfg.branch pr0.1)
    let (tn, ts, tc, btrail, ok, kk) ←
      match dd with
      | none => pure (0, 0, 0, cfg.branch.trail.length, false, 0)
      | some d =>
        let (tn, b1) ← timeIt (fun _ =>
          narrowState cfg.branch d.frame d.literal d.reason d.learned)
        let (ts, b2) ← timeIt (fun _ => syncSlot cfg.orig b1 d.literal.atom.slot)
        let nrm : List Clause := d.learned.map (fun c => c.map Literal.norm)
        let (tc, k) ← timeIt (fun _ =>
          (insertClauseKeys cfg.poolHash cfg.learnedKeys nrm).size)
        pure (tn, ts, tc, b2.trail.length, true, k)
    let (tstep, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
    let acc : DAcc :=
      { acc with
        steps := acc.steps + 1, promptNs := acc.promptNs + tp,
        dbNs := acc.dbNs + tdb, viewNs := acc.viewNs + tview,
        pscanNs := acc.pscanNs + tps, entries := acc.entries + nseen,
        dedNs := acc.dedNs + td, narrowNs := acc.narrowNs + tn,
        syncNs := acc.syncNs + ts, cacheNs := acc.cacheNs + tc,
        stepNs := acc.stepNs + tstep,
        trailMax := max acc.trailMax btrail,
        trailSum := acc.trailSum + btrail,
        learnedMax := max acc.learnedMax cfg.branch.learned.length,
        dedSome := acc.dedSome + (if ok then 1 else 0),
        keySum := acc.keySum + kk }
    match pr.1 with
    | .sat _ => return acc
    | .unsat => return acc
    | _ =>
      match pr.1.successor with
      | some n => dwalk k2 fuel n pr.2 acc
      | none => return acc

def runDiag (k2 : Bool) (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      let t0 ← IO.monoNanosNow
      let acc ← dwalk k2 fuel cfg sched {}
      let t1 ← IO.monoNanosNow
      let per (x : Nat) : Nat := if acc.steps == 0 then 0 else x / acc.steps
      if k2 then
        say s!"DIAGK2 {path} mode=fused prompt=promptOfK2 scan=scanPropagatorsSchedFast"
      say s!"DIAG {path} steps={acc.steps} dedSome={acc.dedSome} walkMs={(t1-t0)/1000000}"
      say s!"DIAGSTEP {path} stepNs={per acc.stepNs} promptNs={per acc.promptNs} dbNs={per acc.dbNs} viewNs={per acc.viewNs} pscanNs={per acc.pscanNs} dedNs={per acc.dedNs} narrowNs={per acc.narrowNs} syncNs={per acc.syncNs} cacheNs={per acc.cacheNs} entries={per acc.entries}"
      say s!"DIAGSHAPE {path} trailAvg={per acc.trailSum} trailMax={acc.trailMax} learnedMax={acc.learnedMax} keysAvg={per acc.keySum}"


/-! ## Diagnostic: multi-literal step width (TEST-ONLY, UNCERTIFIED; PLAN K4 W0)

`--diagbatch FUEL FILE...` walks exactly like `--diag` (`phaseNextSched` still
drives every transition) but, at every active prompt step, additionally runs
the two bounded one-pass unit collections of the K4 design draft (§2 B/§5.1):

* `collectDbUnits`: walk the learned DB in order and keep the first `batchCap`
  clauses whose `clauseRemaining` is a singleton (the unit literal); a clause
  with no remaining literal is a conflict and preempts every collected unit.
  The indexed classifier is used above the same `db.length ≤ 8` crossover as
  `scanDatabaseFast` (the reference `clauseRemaining` walk is used below it);
  both branches return the same units.
* `collectPropUnits`: one cached pass over the propagator list with the same
  version-stamp table and reuse test as `scanPropagatorsSched`, but continuing
  after a productive `.implied` instead of returning it. A cache-clean
  propagator is not run again; a propagator contributes at most one literal
  and is never re-run per literal. A `.conflict` preempts the pass.

Neither pass advances the branch: the next transition is the certified
`phaseNextSched` step. `dbWidth`/`propWidth` are the collected list lengths
capped at `batchCap` (DB first, then the remaining cap for propagators).
The DB units are the design's `frameLiveB`-gated list (a conflict is never
gated; at a dead frame the unit list is empty), and the propagator pass runs
only when `frameViewedB f`, never after a conflict. `total` is their sum,
forced to 0 when either pass reports a conflict (the design's conflict
preemption). Means are over measured active prompt steps (`active`); `steps`
counts every walk iteration like `--diag`.

`dbProdWidth` counts the collected DB units that pass the scan's `productive`
gate; `effective = dbProdWidth + propWidth` is the number of units on which
the fold acts at all (a strict narrowing or the dead landing), and
`noProgress` flags `total > 0 ∧ effective = 0`, i.e. a nonempty batch whose
units are all non-productive (the `batchFold` `n = 0` self-loop gap of §5.2).
Raw `dbWidth` deliberately counts every unit clause, as §3 specifies.

`disagree` compares the batch's selected event (conflict; otherwise the first
productive DB unit, then the first productive propagator unit) with the event
the certified scheduled prompt selects from `scanDatabaseFast` +
`scanPropagatorsSched` at the same frame (the `nextPruningEventSched` gating,
which `promptOf_fst_eq` identifies with the event the wired step consumes).
A conflict later in a pass may preempt an earlier single-step implication
(the documented K4 conflict risk); `litDisagree` excludes those conflict
steps. It still counts the batch's other divergence: the batch skips a
non-productive DB unit and selects a later productive one (or a propagator
unit), while the certified prompt reports the first DB unit even when the
deduction filter then rejects it. A nonzero `litDisagree` with
`dbProdWidth < dbWidth` on the same steps is exactly that skip gap; on steps
where every collected DB unit is productive it should stay 0. -/

/-- The K4 design cap (§5.1). -/
def batchCap : Nat := 8

/-- One bounded collection pass: a falsified clause preempts the pass, or the
    unit literals collected in scan order (list order). -/
inductive UnitPass where
  | conflict (clause : Clause)
  | units (lits : List Literal)
  deriving DecidableEq, BEq, Repr, Nonempty

/-- Increment bucket `i` of a width histogram. -/
def bumpWidth : List Nat → Nat → List Nat
  | [], _ => []
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, n + 1 => x :: bumpWidth xs n

/-- Reference DB unit pass (`clauseRemaining`, DB order). Collects at most
    `cap` unit clauses; a falsified clause returns `.conflict` immediately;
    the walk stops once the cap is reached (a full batch inspects no more). -/
partial def collectDbUnitsRef (f : BranchFrame) (cap : Nat) :
    List Clause → List Literal → UnitPass
  | [], acc => .units acc.reverse
  | c :: rest, acc =>
    if acc.length ≥ cap then .units acc.reverse
    else
      match clauseRemaining f c with
      | [] => .conflict c
      | [l] =>
          let acc := l :: acc
          if acc.length ≥ cap then .units acc.reverse
          else collectDbUnitsRef f cap rest acc
      | _ => collectDbUnitsRef f cap rest acc

/-- Indexed DB unit pass: `clauseClassifyFast`'s classification of every
    clause, collecting unit clauses instead of stopping at the first event.
    `none` is a clause with no remaining literal, `some none` a non-unit. -/
partial def collectDbUnitsFast (a : Array Domain) (sums : Array SlotSum) (cap : Nat) :
    List Clause → List Literal → UnitPass
  | [], acc => .units acc.reverse
  | c :: rest, acc =>
    if acc.length ≥ cap then .units acc.reverse
    else
      match clauseClassifyFast a sums c none with
      | none => .conflict c
      | some none => collectDbUnitsFast a sums cap rest acc
      | some (some l) =>
          let acc := l :: acc
          if acc.length ≥ cap then .units acc.reverse
          else collectDbUnitsFast a sums cap rest acc

/-- The DB unit collection of the K4 design, using `scanDatabaseFast`'s hybrid
    dispatch (reference below the small-DB crossover, indexed above it). -/
def collectDbUnits (f : BranchFrame) (cap : Nat) (db : List Clause) : UnitPass :=
  if db.length ≤ 8 then collectDbUnitsRef f cap db []
  else
    let a := frameDomainArray f
    let sums := sumsOfArray a
    collectDbUnitsFast a sums cap db []

/-- The propagator unit collection: `scanPropagatorsSchedAux`'s order and
    version-stamp reuse test, but `.stable` and non-productive `.implied`
    results continue the scan and a productive `.implied` is collected instead
    of returned. A `.conflict` preempts; the pass stops at `cap` units. The
    `seen`/`props` lists stay positionally aligned, so a cache hit never runs
    the propagator and a run never feeds a later position's reuse decision. -/
partial def collectPropUnitsAux (f : BranchFrame) (v : SchedVersions) (cap : Nat) :
    List (Option SchedEntry) → List Propagator → List Literal → UnitPass
  | _, [], acc => .units acc.reverse
  | seens, p :: ps, acc =>
    if acc.length ≥ cap then .units acc.reverse
    else
      let r :=
        match seens with
        | some e :: _ =>
            if stampNatEqB e.stamps (watchVersions v p.watches) && !p.watches.isEmpty
            then e.result
            else p.run (frameState f)
        | _ => p.run (frameState f)
      let rest :=
        match seens with
        | _ :: tl => tl
        | [] => []
      match r with
      | .stable => collectPropUnitsAux f v cap rest ps acc
      | .conflict c => .conflict c
      | .implied l _ =>
          if productive l f then
            let acc := l :: acc
            if acc.length ≥ cap then .units acc.reverse
            else collectPropUnitsAux f v cap rest ps acc
          else collectPropUnitsAux f v cap rest ps acc

/-- Sync the version table to the frame (as `scanPropagatorsSched` does on
    every call) and run the bounded collection pass. -/
def collectPropUnits (f : BranchFrame) (sched : PropScheduler) (cap : Nat)
    (props : List Propagator) : UnitPass :=
  let sched' := sched.sync f
  collectPropUnitsAux f sched'.versions cap sched'.seen props []

/-- Test-only selected-event form shared by the batch and single-step
    comparison: a literal, a conflict clause, or stability. -/
inductive BatchSel where
  | stable
  | conflict (clause : Clause)
  | lit (literal : Literal)
  deriving DecidableEq, BEq, Repr

/-- The selected event's comparable payload. `scanDatabase` reports `[c]` and
    the propagator scan `[]` for an empty reason clause, so `headD []`
    normalizes both to the clause itself. -/
def eventSel : PruningEvent → BatchSel
  | .stable => .stable
  | .conflict cs => .conflict (cs.headD [])
  | .implied l _ _ _ => .lit l

/-- The first productive literal of a collected list, in collection order. -/
def firstProductive (f : BranchFrame) (ls : List Literal) : Option Literal :=
  ls.findSome? fun l => if productive l f then some l else none

/-- The batch's selected event: a DB or propagator conflict wins; otherwise
    the first productive DB unit, then the first productive propagator unit.
    Non-productive collected units are skipped exactly as the batch fold
    skips them. -/
def batchSel (f : BranchFrame) (dbRes propRes : UnitPass) : BatchSel :=
  match dbRes with
  | .conflict c => .conflict c
  | .units dbl =>
      match propRes with
      | .conflict c => .conflict c
      | .units pl =>
          match firstProductive f dbl with
          | some l => .lit l
          | none =>
              match firstProductive f pl with
              | some l => .lit l
              | none => .stable

/-- The event selected by the certified scheduled prompt at the same frame:
    `scanDatabaseFast`'s event, live-gated exactly as
    `nextPruningEventSched` gates it, then `scanPropagatorsSched`'s event
    when the DB is stable and the frame is viewed. -/
def schedSel (f : BranchFrame) (evDb evPs : PruningEvent) : BatchSel :=
  match evDb with
  | .stable => if frameViewedB f then eventSel evPs else .stable
  | .conflict cs => .conflict (cs.headD [])
  | .implied l _ _ _ => if frameLiveB f then .lit l else .stable

structure BAcc where
  steps : Nat := 0
  active : Nat := 0
  propRuns : Nat := 0
  dbWidthSum : Nat := 0
  propWidthSum : Nat := 0
  effectiveSum : Nat := 0
  widthSum : Nat := 0
  widthMax : Nat := 0
  zero : Nat := 0
  zeroConflict : Nat := 0
  zeroEmpty : Nat := 0
  noProgress : Nat := 0
  dbConflict : Nat := 0
  propConflict : Nat := 0
  disagree : Nat := 0
  litDisagree : Nat := 0
  dbNs : Nat := 0
  pscanNs : Nat := 0
  dbBatchNs : Nat := 0
  propBatchNs : Nat := 0
  hist : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Measure one active prompt step: the two single-scan reference times
(`dbNs`/`pscanNs`), the two collection passes, the width bookkeeping, and the
selected-event comparison. Nothing here mutates the walk state. -/
def measureBatch {leaf : Assignment → Bool} (path : String)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : BAcc) : IO BAcc := do
  let f := cfg.branch.frame
  let db := cfg.branch.learned
  let viewed := frameViewedB f
  let live := frameLiveB f
  let (tdb, evDb) ← timeIt (fun _ => scanDatabaseFast cfg.original f db)
  let (tps, nps) ← timeIt (fun _ => scanPropagatorsSched f sched cfg.props)
  let evPs := nps.1
  let (tdbB, dbRes) ← timeIt (fun _ => collectDbUnits f batchCap db)
  let dbGated : UnitPass :=
    match dbRes with
    | .conflict c => .conflict c
    | .units ls => if live then .units ls else .units []
  let dbW :=
    match dbGated with
    | .conflict _ => 0
    | .units ls => ls.length
  let dbConf :=
    match dbGated with
    | .conflict _ => true
    | .units _ => false
  let rem := batchCap - dbW
  let runProp := viewed && !dbConf && decide (0 < rem)
  let (tpb, propRes) ←
    if runProp then
      timeIt (fun _ => collectPropUnits f sched rem cfg.props)
    else pure (0, (UnitPass.units [] : UnitPass))
  let propW :=
    match propRes with
    | .conflict _ => 0
    | .units ls => ls.length
  let propConf :=
    match propRes with
    | .conflict _ => true
    | .units _ => false
  let total := if dbConf || propConf then 0 else dbW + propW
  let dbProdW :=
    match dbGated with
    | .conflict _ => 0
    | .units dbl => dbl.foldl (fun n l => n + (if productive l f then 1 else 0)) 0
  let effective := dbProdW + propW
  let noProg := if total != 0 && effective == 0 then 1 else 0
  let dis := if batchSel f dbGated propRes == schedSel f evDb evPs then 0 else 1
  let ldis := if dbConf || propConf then 0 else dis
  say s!"DIAGBATCHSTEP {path} step={acc.steps} dbWidth={dbW} dbProdWidth={dbProdW} \
propWidth={propW} total={total} effective={effective} noProgress={noProg} \
dbConflict={if dbConf then 1 else 0} propConflict={if propConf then 1 else 0} \
dbNs={tdb} pscanNs={tps} dbBatchNs={tdbB} propBatchNs={tpb} disagree={dis} \
litDisagree={ldis}"
  return { acc with
    active := acc.active + 1,
    propRuns := acc.propRuns + (if runProp then 1 else 0),
    dbWidthSum := acc.dbWidthSum + dbW,
    propWidthSum := acc.propWidthSum + propW,
    effectiveSum := acc.effectiveSum + effective,
    widthSum := acc.widthSum + total,
    widthMax := max acc.widthMax total,
    zero := acc.zero + (if total == 0 then 1 else 0),
    zeroConflict := acc.zeroConflict + (if dbConf || propConf then 1 else 0),
    zeroEmpty := acc.zeroEmpty + (if total == 0 && !(dbConf || propConf) then 1 else 0),
    noProgress := acc.noProgress + noProg,
    dbConflict := acc.dbConflict + (if dbConf then 1 else 0),
    propConflict := acc.propConflict + (if propConf then 1 else 0),
    disagree := acc.disagree + dis,
    litDisagree := acc.litDisagree + ldis,
    dbNs := acc.dbNs + tdb,
    pscanNs := acc.pscanNs + tps,
    dbBatchNs := acc.dbBatchNs + tdbB,
    propBatchNs := acc.propBatchNs + tpb,
    hist := bumpWidth acc.hist total }

/-- Same walk as `--diag` (`phaseNextSched` is still the only transition), with
the batch measurement inserted before each active step. -/
partial def bwalk {leaf : Assignment → Bool} (path : String) (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : BAcc) : IO BAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let acc := { acc with steps := acc.steps + 1 }
    let acc ←
      if cfg.conflict.isNone && cfg.status == .active then
        measureBatch path cfg sched acc
      else pure acc
    let pr ← IO.lazyPure (fun _ => phaseNextSched cfg sched)
    match pr.1 with
    | .sat _ => return acc
    | .unsat => return acc
    | _ =>
      match pr.1.successor with
      | some n => bwalk path fuel n pr.2 acc
      | none => return acc

/-- Summary of one `--diagbatch` walk. `meanPm`/`dbMeanPm`/`propMeanPm`/
`effMeanPm` are widths ×1000 over active prompt steps; `ratioPm` is the
raw total collection time against the raw total single-scan time (×1000,
1000 = equal), with the per-pass `dbRatioPm`/`propRatioPm` using
`active`/`propRuns` respectively. Unlike `total`, the width sums keep raw
collected counts: on a propagator conflict step `dbWidthSum` still includes
the DB units collected before the conflict; a DB conflict zeroes both (the
propagator pass is not run). The histogram and `zero*` use `total`. -/
def reportDiagBatch (path : String) (walkMs : Nat) (a : BAcc) : IO Unit := do
  let n := a.active
  let meanPm (x : Nat) : Nat := if n == 0 then 0 else 1000 * x / n
  let nsPer (x runs : Nat) : Nat := if runs == 0 then 0 else x / runs
  let ratio (x y : Nat) : Nat := if y == 0 then 0 else 1000 * x / y
  let ratioPer (x xr y yr : Nat) : Nat :=
    if xr == 0 || yr == 0 || y == 0 then 0 else 1000 * x * yr / (y * xr)
  let hist := ",".intercalate (a.hist.zipIdx.map fun (k, i) => s!"{i}:{k}")
  say s!"DIAGBATCHSUM {path} steps={a.steps} active={n} propRuns={a.propRuns} \
walkedMs={walkMs} meanPm={meanPm a.widthSum} dbMeanPm={meanPm a.dbWidthSum} \
propMeanPm={meanPm a.propWidthSum} effMeanPm={meanPm a.effectiveSum} \
max={a.widthMax} zero={a.zero} \
zeroConflict={a.zeroConflict} zeroEmpty={a.zeroEmpty} noProgress={a.noProgress} \
dbConflict={a.dbConflict} \
propConflict={a.propConflict} disagree={a.disagree} litDisagree={a.litDisagree} \
hist={hist} ratioPm={ratio (a.dbBatchNs + a.propBatchNs) (a.dbNs + a.pscanNs)}"
  say s!"DIAGBATCHTIME {path} dbNs={nsPer a.dbNs n} pscanNs={nsPer a.pscanNs n} \
dbBatchNs={nsPer a.dbBatchNs n} propBatchNs={nsPer a.propBatchNs a.propRuns} \
dbRatioPm={ratioPer a.dbBatchNs n a.dbNs n} \
propRatioPm={ratioPer a.propBatchNs a.propRuns a.pscanNs n}"

/-- `--diagbatch FUEL FILE...`: the `--diag` configuration and walk, with the
K4 batch-width measurement at each active prompt step. TEST-ONLY/UNCERTIFIED. -/
def runDiagBatch (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      let t0 ← IO.monoNanosNow
      let acc ← bwalk path fuel cfg sched {}
      let t1 ← IO.monoNanosNow
      reportDiagBatch path ((t1 - t0) / 1000000) acc


/-! ## Diagnostic: split of `syncNs` (TEST-ONLY, UNCERTIFIED; PLAN K1 step 1)

Times the four pieces of one `syncSlot` call on the same `BranchState`
that the wired step feeds it: the slot-trail filter (`trailOnSlot`), the
current-domain guard (`Dom.enum d` + `valueAllFast`), the original-domain
rejected-value list (`Dom.enum od` + filter) and the per-rejected-value
`syncRemover` scans. The pieces are timed *in addition to* the real
`syncSlot` call, so this run is for the split only; the K-panel numbers
come from `--diag`. -/

structure SAcc where
  steps : Nat := 0
  dedSome : Nat := 0
  syncNs : Nat := 0
  candsNs : Nat := 0
  idxNs : Nat := 0
  guardNs : Nat := 0
  wNs : Nat := 0
  anyNs : Nat := 0
  remNs : Nat := 0
  sumCands : Nat := 0
  sumTl : Nat := 0
  sumW : Nat := 0
  sumOd : Nat := 0
  sumCur : Nat := 0
  sumRem : Nat := 0
  explCnt : Nat := 0

partial def swalk {leaf : Assignment → Bool} (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : SAcc) : IO SAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let (_, pr0) ← timeIt (fun _ =>
      promptOf cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned)
    let (_, dd) ← timeIt (fun _ =>
      explainedDeductionOf cfg.original cfg.props cfg.branch pr0.1)
    match dd with
    | none =>
      let (_, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
      let acc := { acc with steps := acc.steps + 1 }
      match pr.1 with
      | .sat _ => return acc
      | .unsat => return acc
      | _ =>
        match pr.1.successor with
        | some n => swalk fuel n pr.2 acc
        | none => return acc
    | some d =>
      let (_, b1) ← timeIt (fun _ =>
        narrowState cfg.branch d.frame d.literal d.reason d.learned)
      let s := d.literal.atom.slot
      let (ts, _) ← timeIt (fun _ => syncSlot cfg.orig b1 s)
      -- the split, on the same pre-sync state b1
      let l := d.literal.norm
      let od := cfg.orig.getD s Dom.empty
      let (tc, cands) ← timeIt (fun _ => syncCands cfg.orig b1.frame s)
      let (tidx, tl) ← timeIt (fun _ => trailOnSlot b1.trail s)
      let (tg, gok) ← timeIt (fun _ =>
        match b1.frame.doms[s]? with
        | none => false
        | some cur => !cur.isEmpty && valueAllFast l.valueHolds (Dom.enum cur))
      let (ta, aimp) ← timeIt (fun _ =>
        tl.any fun e => impliesP cfg.orig e.literal l)
      let (tw, W) ← timeIt (fun _ =>
        if gok && !aimp then
          (Dom.enum od).filter fun w => !l.valueHolds w
        else [])
      let (tr, nrem) ← timeIt (fun _ =>
        if !W.isEmpty then
          let rs := W.map (syncRemover tl s)
          if rs.any Option.isNone then 0 else (rs.filterMap id).eraseDups.length
        else 0)
      let (_, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
      let acc : SAcc :=
        { acc with
          steps := acc.steps + 1, dedSome := acc.dedSome + 1,
          syncNs := acc.syncNs + ts, candsNs := acc.candsNs + tc,
          idxNs := acc.idxNs + tidx, guardNs := acc.guardNs + tg,
          wNs := acc.wNs + tw, anyNs := acc.anyNs + ta, remNs := acc.remNs + tr,
          sumCands := acc.sumCands + cands.length,
          sumTl := acc.sumTl + tl.length,
          sumW := acc.sumW + W.length,
          sumOd := acc.sumOd + od.length,
          sumCur := acc.sumCur + (match b1.frame.doms[s]? with
            | none => 0 | some cur => cur.length),
          sumRem := acc.sumRem + nrem,
          explCnt := acc.explCnt + (if !W.isEmpty then 1 else 0) }
      match pr.1 with
      | .sat _ => return acc
      | .unsat => return acc
      | _ =>
        match pr.1.successor with
        | some n => swalk fuel n pr.2 acc
        | none => return acc

def runDiagSplit (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      let t0 ← IO.monoNanosNow
      let acc ← swalk fuel cfg sched {}
      let t1 ← IO.monoNanosNow
      let per (x : Nat) : Nat := if acc.steps == 0 then 0 else x / acc.steps
      let avg (x n : Nat) : Nat := if n == 0 then 0 else x / n
      let ex := acc.explCnt
      say s!"DIAGSPLIT {path} steps={acc.steps} dedSome={acc.dedSome} expl={ex} walkMs={(t1-t0)/1000000}"
      say s!"DIAGSPLITNS {path} syncNs={per acc.syncNs} candsNs={per acc.candsNs} idxNs={per acc.idxNs} guardNs={per acc.guardNs} anyNs={per acc.anyNs} wNs={per acc.wNs} remNs={per acc.remNs} wShare={if per acc.syncNs == 0 then 0 else 100 * per acc.wNs / per acc.syncNs} remShare={if per acc.syncNs == 0 then 0 else 100 * per acc.remNs / per acc.syncNs} idxShare={if per acc.syncNs == 0 then 0 else 100 * per acc.idxNs / per acc.syncNs} guardShare={if per acc.syncNs == 0 then 0 else 100 * per acc.guardNs / per acc.syncNs} anyShare={if per acc.syncNs == 0 then 0 else 100 * per acc.anyNs / per acc.syncNs}"
      say s!"DIAGSPLITSIZE {path} candsAvg={avg acc.sumCands acc.steps} tlAvg={avg acc.sumTl acc.steps} wAvg={avg acc.sumW ex} odAvg={avg acc.sumOd acc.steps} curAvg={avg acc.sumCur acc.steps} remAvg={avg acc.sumRem ex}"


/-! ## Diagnostic: per-candidate `syncSlot` replay (TEST-ONLY, UNCERTIFIED)

The `--diagsplit` probe times each piece once per `syncSlot` call; the real
call runs the guard, the trail scan and the implication scan once per
CANDIDATE.  This replay walks the candidate list exactly like `syncSlot`
(`syncClause` + `narrowState` on the growing trail) and times the pieces on
the state each candidate actually sees.  It is used only to justify the K1
design; the K-panel numbers come from `--diag`. -/

structure PS where
  cands : Nat := 0
  idxNs : Nat := 0
  guardNs : Nat := 0
  anyNs : Nat := 0
  explNs : Nat := 0
  clauseNs : Nat := 0
  candsNs : Nat := 0
  sumTl : Nat := 0
  sumCur : Nat := 0
  sumCands : Nat := 0
  explCnt : Nat := 0

partial def probeCands {leaf : Assignment → Bool} (orig : List Domain)
    (b : BranchState leaf) (cs : List Literal) (acc : PS) : IO (PS × BranchState leaf) := do
  match cs with
  | [] => return (acc, b)
  | l :: rest =>
    let s := l.atom.slot
    let od := orig.getD s Dom.empty
    let (ti, tl) ← timeIt (fun _ => trailOnSlot b.trail s)
    let (tg, gok) ← timeIt (fun _ =>
      match b.frame.doms[s]? with
      | none => false
      | some d => !d.isEmpty && valueAllFast l.norm.valueHolds (Dom.enum d))
    let (ta, aimp) ← timeIt (fun _ => tl.any fun e => impliesP orig e.literal l.norm)
    let (te, _) ← timeIt (fun _ =>
      if gok && !aimp then syncExplain tl s
        ((Dom.enum od).filter fun w => !l.norm.valueHolds w)
      else none)
    let (tcl, cl) ← timeIt (fun _ => syncClause orig b l)
    let (_, b') ← timeIt (fun _ =>
      match cl with
      | some c => narrowState b b.frame l c []
      | none => b)
    let acc := { acc with
      cands := acc.cands + 1, idxNs := acc.idxNs + ti, guardNs := acc.guardNs + tg,
      anyNs := acc.anyNs + ta, explNs := acc.explNs + te, clauseNs := acc.clauseNs + tcl,
      sumTl := acc.sumTl + tl.length,
      sumCur := acc.sumCur + (match b.frame.doms[s]? with
        | none => 0 | some d => d.length),
      explCnt := acc.explCnt + (if gok && !aimp then 1 else 0) }
    probeCands orig b' rest acc

def probeSlot {leaf : Assignment → Bool} (orig : List Domain)
    (b : BranchState leaf) (s : Nat) : IO (PS × BranchState leaf) := do
  let (tc, cs) ← timeIt (fun _ => syncCands orig b.frame s)
  let (acc, b') ← probeCands orig b cs {}
  return ({ acc with candsNs := acc.candsNs + tc, sumCands := cs.length }, b')

structure PWAcc where
  steps : Nat := 0
  syncNs : Nat := 0
  idxNs : Nat := 0
  guardNs : Nat := 0
  anyNs : Nat := 0
  explNs : Nat := 0
  clauseNs : Nat := 0
  candsNs : Nat := 0
  sumTl : Nat := 0
  sumCur : Nat := 0
  sumCands : Nat := 0
  explCnt : Nat := 0

partial def swalkProbe {leaf : Assignment → Bool} (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : PWAcc) : IO PWAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let (_, pr0) ← timeIt (fun _ =>
      promptOf cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned)
    let (_, dd) ← timeIt (fun _ =>
      explainedDeductionOf cfg.original cfg.props cfg.branch pr0.1)
    match dd with
    | none =>
      let (_, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
      let acc := { acc with steps := acc.steps + 1 }
      match pr.1 with
      | .sat _ => return acc
      | .unsat => return acc
      | _ =>
        match pr.1.successor with
        | some n => swalkProbe fuel n pr.2 acc
        | none => return acc
    | some d =>
      let (_, b1) ← timeIt (fun _ =>
        narrowState cfg.branch d.frame d.literal d.reason d.learned)
      let s := d.literal.atom.slot
      let (ts, _) ← timeIt (fun _ => syncSlot cfg.orig b1 s)
      let (p, _) ← probeSlot cfg.orig b1 s
      let acc : PWAcc :=
        { acc with
          steps := acc.steps + 1, syncNs := acc.syncNs + ts,
          idxNs := acc.idxNs + p.idxNs, guardNs := acc.guardNs + p.guardNs,
          anyNs := acc.anyNs + p.anyNs, explNs := acc.explNs + p.explNs,
          clauseNs := acc.clauseNs + p.clauseNs, candsNs := acc.candsNs + p.candsNs,
          sumTl := acc.sumTl + p.sumTl, sumCur := acc.sumCur + p.sumCur,
          sumCands := acc.sumCands + p.sumCands, explCnt := acc.explCnt + p.explCnt }
      let (_, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
      match pr.1 with
      | .sat _ => return acc
      | .unsat => return acc
      | _ =>
        match pr.1.successor with
        | some n => swalkProbe fuel n pr.2 acc
        | none => return acc

def runDiagSync (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      let t0 ← IO.monoNanosNow
      let acc ← swalkProbe fuel cfg sched {}
      let t1 ← IO.monoNanosNow
      let per (x n : Nat) : Nat := if n == 0 then 0 else x / n
      let avg (x n : Nat) : Nat := if n == 0 then 0 else x / n
      say s!"DIAGSYNC {path} steps={acc.steps} expl={acc.explCnt} walkMs={(t1-t0)/1000000}"
      say s!"DIAGSYNCPER {path} syncNs={per acc.syncNs acc.steps} candsNs={per acc.candsNs acc.steps} idxNs={per acc.idxNs acc.steps} guardNs={per acc.guardNs acc.steps} anyNs={per acc.anyNs acc.steps} explNs={per acc.explNs acc.steps} clauseNs={per acc.clauseNs acc.steps}"
      say s!"DIAGSYNCSIZE {path} candsAvg={avg acc.sumCands acc.steps} tlAvg={avg acc.sumTl acc.steps} curAvg={avg acc.sumCur acc.steps}"

/-! ## Root presolve prototype (PLAN P4, TEST-ONLY/UNCERTIFIED)

`presolveSweep` runs every propagator once in reference order, applying each
productive implied literal immediately and re-running the SAME unit to its
local fixpoint; `presolveLoop` repeats sweeps until a sweep removes nothing
(or the fuel runs out).  This is the batched alternative to the dispatcher's
one-literal-per-step loop; the prototype measures the closure cost/mass at
the root against the scheduled reference walk. -/

/-- Run one unit to its local fixpoint (fuel = current frame mass). -/
partial def unitFix (p : Propagator) (f : BranchFrame) (fuel : Nat) :
    Option (BranchFrame × Nat) :=
  match fuel with
  | 0 => some (f, 0)
  | fuel + 1 =>
    match p.run (frameState f) with
    | .stable => some (f, 0)
    | .conflict _ => none
    | .implied l _ =>
      match filterFrame l f with
      | none => none
      | some g =>
        if Frame.mass g < Frame.mass f then
          match unitFix p g fuel with
          | some (g', n) => some (g', n + 1)
          | none => none
        else some (f, 0)

/-- One sweep over the propagator list. -/
partial def presolveSweep (props : List Propagator) (f : BranchFrame) :
    Option (BranchFrame × Nat) :=
  match props with
  | [] => some (f, 0)
  | p :: ps =>
    match unitFix p f (Frame.mass f) with
    | none => none
    | some (g, n) =>
      match presolveSweep ps g with
      | none => none
      | some (h, m) => some (h, n + m)

/-- Sweep to a global fixpoint (fuel = number of sweeps). -/
partial def presolveLoop (props : List Propagator) (f : BranchFrame) (fuel : Nat) :
    Option (BranchFrame × Nat × Nat) :=
  match fuel with
  | 0 => some (f, 0, 0)
  | fuel + 1 =>
    let m0 := Frame.mass f
    match presolveSweep props f with
    | none => none
    | some (g, n) =>
      if Frame.mass g < m0 then
        match presolveLoop props g fuel with
        | none => none
        | some (h, n', k) => some (h, n + n', k + 1)
      else some (g, n, 1)

/-- Reference root closure through the scheduled dispatcher (stops at the
first non-`.propagate` transition). -/
partial def closeRef {leaf : Assignment → Bool} (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    IO (Nat × Nat × Nat) := do
  match fuel with
  | 0 => return (0, Frame.mass cfg.branch.frame, 0)
  | fuel + 1 =>
    let (t, pr) ← timeIt (fun _ => phaseNextSched cfg sched)
    match pr.1 with
    | .propagate _ =>
      match pr.1.successor with
      | some n =>
        let (k, m, tot) ← closeRef fuel n pr.2
        return (k + 1, m, tot + t)
      | none => return (1, Frame.mass cfg.branch.frame, t)
    | _ => return (0, Frame.mass cfg.branch.frame, t)

def runPresolve (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      let f0 := cfg.branch.frame
      let m0 := Frame.mass f0
      let (tPre, pre) ← timeIt (fun _ => presolveLoop props f0 (m0 + 1))
      say s!"PRESOLVE {path} massBefore={m0} timeMs={tPre/1000000}"
      match pre with
      | none => say s!"PRESOLVE_RESULT {path} conflict"
      | some (g, n, sweeps) =>
          say s!"PRESOLVE_RESULT {path} massAfter={Frame.mass g} applied={n} sweeps={sweeps}"
      let (tRef, ref) ← timeItIO (fun _ => closeRef 400000 cfg sched)
      say s!"REFCLOSE {path} steps={ref.1} massAfter={ref.2.1} timeMs={tRef/1000000}"


/-- Compare the two closure engines at one node: batched presolve (fresh) and
the scheduled reference driver (current table). -/
def compareAtNode {leaf : Assignment → Bool} (path : String) (step : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) : IO Unit := do
  let f0 := cfg.branch.frame
  let m0 := Frame.mass f0
  let (tPre, pre) ← timeIt (fun _ => presolveLoop cfg.props f0 (m0 + 1))
  let preS := match pre with
    | none => s!"massAfter=CONFLICT applied=- sweeps=-"
    | some (g, n, sw) => s!"massAfter={Frame.mass g} applied={n} sweeps={sw}"
  let (tRef, ref) ← timeItIO (fun _ => closeRef 10000 cfg sched)
  say s!"NODE {path} step={step} mass={m0} preMs={tPre/1000000} {preS} refSteps={ref.1} refMass={ref.2.1} refMs={tRef/1000000}"

/-- Walk the reference driver and compare both closures at the requested
step numbers (1-indexed, measured before executing the step). -/
partial def nodeCloseWalk {leaf : Assignment → Bool} (path : String)
    (targets : List Nat) (fuel : Nat) (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (step : Nat) : IO Unit := do
  match fuel with
  | 0 => pure ()
  | fuel + 1 =>
    if targets.contains (step + 1) && cfg.conflict.isNone && cfg.status == .active then
      compareAtNode path (step + 1) cfg sched
    let pr ← IO.lazyPure (fun _ => phaseNextSched cfg sched)
    match pr.1 with
    | .sat _ => pure ()
    | .unsat => pure ()
    | _ =>
      match pr.1.successor with
      | some n => nodeCloseWalk path targets fuel n pr.2 (step + 1)
      | none => pure ()

def runNodeClose (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched := PropScheduler.init props
      nodeCloseWalk path [1,2,3,5,10,20,50,100,200,500,1000,2000] 4000 cfg sched 0


/-- Step-counting walk (no sampling) used by the presolve prototype. -/
partial def tagWalk {leaf : Assignment → Bool} (fuel : Nat)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (steps props decs confl : Nat) : IO (Nat × Nat × Nat × Nat × Bool) := do
  match fuel with
  | 0 => return (steps, props, decs, confl, false)
  | fuel + 1 =>
    let pr ← IO.lazyPure (fun _ => phaseNextSched cfg sched)
    match pr.1 with
    | .sat _ => return (steps + 1, props, decs, confl, true)
    | .unsat => return (steps + 1, props, decs, confl, false)
    | .propagate _ =>
      match pr.1.successor with
      | some n => tagWalk fuel n pr.2 (steps+1) (props+1) decs confl
      | none => return (steps+1, props+1, decs, confl, false)
    | .decide _ _ =>
      match pr.1.successor with
      | some n => tagWalk fuel n pr.2 (steps+1) props (decs+1) confl
      | none => return (steps+1, props, decs+1, confl, false)
    | .analyzeConflict _ _ =>
      match pr.1.successor with
      | some n => tagWalk fuel n pr.2 (steps+1) props decs (confl+1)
      | none => return (steps+1, props, decs, confl+1, false)
    | _ =>
      match pr.1.successor with
      | some n => tagWalk fuel n pr.2 (steps+1) props decs confl
      | none => return (steps+1, props, decs, confl, false)

def runTagWalk (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let props := lcgProps p
      let f0 : BranchFrame := { doms := p.domains, order := [] }
      let m0 := Frame.mass f0
      let (tPre, pre) ← timeIt (fun _ => presolveLoop props f0 (m0 + 1))
      say s!"TAGWALK {path} massBefore={m0} presolveMs={tPre/1000000} props={props.length}"
      match pre with
      | none => say s!"TAGWALK_RESULT {path} rootConflict"
      | some (g, n, sw) =>
          say s!"TAGWALK_RESULT {path} massAfter={Frame.mass g} applied={n} sweeps={sw}"
          let leaf := lcgLeaf p
          let cfg : SchedulerConfig leaf :=
            SchedulerConfig.init g.doms (LeanFzn.Compiler.seedClauses p.constraints) props
          let sched := PropScheduler.init props
          let (tW, r) ← timeItIO (fun _ => tagWalk fuel cfg sched 0 0 0 0)
          let stepsN := r.1
          let propsN := r.2.1
          let decsN := r.2.2.1
          let conflN := r.2.2.2.1
          let satB := r.2.2.2.2
          say s!"TAGWALK_WALK {path} steps={stepsN} propagates={propsN} decs={decsN} confl={conflN} sat={satB} walkMs={tW/1000000}"

/-- Sum the wall time of `n` applications of a pure action. The result is
forced inside each timed action (`timeIt`), so the compiler cannot elide it. -/
partial def timeReps {α : Type} (n : Nat) (act : Unit → α) (acc : Nat) : IO Nat := do
  match n with
  | 0 => return acc
  | n + 1 =>
    let (t, _) ← timeIt act
    timeReps n act (acc + t)

/-- The LAST slot with at least two integer values and one such value (a
high index makes the list-spine write cost visible). -/
private def pickIntSlot : List Domain → Nat → Option (Nat × Int)
  | [], _ => none
  | d :: rest, i =>
    let here :=
      match (Dom.enum d).filterMap LeanFzn.Semantics.Value.intView with
      | _ :: v :: _ => some (i, v)
      | _ => none
    match pickIntSlot rest (i + 1) with
    | some r => some r
    | none => here

/-- Frame-operation microbenchmark (P7 spike, TEST-ONLY, UNCERTIFIED): per-call
cost of the O(frame-width) list-spine operations on the actual root frame:
`Frame.mass`, `List.set` (the write used by `filterFrame`/`setSlot`), `pin`,
and `filterFrame` for one real value literal. Compare with the per-step
propagator-scan time from `--diag`. -/
def runFrames (reps : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let f : BranchFrame := { doms := p.domains, order := [] }
      match pickIntSlot f.doms 0 with
      | none => say s!"FRAMEPROBE {path} no-int-slot vars={f.doms.length}"
      | some (k, v) =>
        let d := f.doms.getD k Dom.empty
        let lit : Literal := { atom := .intNe k v, positive := true }
        let _ ← timeReps 50 (fun _ => Frame.mass f) 0
        let tMass ← timeReps reps (fun _ => Frame.mass f) 0
        let tSet ← timeReps reps (fun _ => f.doms.set k d) 0
        let tPin ← timeReps reps (fun _ => f.pin k (.int v)) 0
        let tFilter ← timeReps reps (fun _ => filterFrame lit f) 0
        say s!"FRAMEPROBE {path} vars={f.doms.length} domSum={Frame.mass f} slot={k} domLen={d.length} reps={reps} massNs={tMass/reps} setNs={tSet/reps} pinNs={tPin/reps} filterNs={tFilter/reps}"

/-- The widest root domain (the D2 target shape). -/
private def widestDomain (ds : List Domain) : Domain :=
  ds.foldl (fun b d => if d.length > b.length then d else b) Dom.empty

/-- `Dom` version of `aieSupportB`, the `arrayIntElementSlot` support arm
(the table entry at `idx` is present and lies in the target domain). -/
private def aieSupportDomB (xs : List Int) (kd : Dom) (idx : Int) : Bool :=
  match LeanFzn.Semantics.valuesGet1 (xs.map LeanFzn.Semantics.Value.int) idx with
  | some (.int e) => Dom.memBool kd (.int e)
  | _ => true

/-- Time `reps` Nat-valued calls, accumulating both the elapsed time and the
results. The result checksum is returned to the caller and printed, so the
timed computation cannot be dead-code-eliminated. -/
private partial def timeRepsVal (reps : Nat) (act : Unit → Nat)
    (accT accV : Nat) : IO (Nat × Nat) := do
  match reps with
  | 0 => return (accT, accV)
  | reps + 1 =>
    let (t, a) ← timeIt act
    timeRepsVal reps act (accT + t) (accV + a)

/-- A compact tag of a `Dom` (forces the representation without an `enum`). -/
private def domTag (d : Dom) : Nat :=
  match d.rep with
  | .small _ _ bits => bits.toNat
  | .holes lo _ _ => lo.toNat
  | .general vs => vs.length

/-- Opaque identity, so a timed `Dom.ofList (hideList d)` is not CSE'd with
an earlier `Dom.ofList d`. -/
@[noinline] private def hideList (l : List LeanFzn.Semantics.Value) :
    List LeanFzn.Semantics.Value := l

/-- The upper endpoint of a contiguous ascending integer run, if the whole
list is one. Linear in the list length. -/
private def contiguousInts? : List LeanFzn.Semantics.Value → Option (Int × Int)
  | [] => none
  | .int lo :: rest =>
      let rec go (prev : Int) : List LeanFzn.Semantics.Value → Option Int
        | [] => some prev
        | .int x :: tl => if x = prev + 1 then go x tl else none
        | _ => none
      match go lo rest with
      | some hi => some (lo, hi)
      | none => none
  | _ => none

/-- Linear construction of the compact form for a contiguous int range (the
`ofIntRange` shape the compiler can emit directly). -/
private def ofRangeFast? (d : List LeanFzn.Semantics.Value) : Option Dom :=
  match contiguousInts? d with
  | some (lo, hi) =>
      if 64 < hi - lo + 1 then some ⟨.holes lo hi []⟩ else none
  | none => none

/-- `aieSupportB` with the table's `Value.int` view precomputed once. -/
private def aieSupportDomV (tblV : List LeanFzn.Semantics.Value) (kd : Dom) (idx : Int) :
    Bool :=
  match LeanFzn.Semantics.valuesGet1 tblV idx with
  | some (.int e) => Dom.memBool kd (.int e)
  | _ => true

/-- P6 S0-utilization probe (TEST-ONLY, UNCERTIFIED): per-operation cost of the
legacy `List Value` domain against the frozen `CompactDomain.Dom` on the real
widest root domain of a compiled model. The `Pass` rows replay the
`arrayIntElementSlot` support arm: for every table index, test whether the
constant entry is in the target domain. `domPassConv` re-canonicalizes the
domain on every call (the convert-per-operation pilot); `domPass` amortizes
one `ofList`. `agree*` checks the two paths return identical counts (a
plumbing check, not a proof). -/
def runDomProbe (target : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let d := widestDomain p.domains
      let dl : List LeanFzn.Semantics.Value := Dom.enum d
      let dom := d
      let tbl : List Int := p.constraints.foldl (fun acc c =>
        match c with
        | .arrayIntElementSlot xs _ _ => if acc.isEmpty then xs else acc
        | _ => acc) []
      let idxs : List Int := (List.range (min 64 tbl.length)).map (fun (k : Nat) => (k : Int) + 1)
      let probes : List LeanFzn.Semantics.Value :=
        if tbl.isEmpty then
          (dl.take 8) ++ ((dl.drop (dl.length / 2)).take 4) ++ (dl.reverse.take 4)
        else
          (tbl.map LeanFzn.Semantics.Value.int).take 64
      let tblV : List LeanFzn.Semantics.Value := tbl.map LeanFzn.Semantics.Value.int
      let domFast : Option Dom := ofRangeFast? dl
      let domsDom : List Dom := p.domains.map (fun dk =>
        match ofRangeFast? (Dom.enum dk) with
        | some dd => dd
        | none => dk)
      let domsDomConv : List Dom := p.domains.map (fun dk =>
        match ofRangeFast? (hideList (Dom.enum dk)) with
        | some dd => dd
        | none => dk)
      let aieRootList : Nat :=
        p.constraints.foldl (fun acc c =>
          match c with
          | .arrayIntElementSlot xs i k =>
              let di := Dom.enum (p.domains.getD i Dom.empty)
              let dk := Dom.enum (p.domains.getD k Dom.empty)
              di.foldl (fun n v =>
                match v with
                | .int idx => n + (if aieSupportB xs dk idx then 1 else 0)
                | _ => n) acc
          | _ => acc) 0
      let aieRootDom (ds : List Dom) : Nat :=
        p.constraints.foldl (fun acc c =>
          match c with
          | .arrayIntElementSlot xs i k =>
              let di := Dom.enum (p.domains.getD i Dom.empty)
              let dk : Dom := ds.getD k default
              let xsV := xs.map LeanFzn.Semantics.Value.int
              di.foldl (fun n v =>
                match v with
                | .int idx => n + (if aieSupportDomV xsV dk idx then 1 else 0)
                | _ => n) acc
          | _ => acc) 0
      let domPass (dd : Dom) : Nat :=
        idxs.foldl (fun n idx => n + (if aieSupportDomB tbl dd idx then 1 else 0)) 0
      let lit : Literal :=
        match dl.reverse.head? with
        | some (.int v) => { atom := .intNe 0 v, positive := true }
        | _ => { atom := .intNe 0 0, positive := true }
      let xval : LeanFzn.Semantics.Value :=
        match dl.reverse.head? with
        | some v => v
        | none => .int 0
      let shape := match d.rep with
        | .small true _ _ => "bool"
        | .small false _ _ => "small"
        | .holes _ _ hs => s!"holes{hs.length}"
        | .general _ => "general"
      say s!"DOMPROBE_PRE {path} constraints={p.constraints.length} aie={p.constraints.foldl (fun n c => match c with | .arrayIntElementSlot _ _ _ => n + 1 | _ => n) 0} doms={domsDom.length} rootListChk={aieRootList} rootDomChk={aieRootDom domsDom}"
      let nMem := min 2000 (max 1 (target / max 1 (dl.length * max 1 probes.length)))
      let nPass := min 2000 (max 1 (target / max 1 (dl.length * max 1 idxs.length)))
      let nConv := min 2000 (max 1 (target / max 1 dl.length))
      let (tListMem, vListMem) ← timeRepsVal nMem (fun _ =>
        probes.foldl (fun n v =>
          n + (if LeanFzn.Solver.Propagation.DomainFiltering.valueMemB v dl then 1 else 0)) 0) 0 0
      let (tDomMem, vDomMem) ← timeRepsVal nMem (fun _ =>
        probes.foldl (fun n v => n + (if Dom.memBool dom v then 1 else 0)) 0) 0 0
      let (tListPass, vListPass) ← timeRepsVal nPass (fun _ =>
        idxs.foldl (fun n idx => n + (if aieSupportB tbl dl idx then 1 else 0)) 0) 0 0
      let (tDomPass, vDomPass) ← timeRepsVal nPass (fun _ =>
        idxs.foldl (fun n idx => n + (if aieSupportDomB tbl dom idx then 1 else 0)) 0) 0 0
      let (tDomPassConv, vDomPassConv) ← timeRepsVal nPass (fun _ =>
        domPass (Dom.ofList (hideList dl))) 0 0
      let (tDomPassConvFast, vDomPassConvFast) ← timeRepsVal nPass (fun _ =>
        match ofRangeFast? (hideList dl) with
        | some df => domPass df
        | none => 0) 0 0
      let (tDomPassPre, vDomPassPre) ← timeRepsVal nPass (fun _ =>
        idxs.foldl (fun n idx => n + (if aieSupportDomV tblV dom idx then 1 else 0)) 0) 0 0
      let (tDomPassFast, vDomPassFast) ← timeRepsVal nPass (fun _ =>
        match domFast with
        | some df => idxs.foldl (fun n idx => n + (if aieSupportDomV tblV df idx then 1 else 0)) 0
        | none => 0) 0 0
      let (tOfList, vOfList) ← timeRepsVal nConv (fun _ =>
        domTag (Dom.ofList (hideList dl))) 0 0
      let (tOfRange, vOfRange) ← timeRepsVal nConv (fun _ =>
        match ofRangeFast? (hideList dl) with
        | some df => domTag df
        | none => 0) 0 0
      let (tEnum, vEnum) ← timeRepsVal nConv (fun _ => (Dom.enum dom).length) 0 0
      let (tRootList, vRootList) ← timeRepsVal 2 (fun _ =>
        p.constraints.reverse.foldl (fun acc c =>
          match c with
          | .arrayIntElementSlot xs i k =>
              let di := Dom.enum (p.domains.getD i Dom.empty)
              let dk := Dom.enum (p.domains.getD k Dom.empty)
              di.foldl (fun n v =>
                match v with
                | .int idx => n + (if aieSupportB xs dk idx then 1 else 0)
                | _ => n) acc
          | _ => acc) 0) 0 0
      let (tRootDomPre, vRootDomPre) ← timeRepsVal 5 (fun _ =>
        aieRootDom domsDom.reverse.reverse) 0 0
      let (tRootDomConv, vRootDomConv) ← timeRepsVal 2 (fun _ =>
        aieRootDom domsDomConv) 0 0
      let (tListFilt, vListFilt) ← timeRepsVal nConv (fun _ => (dl.filter lit.valueHolds).length) 0 0
      let (tDomFilt, vDomFilt) ← timeRepsVal nConv (fun _ =>
        (Dom.enum (Dom.filterLit lit dom)).length) 0 0
      let (tDomFiltOnly, vDomFiltOnly) ← timeRepsVal nConv (fun _ =>
        domTag (Dom.filterLit lit dom)) 0 0
      let (tListRem, vListRem) ← timeRepsVal nConv (fun _ =>
        (dl.filter (fun v => !(v.eqB xval))).length) 0 0
      let (tDomRem, vDomRem) ← timeRepsVal nConv (fun _ =>
        (Dom.enum (Dom.removeVal xval dom)).length) 0 0
      let (tDomRemOnly, vDomRemOnly) ← timeRepsVal nConv (fun _ =>
        domTag (Dom.removeVal xval dom)) 0 0
      say s!"DOMPROBE {path} vars={p.domains.length} domSum={p.domains.foldl (fun a d => a + d.length) 0} widest={dl.length} shape={shape} card={Dom.card dom} tableN={tbl.length} enumEq={(Dom.enum dom == dl)} agreeMem={(vListMem / nMem == vDomMem / nMem)} agreePass={(vListPass / nPass == vDomPass / nPass)} agreeFilt={(vListFilt / nConv == vDomFilt / nConv)} agreeRem={(vListRem / nConv == vDomRem / nConv)} chk={vListMem+vDomMem+vListPass+vDomPass+vDomPassConv+vDomPassConvFast+vDomPassPre+vDomPassFast+vOfList+vOfRange+vEnum+vListFilt+vDomFilt+vDomFiltOnly+vListRem+vDomRem+vDomRemOnly} contig={domFast.isSome} listMemNs={tListMem / nMem} domMemNs={tDomMem / nMem} listPassNs={tListPass / nPass} domPassNs={tDomPass / nPass} domPassConvNs={tDomPassConv / nPass} domPassConvFastNs={tDomPassConvFast / nPass} domPassPreNs={tDomPassPre / nPass} domPassFastNs={tDomPassFast / nPass} ofListNs={tOfList / nConv} ofRangeNs={tOfRange / nConv} enumNs={tEnum / nConv} listFiltNs={tListFilt / nConv} domFiltNs={tDomFilt / nConv} domFiltOnlyNs={tDomFiltOnly / nConv} listRemNs={tListRem / nConv} domRemNs={tDomRem / nConv} domRemOnlyNs={tDomRemOnly / nConv} rootListNs={tRootList / 2} rootDomConvNs={tRootDomConv / 2} rootDomPreNs={tRootDomPre / 5} agreeRoot={(vRootList / 2 == vRootDomPre / 5)} reps={nMem}/{nPass}/{nConv}"

/-- Stripped lists are vacuously locally sound (no member declares a footprint). -/
theorem stripWatches_local (props : List Propagator) :
    PropLocal (props.map fun p => { p with watches := [] }) := by
  intro p hp hne
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  simp at hne

/-- The scheduled entry over the stripped (no-footprint) propagator list. -/
def lcgRunSchedNoWatch (p : CompiledProblem
    LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint)
    (hroute : lcgRouteGateMixed p = true) :
    DriverResult (lcgLeaf p) :=
  let props := LeanFzn.Integration.lcgProps p |>.map (fun q => { q with watches := [] })
  solve_sched p.domains (LeanFzn.Compiler.seedClauses p.constraints) props
    (LeanFzn.Integration.lcgSeedEntailed p) (PropScheduler.init props)
    (stripWatches_local _) (PropSchedulerOK.init props)
    (LcgHarness.frameGate_of_routeGate hroute)

/-- Direct ablation: the scheduled route vs the same route with every
declared watch footprint stripped (same binary, same foundations). -/
def runAblate (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      if hroute : lcgRouteGateMixed p = true then
        let (t1, r1) ← timeIt (fun _ => lcgRun p (LcgHarness.frameGate_of_routeGate hroute))
        let (t2, r2) ← timeIt (fun _ => lcgRunSchedNoWatch p hroute)
        let (t3, r3) ← timeIt (fun _ => LcgHeur.lcgRunHeur p (LcgHeur.heurFrameGate hroute))
        let vt {leaf : Assignment → Bool} (r : DriverResult leaf) : Nat :=
          match r with | .sat _ => 1 | .unsat => 2
        say s!"ABLATE {path} watchMs={t1/1000000} noWatchMs={t2/1000000} heurMs={t3/1000000} tags={vt r1}/{vt r2}/{vt r3}"
      else
        say s!"ABLATE {path} NOT ROUTED (gate off)"

/-! ## 5. Mode: `--watch` / `--watch-battery` (oracle vs self-validating scan)

On the REAL `(frame, db)` pair of every active step of the wired dispatcher
walk, this mode times `scanDatabaseFast` (the wired oracle) against the
self-validating watched scan `scanDatabaseWatch2` (threaded across steps),
compares the two events exactly, and accumulates the per-scan work counters
(skips / rechecks / classifies) and oracle-vs-watched times in total and for
large databases (`db.length ≥ 256`). `setupNs` is the wrapper's only per-scan
setup (`frameDomainArray f` + `sumsOfArray`). TEST-ONLY, UNCERTIFIED. -/

structure WAcc where
  steps : Nat := 0
  active : Nat := 0
  oracleNs : Nat := 0
  watchNs : Nat := 0
  setupNs : Nat := 0
  disagree : Nat := 0
  skips : Nat := 0
  rechecks : Nat := 0
  classifies : Nat := 0
  establishes : Nat := 0
  dbSum : Nat := 0
  dbMax : Nat := 0
  bigSteps : Nat := 0
  bigOracleNs : Nat := 0
  bigWatchNs : Nat := 0
  versNs : Nat := 0
  vdisagree : Nat := 0
  vresets : Nat := 0
  bigVersNs : Nat := 0
  vsyncNs : Nat := 0
  vskips : Nat := 0
  vrechecks : Nat := 0
  vclassifies : Nat := 0

def WAcc.add (a b : WAcc) : WAcc :=
  { steps := a.steps + b.steps, active := a.active + b.active,
    oracleNs := a.oracleNs + b.oracleNs, watchNs := a.watchNs + b.watchNs,
    setupNs := a.setupNs + b.setupNs, disagree := a.disagree + b.disagree,
    skips := a.skips + b.skips, rechecks := a.rechecks + b.rechecks,
    classifies := a.classifies + b.classifies, establishes := a.establishes + b.establishes,
    dbSum := a.dbSum + b.dbSum, dbMax := max a.dbMax b.dbMax,
    bigSteps := a.bigSteps + b.bigSteps,
    bigOracleNs := a.bigOracleNs + b.bigOracleNs, bigWatchNs := a.bigWatchNs + b.bigWatchNs,
    versNs := a.versNs + b.versNs, vdisagree := a.vdisagree + b.vdisagree,
    vresets := a.vresets + b.vresets, bigVersNs := a.bigVersNs + b.bigVersNs,
    vsyncNs := a.vsyncNs + b.vsyncNs,
    vskips := a.vskips + b.vskips, vrechecks := a.vrechecks + b.vrechecks,
    vclassifies := a.vclassifies + b.vclassifies }

/-- Exact event comparison (both sides carry the same payloads when equal). -/
def evEq (a b : PruningEvent) : Bool :=
  match a, b with
  | .stable, .stable => true
  | .conflict xs, .conflict ys => xs == ys
  | .implied l c lr fl, .implied l' c' lr' fl' =>
      l == l' && c == c' && (lr == lr') && (fl == fl')
  | _, _ => false

/-- Measure one active step: time the wired oracle and the corrected watched
scan on the REAL `(frame, db)`, compare the events exactly, accumulate the
counters, and thread the updated watch index. -/
def measureActive {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (idx : WatchIndex) (vst : VersionWatch) (acc : WAcc) :
    IO (WAcc × WatchIndex × VersionWatch) := do
  let f := cfg.branch.frame
  let db := cfg.branch.learned
  let reset := decide (db.length ≠ vst.dbLen)
  let (to, eo) ← timeIt (fun _ => scanDatabaseFast cfg.original f db)
  let (tg, _) ← timeIt (fun _ => sumsOfArray (frameDomainArray f))
  let (tw, ew) ← timeIt (fun _ => scanDatabaseWatch2 cfg.original f idx db)
  let (ts, _) ← timeIt (fun _ => vst.sync f)
  let (tv, ev) ← timeIt (fun _ => scanDatabaseWatchVPrepend cfg.original f vst db)
  let w := ew.2.work
  let big := decide (256 ≤ db.length)
  return ({ acc with
    active := acc.active + 1,
    oracleNs := acc.oracleNs + to, watchNs := acc.watchNs + tw,
    versNs := acc.versNs + tv, setupNs := acc.setupNs + tg,
    disagree := acc.disagree + (if evEq eo ew.1 then 0 else 1),
    vdisagree := acc.vdisagree + (if evEq eo ev.1 then 0 else 1),
    vresets := acc.vresets + (if reset then 1 else 0),
    skips := acc.skips + w.skips, rechecks := acc.rechecks + w.rechecks,
    classifies := acc.classifies + w.classifies,
    establishes := acc.establishes + w.establishes,
    dbSum := acc.dbSum + db.length, dbMax := max acc.dbMax db.length,
    bigSteps := acc.bigSteps + (if big then 1 else 0),
    bigOracleNs := acc.bigOracleNs + (if big then to else 0),
    bigWatchNs := acc.bigWatchNs + (if big then tw else 0),
    bigVersNs := acc.bigVersNs + (if big then tv else 0),
    vsyncNs := acc.vsyncNs + ts,
    vskips := acc.vskips + ev.2.work.skips,
    vrechecks := acc.vrechecks + ev.2.work.rechecks,
    vclassifies := acc.vclassifies + ev.2.work.classifies },
    ew.2, ev.2)

partial def walkWatch {leaf : Assignment → Bool} (fuel : Nat) (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (idx : WatchIndex) (vst : VersionWatch) (acc : WAcc) :
    IO WAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let (acc, idx, vst) ←
      if cfg.conflict.isNone && cfg.status == .active then measureActive cfg idx vst acc
      else pure (acc, idx, vst)
    let pr := phaseNextSched cfg sched
    let acc := { acc with steps := acc.steps + 1 }
    match pr.1 with
    | .sat _ => return acc
    | .unsat => return acc
    | _ =>
        match pr.1.successor with
        | some n => walkWatch fuel n pr.2 idx vst acc
        | none => return acc

/-- Walk the public heuristic configuration of `p` with the oracle-vs-watched
measurement active at every active step. -/
def watchProblem (p : CompiledProblem LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint)
    (fuel : Nat) : IO WAcc := do
  let hd := LcgHeur.heurDomains p
  let props := LcgHeur.heurProps p
  let leaf := lcgLeaf p
  let cfg : SchedulerConfig leaf :=
    SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
  walkWatch fuel cfg (PropScheduler.init props) WatchIndex.init (VersionWatch.init cfg.branch.frame) {}

def reportWatch (name : String) (a : WAcc) : IO Unit := do
  let ms (x : Nat) : Nat := x / 1000000
  let us (x : Nat) (n : Nat) : Nat := if n == 0 then 0 else x / 1000 / n
  say s!"WATCH {name} steps={a.steps} active={a.active} oracleMs={ms a.oracleNs} \
watchMs={ms a.watchNs} setupMs={ms a.setupNs} disagree={a.disagree}"
  say s!"WATCHWORK {name} skips={a.skips} rechecks={a.rechecks} classifies={a.classifies} \
establishes={a.establishes} dbSum={a.dbSum} dbMax={a.dbMax}"
  say s!"WATCHBIG {name} bigSteps={a.bigSteps} oracleMs={ms a.bigOracleNs} watchMs={ms a.bigWatchNs} \
oracleUsPer={us a.bigOracleNs a.bigSteps} watchUsPer={us a.bigWatchNs a.bigSteps}"
  say s!"WATCHV {name} versMs={ms a.versNs} vdisagree={a.vdisagree} vresets={a.vresets} \
versUsPer={us a.versNs a.active} bigVersMs={ms a.bigVersNs} \
bigVersUsPer={us a.bigVersNs a.bigSteps}"
  say s!"WATCHVWORK {name} vskips={a.vskips} vrechecks={a.vrechecks} vclassifies={a.vclassifies} \
vsyncMs={ms a.vsyncNs} vsyncUsPer={us a.vsyncNs a.active}"

/-- `--watch BOUND FUEL FILE...`: the bounded heuristic configuration of each
file, walked with the oracle-vs-watched measurement. -/
def runWatchOpt (bound : Int) (fuel : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    match LeanFzn.Compiler.compileModelOpt m with
    | .error e => say s!"FILE {path} compileOpt=ERROR {e.take 120}"
    | .ok (po, spec) =>
      let p2 := curP po spec (some bound)
      let t0 ← IO.monoNanosNow
      let a ← watchProblem p2 fuel
      let t1 ← IO.monoNanosNow
      say s!"WALLWATCH {path} bound={bound} ms={(t1 - t0) / 1000000}"
      reportWatch path a

/-- `--watch-battery FUEL`: the 43-instance harness battery, each walked with
the oracle-vs-watched measurement. -/
def runWatchBattery (fuel : Nat) : IO Unit := do
  let mut tot : WAcc := {}
  for (name, src) in LcgHarness.battery do
    match LcgHarness.ofSource name src with
    | .error e => IO.eprintln s!"{name}: {e}"
    | .ok inst =>
        match inst.compiled with
        | none => pure ()
        | some p =>
            let a ← watchProblem p fuel
            reportWatch name a
            tot := tot.add a
  reportWatch "BATTERY-TOTAL" tot

/-! ## 6. Mode: `--diagk3` -- the watched-clause scan candidate, before/after
in one binary (TEST-ONLY, UNCERTIFIED; PLAN task K3)

The watched scan measured a NO-GO on the K3 panel (the candidate was slower in
`promptNs` on every learned-heavy panel file; see the K3 report under
`tmp/k3/`), so the production `nextPruningEventSched` keeps the indexed
`scanDatabaseFast`. This mode runs the SAME step loop twice on the same
instance from a fresh scheduler and the same fuel:

* *before* -- the default route (`promptOf` -> `scanDatabaseFast`);
* *after*  -- the watched candidate (`promptOfWatchProbe`, a test-only twin
  with the K3 wiring: `scanDatabaseWatch2` and its `WatchIndex` threaded
  through the returned scheduler).

At every step it also times `scanDatabaseFast` and `scanDatabaseWatch2` on the
SAME `(frame, db, sched.watch)` the step uses, compares the two events exactly
(0 disagreements is the `scanDatabaseWatch2_fst_eq_fast` check), and
accumulates the watched scan's `WatchWork` counters. The counters and the scan
times are restricted to steps whose prompt actually takes the stamp path; the
queued E1 branch is untouched by K3 and shows up as `queueSteps`. -/

/-- The K3 watched candidate: identical to the old `nextPruningEventSched`
wiring, with `scanDatabaseWatch2` in the stamp branch and the returned
`WatchIndex` threaded into every arm. TEST-ONLY twin used for the `--diagk3`
before/after measurement. -/
def nextPruningEventSchedWatchProbe (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  let q := scanDatabaseWatch2 original f sched.watch db
  match q.1 with
  | .stable =>
      if frameViewedB f then
        scanPropagatorsSched f { sched with watch := q.2 } props
      else (.stable, { sched with watch := q.2 })
  | .conflict cs => (.conflict cs, { sched with watch := q.2 })
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then
        (.implied l c learnReason fromLearned, { sched with watch := q.2 })
      else (.stable, { sched with watch := q.2 })

/-- The `promptOf` policy switch with the watched candidate in the stamp
branch. -/
def promptOfWatchProbe (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  if queuePolicy props f then
    nextPruningEventQueuedSched original props sched f db
  else
    nextPruningEventSchedWatchProbe original props sched f db

/-- The active dispatch twin (verbatim `schedulerNextSchedActive` with
`promptOfWatchProbe`). -/
def schedulerNextSchedActiveWatchProbe {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  match promptOfWatchProbe cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned with
  | (ev, sched') =>
      (match explainedDeductionOf cfg.original cfg.props cfg.branch ev with
       | some d => .propagate (stepPropagate cfg d)
       | none =>
           match terminalResultOf cfg.orig cfg.original cfg.props cfg.branch ev with
           | .stable _ => stableStepGuarded cfg
           | .conflict _ cs learned => conflictStepFast cfg cs learned
           | .localExcluded _ _ _ learned =>
               .localExclude (stepLocalExclude cfg learned (branchRegion cfg)),
       sched')

/-- The dispatch twin (verbatim `schedulerNextSched` with the watched
candidate). -/
def schedulerNextSchedWatchProbe {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  match cfg.conflict with
  | some ev => (backjumpStepFast cfg ev, sched)
  | none =>
      match cfg.status with
      | .dead => (consumeStep cfg, sched)
      | .active => schedulerNextSchedActiveWatchProbe cfg sched

/-- The phase dispatcher twin (verbatim `phaseNextSched` with the watched
candidate). -/
def phaseNextSchedWatchProbe {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  let pr := schedulerNextSchedWatchProbe cfg sched
  (phaseResolve cfg pr.1, pr.2)

/-- Per-run accumulator of the `--diagk3` before/after walk. -/
structure K3Acc where
  steps : Nat := 0
  promptNs : Nat := 0
  stepNs : Nat := 0
  dbNs : Nat := 0
  watchNs : Nat := 0
  stampSteps : Nat := 0
  queueSteps : Nat := 0
  probeSteps : Nat := 0
  disagree : Nat := 0
  skips : Nat := 0
  rechecks : Nat := 0
  classifies : Nat := 0
  establishes : Nat := 0
  dbSum : Nat := 0
  dbMax : Nat := 0
  learnedMax : Nat := 0
  sig : Nat := 0

/-- One bounded walk of the same dispatcher loop in the default (`fastMode`) or
watched-candidate mode, with the two scans probed and compared at every step. -/
partial def k3walk {leaf : Assignment → Bool} (fuel : Nat) (fastMode : Bool)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) (acc : K3Acc) : IO K3Acc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let f := cfg.branch.frame
    let db := cfg.branch.learned
    let active := cfg.conflict.isNone && cfg.status == .active
    let stamp := active && !queuePolicy cfg.props f
    let (tp, _) ← timeIt (fun _ =>
      if fastMode then promptOf cfg.original cfg.props sched f db
      else promptOfWatchProbe cfg.original cfg.props sched f db)
    -- probes exactly on the steps whose prompt takes the stamp path
    let (tdb, eo, tw, ew) ←
      if stamp then do
        let (tdb, eo) ← timeIt (fun _ => scanDatabaseFast cfg.original f db)
        let (tw, ew) ← timeIt (fun _ => scanDatabaseWatch2 cfg.original f sched.watch db)
        pure (tdb, eo, tw, ew)
      else pure (0, PruningEvent.stable, 0, (PruningEvent.stable, WatchIndex.init))
    let w := ew.2.work
    let (tstep, pr) ← timeIt (fun _ =>
      if fastMode then phaseNextSched cfg sched else phaseNextSchedWatchProbe cfg sched)
    let code : Nat :=
      match pr.1 with
      | .propagate _ => 1
      | .analyzeConflict _ _ => 2
      | .learnBackjumpAssert _ _ _ => 3
      | .chronologicalFallback _ => 4
      | .decide _ _ => 5
      | .localExclude _ => 6
      | .sat _ => 7
      | .unsat => 8
    let acc : K3Acc :=
      { acc with
        steps := acc.steps + 1,
        promptNs := acc.promptNs + tp, stepNs := acc.stepNs + tstep,
        dbNs := acc.dbNs + (if stamp then tdb else 0),
        watchNs := acc.watchNs + (if stamp then tw else 0),
        stampSteps := acc.stampSteps + (if stamp then 1 else 0),
        queueSteps := acc.queueSteps + (if active && !stamp then 1 else 0),
        probeSteps := acc.probeSteps + (if stamp then 1 else 0),
        disagree := acc.disagree + (if stamp then (if evEq eo ew.1 then 0 else 1) else 0),
        skips := acc.skips + (if stamp then w.skips else 0),
        rechecks := acc.rechecks + (if stamp then w.rechecks else 0),
        classifies := acc.classifies + (if stamp then w.classifies else 0),
        establishes := acc.establishes + (if stamp then w.establishes else 0),
        dbSum := acc.dbSum + db.length, dbMax := max acc.dbMax db.length,
        learnedMax := max acc.learnedMax db.length,
        sig := acc.sig * 7 + code }
    match pr.1 with
    | .sat _ => return acc
    | .unsat => return acc
    | _ =>
      match pr.1.successor with
      | some nxt => k3walk fuel fastMode nxt pr.2 acc
      | none => return acc

/-- `--diagk3 FUEL FILE...`: run the before/after walks and report both. The
`reverse` flag swaps their order (the first walk of a process pays the warmup),
so `--diagk3` and `--diagk3r` bound the ordering bias. -/
def runDiagK3 (fuel : Nat) (path : String) (reverse : Bool) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let hd := LcgHeur.heurDomains p
      let props := LcgHeur.heurProps p
      let leaf := lcgLeaf p
      let cfg : SchedulerConfig leaf :=
        SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
      let sched0 := PropScheduler.init props
      let (before, after, tb, ta) ←
        if reverse then do
          let t0 ← IO.monoNanosNow
          let a ← k3walk fuel false cfg sched0 {}
          let t1 ← IO.monoNanosNow
          let b ← k3walk fuel true cfg sched0 {}
          let t2 ← IO.monoNanosNow
          pure (b, a, t2 - t1, t1 - t0)
        else do
          let t0 ← IO.monoNanosNow
          let b ← k3walk fuel true cfg sched0 {}
          let t1 ← IO.monoNanosNow
          let a ← k3walk fuel false cfg sched0 {}
          let t2 ← IO.monoNanosNow
          pure (b, a, t1 - t0, t2 - t1)
      let per (x n : Nat) : Nat := if n == 0 then 0 else x / n
      let ratio (a b : Nat) : Nat := if b == 0 then 0 else 1000 * a / b
      let scanTotal := after.skips + after.rechecks + after.classifies
      say s!"DIAGK3 {path} steps={after.steps} beforeSteps={before.steps} \
sig={before.sig}/{after.sig} walkBeforeMs={tb/1000000} walkAfterMs={ta/1000000} \
queueRoot={queuePolicy props cfg.branch.frame}"
      say s!"DIAGK3NS {path} beforeStepNs={per before.stepNs before.steps} \
beforePromptNs={per before.promptNs before.steps} afterStepNs={per after.stepNs after.steps} \
afterPromptNs={per after.promptNs after.steps} stepPermille={ratio after.stepNs before.stepNs} \
promptPermille={ratio after.promptNs before.promptNs}"
      say s!"DIAGK3SCAN {path} stampSteps={after.stampSteps} queueSteps={after.queueSteps} \
probeSteps={after.probeSteps} dbNs={per after.dbNs after.stampSteps} \
watchNs={per after.watchNs after.stampSteps} dbSum={after.dbSum} dbMax={after.dbMax} \
learnedMax={after.learnedMax} disagree={after.disagree}"
      say s!"DIAGK3WORK {path} skips={after.skips} rechecks={after.rechecks} \
classifies={after.classifies} establishes={after.establishes} \
skipPct={if scanTotal == 0 then 0 else 100 * after.skips / scanTotal} \
watchUsPer={if after.stampSteps == 0 then 0 else after.watchNs / 1000 / after.stampSteps}"
      say s!"DIAGK3BEFORE {path} skips={before.skips} rechecks={before.rechecks} \
classifies={before.classifies} dbNs={per before.dbNs before.stampSteps} \
watchNs={per before.watchNs before.stampSteps}"

def run (args : List String) : IO UInt32 := do
  match args with
  | "--ablate" :: files =>
    for path in files do
      runAblate path
    return 0
  | "--watch-battery" :: fuelS :: _ =>
    runWatchBattery (fuelS.toNat?.getD 400000)
    return 0
  | "--watch" :: boundS :: fuelS :: files =>
    let bound := Int.ofNat (boundS.toNat?.getD 0)
    let fuel := fuelS.toNat?.getD 1000000
    for path in files do
      runWatchOpt bound fuel path
    return 0
  | "--opt" :: boundS :: fuelS :: samplesS :: files =>
    let bound := Int.ofNat (boundS.toNat?.getD 0)
    let fuel := fuelS.toNat?.getD 1000000
    let samples := samplesS.toNat?.getD 0
    for path in files do
      runOpt bound fuel samples path
    return 0
  | "--diag" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiag false fuel path
    return 0
  | "--diagk2" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiag true fuel path
    return 0
  | "--diagk3" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiagK3 fuel path false
    return 0
  | "--diagk3r" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiagK3 fuel path true
    return 0
  | "--diagbatch" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiagBatch fuel path
    return 0
  | "--diagsplit" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiagSplit fuel path
    return 0
  | "--diagsync" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 100
    for path in files do
      runDiagSync fuel path
    return 0
  | "--presolve" :: files =>
    for path in files do
      runPresolve path
    return 0
  | "--nodeclose" :: files =>
    for path in files do
      runNodeClose path
    return 0
  | "--tagwalk" :: fuelS :: files =>
    let fuel := fuelS.toNat?.getD 3000
    for path in files do
      runTagWalk fuel path
    return 0
  | "--frames" :: repsS :: files =>
    let reps := repsS.toNat?.getD 1000
    for path in files do
      runFrames reps path
    return 0
  | "--domprobe" :: targetS :: files =>
    let target := targetS.toNat?.getD 20000000
    for path in files do
      runDomProbe target path
    return 0
  | fuelS :: samplesS :: files =>
    let fuel := fuelS.toNat?.getD 12
    let samples := samplesS.toNat?.getD 5
    for path in files do
      let src ← IO.FS.readFile path
      let t0 ← IO.monoNanosNow
      match LeanFzn.Parser.parseModel src with
      | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
      | .ok m =>
        let t1 ← IO.monoNanosNow
        let wf := LeanFzn.Checker.wellFormedFastB m
        let ms := { m with solve := .satisfy [] }
        match LeanFzn.Compiler.compileModelFull ms with
        | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
        | .ok p =>
          let t2 ← IO.monoNanosNow
          let domSum := p.domains.foldl (fun a d => a + d.length) 0
          let domMax := p.domains.foldl (fun a d => max a d.length) 0
          let (tHeur, hd) ← timeIt (fun _ => LcgHeur.heurDomains p)
          let (tDc, dcL) ← timeIt (fun _ => LcgHeur.dcConsts p.constraints)
          let (tPin, pinSum) ← timeIt (fun _ =>
            (Dom.enum (hd.getD 0 Dom.empty)).foldl (fun a w => a +
              match LcgHeur.valAct p.constraints (LcgHeur.actDb p) 0 w with
              | n => n) 0)
          let props := LcgHeur.heurProps p
          let propCls := p.constraints.filterMap propagatorOfProved
          let watches := propCls.foldl (fun a pr => a + pr.watches.length) 0
          let propTag (pr : Propagator) : String :=
            if pr.watches.isEmpty then "nowatch" else s!"w{pr.watches.length}"
          let tags := propCls.map propTag
          let leaf := lcgLeaf p
          let cfg : SchedulerConfig leaf :=
            SchedulerConfig.init hd (LeanFzn.Compiler.seedClauses p.constraints) props
          let sched := PropScheduler.init props
          let t3 ← IO.monoNanosNow
          let acc ← walk samples fuel cfg sched { jumpMax := 4 }
          let t4 ← IO.monoNanosNow
          say s!"FILE {path} wf={wf} parseMs={(t1-t0)/1000000} compileMs={(t2-t1)/1000000}"
          say s!"HEUR {path} heurMs={tHeur/1000000} dcMs={tDc/1000000} dcN={dcL.length} pinSum={pinSum} pinMs={tPin/1000000} domSum={domSum} domMax={domMax}"
          say s!"PROPS {path} props={props.length} watches={watches} tags={tags}"
          say s!"FAMS {path} all={famHist p.constraints} prop={propFamHist p.constraints}"
          say s!"WALK {path} steps={acc.steps} propagates={acc.propagates} sampled={acc.sampled} active={acc.active} dbSize={acc.dbSize} walkMs={(t4-t3)/1000000}"
          let per (x : Nat) : String := if acc.steps == 0 then "-" else s!"{x/acc.steps}"
          let perS (x : Nat) : String := if acc.sampled == 0 then "-" else s!"{x/acc.sampled}"
          say s!"TIME {path} stepPerStepNs={per acc.stepMs} frame={perS acc.frameMs} viewed={perS acc.viewedMs} mass={perS acc.massMs} dbScan={perS acc.dbScanMs} propScan={perS acc.propScanMs} propRun={perS acc.propRunMs} prompt={perS acc.promptMs}"
          let share (x : Nat) : String :=
            if acc.stepMs == 0 then "-" else s!"{100 * x / acc.stepMs}%"
          say s!"SHARE {path} propRun={share acc.propRunMs} propScan={share acc.propScanMs} prompt={share acc.promptMs} viewed={share acc.viewedMs} mass={share acc.massMs} frame={share acc.frameMs} dbScan={share acc.dbScanMs}"
    return 0
  | _ =>
    IO.eprintln "usage: tests_heur_timing FUEL SAMPLES FILE..."
    return 2

end Tests.E1.HeurTiming

def main (args : List String) : IO UInt32 := Tests.E1.HeurTiming.run args
