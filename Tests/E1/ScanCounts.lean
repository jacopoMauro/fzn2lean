/-
File: Tests/E1/ScanCounts.lean

Purpose (PLAN task E1, TEST-ONLY, UNCERTIFIED): measured COUNT evidence for the
hotspot ranking, plus unit-cost microbenchmarks, for the search engine the
public route runs (`phaseNext`).

Because `perf` is unavailable in this container, the count evidence is produced
by a *counting twin* of the dispatch's scan layer: verbatim copies of
`literalImpossible`, `clauseRemaining`, `productive`, `scanDatabase`,
`scanPropagators`, `frameViewedB`, `frameLiveB` and `nextPruningEvent`
(`LeanFzn.Solver.Propagation.Pruning` / `ClausePropagation`) that increment
counters instead of returning early on nothing. The twin is evaluated on the
REAL configurations visited by a REAL bounded `phaseNext` run, and the number
of scan invocations per step is derived from the REAL transition the dispatcher
took (`schedulerNext`/`phaseNext` runs `nextPruningEvent` once via
`explainedDeduction` and a second time via `terminalResult` exactly when no
productive deduction exists — i.e. exactly when the step is not `.propagate`).

Nothing in `LeanFzn/**` is modified; the counts are exact for the copied
recursion (same evaluation order, same `List.all` short-circuiting) because the
copies are char-for-char the real bodies with a counter threaded through.

It also times the REAL `scanDatabase` / `scanPropagators` / `Frame.mass` /
`frameViewedB` on a synthetic but realistic frame/database (20 slots x 8 values,
64 clauses, 48 registered propagators) to obtain ns-per-unit costs, so the
counts can be converted into an estimated time share (method notes in the
results file).

Run: lake env lean --run Tests/E1/ScanCounts.lean [--fuzz N SEED] [--repeat K] [FILE...]
-/
import Tests.UIP.LcgHarnessBattery
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP
open LeanFzn.Compiler LeanFzn.Integration
open LeanFzn LeanFzn.Solver LeanFzn.Solver.UIP.C3b LeanFzn.Solver.Core

namespace Tests.E1

/-! ## 1. Counting twin of the scan layer (verbatim recursion + counters) -/

/-- Counts of elementary operations performed by the dispatch's scan layer. -/
structure ScanCost where
  /-- `nextPruningEvent` invocations. -/
  nextPruningCalls : Nat := 0
  /-- `scanDatabase` invocations. -/
  dbScans : Nat := 0
  /-- clause evaluations inside `scanDatabase`. -/
  dbClausesVisited : Nat := 0
  /-- `clauseRemaining` invocations (one per visited clause, plus the unit re-check). -/
  dbClauseRemaining : Nat := 0
  /-- value tests inside `literalImpossible` (including `.all` short-circuit). -/
  dbLiteralValueChecks : Nat := 0
  /-- `scanPropagators` invocations. -/
  propScans : Nat := 0
  /-- propagator `run` calls. -/
  propVisits : Nat := 0
  /-- `frameViewedB` invocations (each scans every value of every remaining domain). -/
  frameViewedCalls : Nat := 0
  frameViewedValueChecks : Nat := 0
  /-- `frameLiveB` invocations (each scans every remaining domain). -/
  frameLiveCalls : Nat := 0
  frameLiveSlots : Nat := 0
  /-- `productive` invocations and the `filterFrame`/`Frame.mass` work inside. -/
  productiveCalls : Nat := 0
  productiveFilterFrameCalls : Nat := 0
  productiveFilterFrameValueChecks : Nat := 0
  productiveMassCalls : Nat := 0
  productiveMassSlots : Nat := 0
  /-- per-event extras of `explainedDeduction`/`terminalResult` on `.implied`. -/
  impliedEventExtras : Nat := 0
  trailEntriesScanned : Nat := 0   -- `TrailRedundant` + `wipeoutClause` entry scans
  dbMembershipChecks : Nat := 0    -- `learned.contains c` clause scans
  dbMembershipClauses : Nat := 0
  /-- frame-restore work on jump/consume transitions (`restoreNarrow`+`syncAll`). -/
  restoreSyncCalls : Nat := 0

def ScanCost.add (a b : ScanCost) : ScanCost :=
  { nextPruningCalls := a.nextPruningCalls + b.nextPruningCalls
    dbScans := a.dbScans + b.dbScans
    dbClausesVisited := a.dbClausesVisited + b.dbClausesVisited
    dbClauseRemaining := a.dbClauseRemaining + b.dbClauseRemaining
    dbLiteralValueChecks := a.dbLiteralValueChecks + b.dbLiteralValueChecks
    propScans := a.propScans + b.propScans
    propVisits := a.propVisits + b.propVisits
    frameViewedCalls := a.frameViewedCalls + b.frameViewedCalls
    frameViewedValueChecks := a.frameViewedValueChecks + b.frameViewedValueChecks
    frameLiveCalls := a.frameLiveCalls + b.frameLiveCalls
    frameLiveSlots := a.frameLiveSlots + b.frameLiveSlots
    productiveCalls := a.productiveCalls + b.productiveCalls
    productiveFilterFrameCalls := a.productiveFilterFrameCalls + b.productiveFilterFrameCalls
    productiveFilterFrameValueChecks := a.productiveFilterFrameValueChecks + b.productiveFilterFrameValueChecks
    productiveMassCalls := a.productiveMassCalls + b.productiveMassCalls
    productiveMassSlots := a.productiveMassSlots + b.productiveMassSlots
    impliedEventExtras := a.impliedEventExtras + b.impliedEventExtras
    trailEntriesScanned := a.trailEntriesScanned + b.trailEntriesScanned
    dbMembershipChecks := a.dbMembershipChecks + b.dbMembershipChecks
    dbMembershipClauses := a.dbMembershipClauses + b.dbMembershipClauses
    restoreSyncCalls := a.restoreSyncCalls + b.restoreSyncCalls }

/-- Verbatim `literalImpossible` + value-check counter. Returns
`(impossible, valueChecks)`. -/
def litImpossibleC (f : BranchFrame) (l : Literal) : Bool × Nat :=
  let vs := Dom.enum ((Frame.domains f).getD l.atom.slot Dom.empty)
  (vs.all (fun v => !l.valueHolds v), vs.length)

/-- Verbatim `clauseRemaining` + counters. Returns
`(remaining, clauseRemainingCalls, literalValueChecks)`. -/
def clauseRemainingC (f : BranchFrame) (c : Clause) : Clause × Nat × Nat :=
  let opts := c.map (litImpossibleC f)
  ((c.zip opts).filterMap (fun (l, o) => if o.1 then none else some l),
   c.length, opts.foldl (fun a p => a + p.2) 0)

/-- Total number of values in `Frame.domains f` (length of its flattening). -/
def frameValueCount (f : BranchFrame) : Nat :=
  (Frame.domains f).foldl (fun a d => a + d.length) 0

/-- Verbatim `productive` + `filterFrame`/`Frame.mass` counters. -/
def productiveC (l : Literal) (f : BranchFrame) : Bool × ScanCost :=
  match filterFrame l f with
  | none => (true, { productiveCalls := 1, productiveFilterFrameCalls := 1,
                     productiveFilterFrameValueChecks := frameValueCount f })
  | some g =>
    (decide (Frame.mass g < Frame.mass f),
     { productiveCalls := 1, productiveFilterFrameCalls := 1,
       productiveFilterFrameValueChecks := frameValueCount f,
       productiveMassCalls := 2, productiveMassSlots := 2 * f.doms.length })

/-- Verbatim `frameViewedB` + value counter. -/
def frameViewedC (f : BranchFrame) : Bool × Nat :=
  let vs := (Frame.domains f).flatMap Dom.enum
  (vs.all (fun v => v.intView != none), vs.length)

/-- Verbatim `frameLiveB` + slot counter. -/
def frameLiveC (f : BranchFrame) : Bool × Nat :=
  (f.doms.all (fun d => !d.isEmpty), f.doms.length)

/-- Verbatim `scanDatabase` + counters. Returns `(event, cost)`. -/
def scanDatabaseC (original : List Clause) (f : BranchFrame) :
    List Clause → PruningEvent × ScanCost
  | [] => (.stable, {})
  | c :: rest =>
    let (rem, crc, vc) := clauseRemainingC f c
    let base : ScanCost :=
      { dbClausesVisited := 1, dbClauseRemaining := crc, dbLiteralValueChecks := vc }
    match rem with
    | [] => (.conflict [c], base)
    | [l] =>
        let (pr, pc) := productiveC l f
        if pr then (.implied l c false (!(original.contains c)), base.add pc)
        else
          let (e, c') := scanDatabaseC original f rest
          (e, base.add c')
    | _ =>
        let (e, c') := scanDatabaseC original f rest
        (e, base.add c')

/-- Verbatim `scanPropagators` + counters. Returns `(event, cost)`. -/
def scanPropagatorsC (f : BranchFrame) : List Propagator → PruningEvent × ScanCost
  | [] => (.stable, {})
  | p :: rest =>
    let base : ScanCost := { propVisits := 1 }
    match p.run (frameState f) with
    | .stable =>
        let (e, c) := scanPropagatorsC f rest
        (e, base.add c)
    | .conflict c =>
        (.conflict (if c.isEmpty then [] else [c]), base)
    | .implied l r =>
        let (pr, pc) := productiveC l f
        if pr then (.implied l r.clause false false, base.add pc)
        else
          let (e, c) := scanPropagatorsC f rest
          (e, (base.add c).add pc)

/-- Verbatim `nextPruningEvent` + counters. -/
def nextPruningEventC (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : PruningEvent × ScanCost :=
  let (e1, c1) := scanDatabaseC original f db
  let c1 := c1.add { dbScans := 1 }
  match e1 with
  | .stable =>
      let (fv, vvc) := frameViewedC f
      let c1 := c1.add { frameViewedCalls := 1, frameViewedValueChecks := vvc }
      if fv then
        let (e2, c2) := scanPropagatorsC f props
        (e2, (c1.add c2).add { propScans := 1 })
      else (PruningEvent.stable, c1)
  | .conflict cs => (.conflict cs, c1)
  | .implied l c lr fl =>
      let (flv, sl) := frameLiveC f
      let c1 := c1.add { frameLiveCalls := 1, frameLiveSlots := sl }
      if flv then (.implied l c lr fl, c1) else (PruningEvent.stable, c1)

/-! ## 2. Counting along a REAL bounded `phaseNext` run -/

/-- Cost the dispatch incurs at `cfg` for the scans of ONE `schedulerNext`
call, derived from the real transition `t`: the `.propagate` arm is
`explainedDeduction` returning `some` (one `nextPruningEvent`; no
`terminalResult`), every other active/conflict-free transition means
`explainedDeduction = none` and `terminalResult` therefore runs a SECOND
`nextPruningEvent`. Jump (`.learnBackjumpAssert`) and consume
(`.chronologicalFallback` from a dead branch) run `restoreNarrow`+`syncAll`
instead of a scan. -/
def stepCost {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (t : SchedulerTransition leaf) : ScanCost :=
  let scans :=
    if cfg.conflict.isNone && cfg.status == .active then
      let (ev, c1) := nextPruningEventC cfg.original cfg.props cfg.branch.frame cfg.branch.learned
      let c1 := c1.add { nextPruningCalls := 1 }
      -- explainedDeduction extras on an implied event: a trail scan
      -- (`TrailRedundant`), a filterFrame + Frame.mass, a `learned.contains c`
      let c1 :=
        match ev with
        | .implied _c _ lr _ =>
            let mem : ScanCost :=
              if lr then { dbMembershipChecks := 1, dbMembershipClauses := cfg.branch.learned.length }
              else {}
            c1.add (mem.add { trailEntriesScanned := cfg.branch.trail.length,
                              impliedEventExtras := 1 })
        | _ => c1
      if t matches .propagate _ then c1
      else
        -- terminalResult: a second nextPruningEvent + its own extras
        let (ev2, c2) := nextPruningEventC cfg.original cfg.props cfg.branch.frame cfg.branch.learned
        let c2 := c2.add { nextPruningCalls := 1 }
        let c2 :=
          match ev2 with
          | .stable =>
              -- `wipeoutClause` scans the frame values once per slot
              c2.add { trailEntriesScanned := cfg.branch.trail.length }
          | .implied _c _ lr _ =>
              let mem : ScanCost :=
                if lr then { dbMembershipChecks := 1, dbMembershipClauses := cfg.branch.learned.length }
                else {}
              c2.add (mem.add { trailEntriesScanned := cfg.branch.trail.length })
          | .conflict cs =>
              c2.add { dbMembershipChecks := (cs.filter (fun c => !(cfg.branch.learned.contains c))).length,
                       dbMembershipClauses := cs.length * cfg.branch.learned.length }
        c1.add c2
    else {}
  let restore : ScanCost :=
    match t with
    | .learnBackjumpAssert _ _ _ => { restoreSyncCalls := 1 }
    | .chronologicalFallback _ => if cfg.status == .dead then { restoreSyncCalls := 1 } else {}
    | .localExclude _ => if cfg.status == .dead then { restoreSyncCalls := 1 } else {}
    | _ => {}
  scans.add restore

structure RunCounts where
  steps : Nat := 0
  jumps : Nat := 0
  consumes : Nat := 0
  conflictsFound : Nat := 0   -- steps whose real transition is .analyzeConflict
  propagates : Nat := 0
  cost : ScanCost := {}
  verdict : Nat := 0          -- 0 bound, 1 sat, 2 unsat
  ms : Nat := 0
  /-- measured bare (uninstrumented) wall ns/steps of the same search -/
  realNs : Nat := 0
  realSteps : Nat := 0
  /-- real analysis sites `(orig, trail, level, conflict clause)`, for the
  analyzer replay benchmark (bounded). -/
  sites : List (List Domain × List TrailEntry × Nat × Clause) := []
  /-- digest of all sampled arm results (forces evaluation; defeats DCE). -/
  sink : Nat := 0
  /-- per-arm single-sample timings (ns) on REAL visited configurations,
  keyed by arm name. -/
  samples : List (String × Nat) := []

/-- Consume a transition result so the compiler cannot eliminate the timed
call as dead code; returns a cheap digest of the real result. -/
def transDigest {leaf : Assignment → Bool} : SchedulerTransition leaf → Nat
  | .propagate next => next.branch.trail.length + next.branch.frame.doms.length
  | .decide next _ => next.branch.trail.length + next.checkpoints.length
  | .analyzeConflict next _ => next.stats.conflicts
  | .learnBackjumpAssert next _ _ => next.branch.trail.length + next.branch.learned.length
  | .localExclude next => next.log.regions.length
  | .chronologicalFallback next => next.pending.length + 1
  | .sat _ => 1
  | .unsat => 1

/-- Time the REAL work the dispatcher performed at this configuration:
(a) the deduction scan (`explainedDeduction`, which runs `nextPruningEvent`),
(b) the terminal scan (`terminalResult`) when no productive deduction exists,
(c) the arm the transition took (`narrowState`+`syncSlot`, `stableStepGuarded`,
`consumeStep`), and, at a jump, the raw-dispatch part
(`schedulerNext`: evidence recording incl. `recordedAnalysis`'s analyzer run)
and the perform part (`backjumpStep`) on the reconstructed post-dispatch
configuration. One timing sample per step; medians are taken later. The
digests force evaluation. -/
def sampleStep {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (t s : SchedulerTransition leaf)
    (samples : List (String × Nat)) (sink : Nat) :
    IO (List (String × Nat) × Nat) := do
  let mut samples := samples
  let mut sink := sink
  if cfg.conflict.isNone && cfg.status == .active then
    -- (a) the deduction scan on the real configuration
    let ta0 ← IO.monoNanosNow
    let d := explainedDeduction cfg.original cfg.props cfg.branch
    let ta1 ← IO.monoNanosNow
    let da := match d with
      | some dd => dd.literal.atom.slot + dd.frame.doms.length + 1
      | none => 0
    samples := samples ++ [("deductionScan(explainedDeduction)", ta1 - ta0)]
    sink := sink + da
    -- (b) the terminal scan, exactly when the deduction scan selected none
    if d.isNone then
      let tb0 ← IO.monoNanosNow
      let r := terminalResult cfg.orig cfg.original cfg.props cfg.branch
      let tb1 ← IO.monoNanosNow
      let db := match r with
        | .stable bs => bs.trail.length + 1
        | .conflict bs cs _ => bs.trail.length + cs.length + 2
        | .localExcluded bs _ _ _ => bs.trail.length + 5
      samples := samples ++ [("terminalScan(terminalResult)", tb1 - tb0)]
      sink := sink + db
  -- (c) the arm's own work
  match t with
  | .propagate _ =>
      match explainedDeduction cfg.original cfg.props cfg.branch with
      | some d =>
          let t0 ← IO.monoNanosNow
          let bs' := narrowState cfg.branch d.frame d.literal d.reason d.learned
          let bs'' := syncSlot cfg.orig bs' d.literal.atom.slot
          let t1 ← IO.monoNanosNow
          samples := samples ++ [("propagateArm(narrowState+syncSlot)", t1 - t0)]
          sink := sink + bs''.trail.length + bs''.frame.doms.length
      | none => pure ()
  | .decide _ _ =>
      let t0 ← IO.monoNanosNow
      let r := stableStepGuarded cfg
      let t1 ← IO.monoNanosNow
      samples := samples ++ [("decideArm(stableStepGuarded)", t1 - t0)]
      sink := sink + transDigest r
  | .learnBackjumpAssert _ _ _ =>
      -- the phase step composed a raw analyzeConflict with its jump; decompose it
      let t0 ← IO.monoNanosNow
      let s' := schedulerNext cfg
      let t1 ← IO.monoNanosNow
      samples := samples ++ [("jumpRawDispatch(schedulerNext)", t1 - t0)]
      sink := sink + transDigest s'
      match s' with
      | .analyzeConflict n _ =>
          match n.conflict with
          | some ev =>
              let t2 ← IO.monoNanosNow
              let r := backjumpStep n ev
              let t3 ← IO.monoNanosNow
              samples := samples ++ [("jumpPerform(backjumpStep)", t3 - t2)]
              sink := sink + transDigest r
          | none => pure ()
      | _ => pure ()
  | .analyzeConflict _ _ =>
      let t0 ← IO.monoNanosNow
      let r := s
      let t1 ← IO.monoNanosNow
      samples := samples ++ [("conflictDispatch(schedulerNext)", t1 - t0)]
      sink := sink + transDigest r
  | .chronologicalFallback _ =>
      if cfg.status == .dead then
        let t0 ← IO.monoNanosNow
        let r := consumeStep cfg
        let t1 ← IO.monoNanosNow
        samples := samples ++ [("consumeArm(consumeStep)", t1 - t0)]
        sink := sink + transDigest r
      else pure ()
  | .localExclude _ => pure ()
  | .sat _ => pure ()
  | .unsat => pure ()
  return (samples, sink)

/-- Bounded REAL `phaseNext` walk that accumulates the twin counts and the
per-arm timing samples. -/
def countLoop {leaf : Assignment → Bool} :
    Nat → Nat → SchedulerConfig leaf → RunCounts → IO (RunCounts × Nat)
  | 0, _, _, acc => return (acc, 0)
  | fuel + 1, i, cfg, acc => do
      let tp0 ← IO.monoNanosNow
      let t := phaseNext cfg
      let tp1 ← IO.monoNanosNow
      let s := schedulerNext cfg
      let acc :=
        { acc with steps := acc.steps + 1, cost := acc.cost.add (stepCost cfg t),
                   samples := acc.samples ++ [("REALphaseNextStep", tp1 - tp0)] }
      let acc :=
        match t with
        | .learnBackjumpAssert _ _ _ => { acc with jumps := acc.jumps + 1 }
        | .analyzeConflict _ _ => { acc with conflictsFound := acc.conflictsFound + 1 }
        | .propagate _ => { acc with propagates := acc.propagates + 1 }
        | .chronologicalFallback _ => { acc with consumes := acc.consumes + 1 }
        | _ => acc
      -- probe the raw dispatcher for real analysis sites (bounded to 300)
      let acc :=
        if acc.sites.length < 300 then
          match s with
          | .analyzeConflict _ c =>
              { acc with sites := acc.sites ++ [(cfg.orig, cfg.branch.trail, cfg.branch.level, c)] }
          | _ => acc
        else acc
      let samples ← sampleStep cfg t s acc.samples acc.sink
      let acc := { acc with samples := samples.1, sink := samples.2 }
      match t with
      | .sat _ => return ({ acc with verdict := 1 }, 1)
      | .unsat => return ({ acc with verdict := 2 }, 2)
      | _ =>
          match t.successor with
          | some n => countLoop fuel (i + 1) n acc
          | none => return (acc, 0)

def runOne (bound : Nat) (name : String) (p : LcgHarness.LProblem) : IO (String × RunCounts) := do
  let leaf := LcgHarness.leafOf p
  let cfg0 : SchedulerConfig leaf := SchedulerConfig.init p.domains p.clauses (LcgHarness.propsOf p)
  -- measured REAL per-step time of the same search (bare loop, no observation)
  let tb0 ← IO.monoNanosNow
  let (brealSteps, _) ← IO.lazyPure fun _ => LcgHarness.bare (leaf := leaf) bound 0 cfg0
  let tb1 ← IO.monoNanosNow
  let t0 ← IO.monoMsNow
  let (acc, _) ← countLoop (leaf := leaf) bound 0 cfg0 {}
  let t1 ← IO.monoMsNow
  return (name, { acc with ms := t1 - t0, realNs := tb1 - tb0, realSteps := brealSteps })

def fmtCost (c : ScanCost) : String :=
  s!"steps/{c.nextPruningCalls}npe dbScans={c.dbScans} dbClauses={c.dbClausesVisited} \
clauseRemCalls={c.dbClauseRemaining} valueChecks={c.dbLiteralValueChecks} \
propScans={c.propScans} propVisits={c.propVisits} frameViewedCalls={c.frameViewedCalls} \
frameViewedValues={c.frameViewedValueChecks} frameLive={c.frameLiveCalls} \
productive={c.productiveCalls} pfFilterFrame={c.productiveFilterFrameCalls} \
pfFilterValues={c.productiveFilterFrameValueChecks} pfMass={c.productiveMassCalls} \
impliedExtras={c.impliedEventExtras} trailScans={c.trailEntriesScanned} \
dbMembership={c.dbMembershipChecks} dbMembershipClauses={c.dbMembershipClauses} \
restoreSync={c.restoreSyncCalls}"

/-! ## 3. Microbenchmarks of the REAL scan functions on a synthetic frame -/

/-- Synthetic realistic frame: `nSlots` slots of `nVals` int values, empty prefix. -/
def synFrame (nSlots nVals : Nat) : BranchFrame :=
  { doms := List.replicate nSlots
      (Dom.ofList ((List.range nVals).map (fun k => Value.int (Int.ofNat k)))), order := [] }

/-- Synthetic clause database: `nClauses` clauses over the first slots. -/
def synDB (nSlots _nVals nClauses : Nat) : List Clause :=
  (List.range nClauses).map fun k =>
    [ posNe (k % nSlots) 0, posNe ((k + 1) % nSlots) 0, posNe ((k + 2) % nSlots) 999 ]

/-- Synthetic registered propagators: `leConstHi` bounds borrowed from the real
`propagatorOfProved`, so the `run` cost is the real one. -/
def synProps (nSlots nVals nProps : Nat) : List Propagator :=
  let doms := (synFrame nSlots nVals).doms
  let dcs : List DomConstraint :=
    (List.range nProps).map fun k => .leConstHi (k % nSlots) ((Int.ofNat nVals) + (Int.ofNat k))
  clampProps doms (dcs.filterMap propagatorOfProved)

/-- Run `act` `inner` times inside each of `outer` timed windows; return the
best window's ns per call and a sink sum (forces evaluation, defeats DCE). -/
def benchCall (outer inner : Nat) (act : Unit → IO Nat) : IO (Nat × Nat) := do
  let mut best := 0
  let mut sink := 0
  for _ in [0:outer] do
    let t0 ← IO.monoNanosNow
    let mut acc := 0
    for _ in [0:inner] do
      acc := acc + (← act ())
    let t1 ← IO.monoNanosNow
    sink := sink + acc
    let ns := (t1 - t0) / inner
    if best == 0 || ns < best then best := ns
  return (best, sink)

/-- Microbenchmarks of the REAL scan functions at two sizes each, so a
per-unit cost and a per-call overhead can be separated by linear
interpolation. Also replays the REAL analyzer (`analyzeAtAllowance`) on
analysis sites recorded from real runs, and converts the measured counts
into an estimated per-step time share. -/
def benchUnit (realNs realSteps : Nat) (total : ScanCost) (steps : Nat)
    (sites : List (List Domain × List TrailEntry × Nat × Clause))
    (samples : List (String × Nat)) : IO Unit := do
  let f20 := synFrame 20 8
  let f5 := synFrame 5 8
  let (nsDB16, _) ← benchCall 30 300 (fun _ => do
    let r := scanDatabase ([] : List Clause) f20 (synDB 20 8 16)
    return (match r with | .stable => 1 | .conflict _ => 2 | .implied _ _ _ _ => 3))
  let (nsDB64, _) ← benchCall 30 300 (fun _ => do
    let r := scanDatabase ([] : List Clause) f20 (synDB 20 8 64)
    return (match r with | .stable => 1 | .conflict _ => 2 | .implied _ _ _ _ => 3))
  let props12 := synProps 20 8 12
  let props48 := synProps 20 8 48
  let (nsP12, _) ← benchCall 30 300 (fun _ => do
    let r := scanPropagators f20 props12
    return (match r with | .stable => 1 | .conflict _ => 2 | .implied _ _ _ _ => 3))
  let (nsP48, _) ← benchCall 30 300 (fun _ => do
    let r := scanPropagators f20 props48
    return (match r with | .stable => 1 | .conflict _ => 2 | .implied _ _ _ _ => 3))
  let (nsV40, _) ← benchCall 30 300 (fun _ => do
    let r := frameViewedB f5
    return (if r then 1 else 0))
  let (nsV160, _) ← benchCall 30 300 (fun _ => do
    let r := frameViewedB f20
    return (if r then 1 else 0))
  let (nsNPE, _) ← benchCall 30 300 (fun _ => do
    let r := nextPruningEvent ([] : List Clause) props48 f20 (synDB 20 8 64)
    return (match r with | .stable => 1 | .conflict _ => 2 | .implied _ _ _ _ => 3))
  -- per-unit costs by interpolation (16 -> 64 clauses is 48 extra clauses)
  let dbPerClause := (nsDB64 - nsDB16) / 48
  let dbOverhead := nsDB64 - 64 * dbPerClause
  let propPerProp := (nsP48 - nsP12) / 36
  let propOverhead := nsP48 - 48 * propPerProp
  let valuePerCheck := (nsV160 - nsV40) / 120
  let framedOverhead := nsV160 - 160 * valuePerCheck
  IO.println s!"BENCH dbPerClauseNs={dbPerClause} dbCallOverheadNs={dbOverhead} \
propPerVisitNs={propPerProp} propCallOverheadNs={propOverhead} valueCheckNs={valuePerCheck} \
frameViewedOverheadNs={framedOverhead} nextPruningEventNs={nsNPE} \
(db16={nsDB16}ns db64={nsDB64}ns props12={nsP12}ns props48={nsP48}ns v40={nsV40}ns v160={nsV160}ns)"
  -- analyzer replay on real sites
  let mut nsAnaPerSite : Nat := 0
  if !sites.isEmpty then
    let (nsAna, sink) ← benchCall 20 20 (fun _ => do
      let mut s := 0
      for (orig, trail, lvl, c) in sites do
        match analyzeAtAllowance orig trail lvl c with
        | some _ => s := s + 1
        | none => s := s + 2
      return s)
    nsAnaPerSite := nsAna / (sites.length + 1)
    IO.println s!"BENCH analyzerPerSiteNs={nsAnaPerSite} analyzerSitesReplayed={sites.length} sink={sink}"
  else
    IO.println "BENCH analyzer: no analysis sites recorded (nothing to replay)"
  -- Estimated per-step time share: measured counts x microbenchmarked unit
  -- costs (same host, single run). Assumes the synthetic benchmark sizes are
  -- representative of the visited configurations' clause lengths and domain
  -- widths; the unit costs below are for a 20-slot x 8-value frame.
  if steps > 0 then
    let ps (x : Nat) : Nat := x / steps
    let dbNs := ps total.dbClausesVisited * dbPerClause
    let propNs := ps total.propVisits * propPerProp
    let fvNs := ps total.frameViewedValueChecks * valuePerCheck
    let ffNs := ps total.productiveFilterFrameValueChecks * valuePerCheck
    let anaNs := sites.length * nsAnaPerSite / steps
    let sum := dbNs + propNs + fvNs + ffNs + anaNs
    let pct (x : Nat) : String := s!"{x * 100 / (sum + 1)}"
    let measuredPerStep := if realSteps == 0 then 0 else realNs / realSteps
    IO.println s!"ESTIMATE perStepNs db={dbNs}({pct dbNs}%) prop={propNs}({pct propNs}%) \
frameViewed={fvNs}({pct fvNs}%) filterFrame={ffNs}({pct ffNs}%) \
analyzerPerStep={anaNs}({pct anaNs}%) sum={sum}ns/step (steps={steps}) \
other(trail-scans/restoreSync/overheads) not included"
    -- per-arm medians on real configurations
    if !samples.isEmpty then
      let names := (samples.map (·.1)).mergeSort (· ≤ ·) |>.eraseDups
      let mut armTotal := 0
      for nm in names do
        let xs := (samples.filter (fun p => p.1 == nm)).map (·.2)
        let sorted := xs.mergeSort (· ≤ ·)
        let med := sorted.getD (sorted.length / 2) 0
        armTotal := armTotal + med * xs.length / steps
        IO.println s!"ARM {nm} n={xs.length} medianNs={med} perStepNs={med * xs.length / steps} totalNs={med * xs.length}"
      IO.println s!"ATTRIBUTION measuredComponentsPerStepNs={sum + armTotal} \
scanComponentsNs={sum} armComponentsNs={armTotal} \
measuredBarePerStepNs={measuredPerStep} coveragePct={(sum + armTotal) * 100 / (measuredPerStep + 1)} (per-step basis)"
  return ()

def main2 (args : List String) : IO UInt32 := do
  -- parse args: --fuzz N SEED, --bound N, FILE...
  let rec go (as : List String) (fuzzN seed bound : Nat) (files : List String) :
      IO (Nat × Nat × Nat × List String) := do
    match as with
    | [] => return (fuzzN, seed, bound, files.reverse)
    | "--fuzz" :: n :: s :: rest =>
        go rest (n.toNat?.getD fuzzN) (s.toNat?.getD seed) bound files
    | "--bound" :: n :: rest => go rest fuzzN seed (n.toNat?.getD bound) files
    | f :: rest => go rest fuzzN seed bound (f :: files)
  let (fuzzN, seed, bound, files) ← go args 0 100000 50000 []
  let mut total : ScanCost := {}
  let mut steps := 0
  let mut ms := 0
  let mut njump := 0
  let mut nconsume := 0
  let mut nconflict := 0
  let mut nprop := 0
  let mut realNs := 0
  let mut realSteps := 0
  let mut sites : List (List Domain × List TrailEntry × Nat × Clause) := []
  let mut samples : List (String × Nat) := []
  let mut sink := 0
  for path in files do
    let src ← IO.FS.readFile path
    match LcgHarness.ofSource path src with
    | .error e => IO.println s!"SKIP {path}: {e}"
    | .ok inst =>
        let (name, acc) ← runOne bound inst.name inst.problem
        IO.println s!"COUNTS {name} verdict={acc.verdict} steps={acc.steps} jumps={acc.jumps} \
conflicts={acc.conflictsFound} propagates={acc.propagates} consumes={acc.consumes} ms={acc.ms}"
        IO.println s!"COST {name} {fmtCost acc.cost}"
        total := total.add acc.cost
        steps := steps + acc.steps
        ms := ms + acc.ms
        njump := njump + acc.jumps
        nconsume := nconsume + acc.consumes
        nconflict := nconflict + acc.conflictsFound
        nprop := nprop + acc.propagates
        realNs := realNs + acc.realNs
        realSteps := realSteps + acc.realSteps
        samples := samples ++ acc.samples
        sink := sink + acc.sink
        sites := sites ++ acc.sites
  for k in [0:fuzzN] do
    let sd := seed + k
    let src := LcgHarness.fuzzSrc sd
    match LcgHarness.ofSource s!"fuzz{sd}" src with
    | .error _ => pure ()
    | .ok inst =>
        let (_, acc) ← runOne bound inst.name inst.problem
        total := total.add acc.cost
        steps := steps + acc.steps
        ms := ms + acc.ms
        njump := njump + acc.jumps
        nconsume := nconsume + acc.consumes
        nconflict := nconflict + acc.conflictsFound
        nprop := nprop + acc.propagates
        realNs := realNs + acc.realNs
        realSteps := realSteps + acc.realSteps
        samples := samples ++ acc.samples
        sink := sink + acc.sink
        if sites.length < 300 then sites := sites ++ acc.sites
  IO.println s!"TOTAL steps={steps} jumps={njump} conflicts={nconflict} propagates={nprop} \
consumes={nconsume} countingMs={ms}"
  IO.println s!"TOTALCOST {fmtCost total}"
  let perStep (x : Nat) : String :=
    if steps == 0 then "-" else s!"{(x * 1000 / steps) / 1000}.{(x * 1000 / steps) % 1000}"
  IO.println s!"PERSTEP dbClauses={perStep total.dbClausesVisited} valueChecks={perStep total.dbLiteralValueChecks} \
propVisits={perStep total.propVisits} frameViewedValues={perStep total.frameViewedValueChecks} \
pfFilterValues={perStep total.productiveFilterFrameValueChecks} nextPruning={perStep total.nextPruningCalls} \
dbScans={perStep total.dbScans} frameViewedCalls={perStep total.frameViewedCalls} \
frameLive={perStep total.frameLiveCalls} productive={perStep total.productiveCalls} \
restoreSync={perStep total.restoreSyncCalls} trailScans={perStep total.trailEntriesScanned}"
  IO.println s!"ANALYSIS-SITES sites={sites.length} sampleSink={sink}"
  IO.println s!"MEASURED bareRealSteps={realSteps} bareRealNs={realNs} barePerStepNs={if realSteps == 0 then 0 else realNs / realSteps}"
  benchUnit realNs realSteps total steps sites samples
  return 0

end Tests.E1

/-- Entry point for `lake env lean --run`. -/
def main (args : List String) : IO UInt32 := Tests.E1.main2 args
