/-
File: Tests/E1/SchedCounts.lean

Purpose (PLAN task P1, TEST-ONLY, UNCERTIFIED): before/after evidence for the
scheduled propagator scan on the P1 fuzz battery (the same seed set the
`tests_lcg_harness --fuzz` acceptance uses).

Two measurements per fuzz instance, all in one process on the SAME instance:

  baselineMs  -- the certified BASELINE route: `LcgPhaseKernel.solve` over
                 `lcgProps`/`lcgSeedEntailed` (named explicitly because after
                 the P1 wiring `lcgRun` IS the scheduled route)
  schedMs     -- the SCHEDULED route (`lcgRunSched` = `solve_sched` over the
                 scheduled dispatch `phaseNextSched`; certified against the
                 kernel by `lcgRunSched_eq_solve`, and now the public `lcgRun`)
  agree       -- all four verdicts coincide: kernel, scheduled, wired `lcgRun`,
                 and the counting twin's drive (must always be true)
  baseVisits  -- propagator `run` calls the BASELINE route makes on the real
                 scheduled run's configurations (every walked position)
  schedVisits -- propagator `run` calls the SCHEDULED route makes (positions
                 whose watched-slot stamp changed)
  skips       -- positions whose memorized stamp matched (run reused, i.e.
                 the rescan elimination this task is about)
  twinMs      -- instrumented ms of the counting twin collecting the counts

The counts come from a counting twin of `scanPropagatorsSchedAux` /
`nextPruningEventSched` (verbatim recursion + counters, same evaluation order
and same `List`/`Bool` short-circuiting) driven along the REAL scheduled
dispatcher `phaseNextSched` on the REAL configurations of the real run. The
scan-occurrence structure is the real `schedulerNextSched` (ONE
`nextPruningEventSched` per step feeding both the transition and the table;
the terminal continuation re-reads that same event), so the scheduled counts
are one-side and directly comparable to the baseline's. Nothing in
`LeanFzn/**` is modified. A skipped position has the SAME
event as the baseline run (that is the proved equivalence
`scanPropagatorsSched_fst_eq`), so baseline visits = positions =
scheduled runs + skips.

Run: lake env lean --run Tests/E1/SchedCounts.lean [--seeds N START] [--reps K]
-/
import Tests.UIP.LcgHarnessBattery
import LeanFzn.Integration.Lcg
import LeanFzn.Solver.UIP.Proofs.SchedulerStepSched
open LeanFzn.Solver.Propagation LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.Core LeanFzn

namespace Tests.E1

/-! ## 1. Counting twin of the scheduled scan layer (verbatim + counters) -/

/-- Scheduled-scan counters over a whole step. `scans` counts
`scanPropagatorsSched` invocations, `runs` the propagator `run` calls and
`skips` the memorized reuses of the scheduled route. The dispatcher evaluates
the scan chain ONCE per step (`schedulerNextSched` reads both the transition
and the table off a single `nextPruningEventSched`), so these counts are
ONE-side and directly comparable to `baseVisits`: the baseline route
(`schedulerNext`) never skips, so `baseVisits = runs + skips` holds per
instance (modulo the baseline's own double scan when no deduction exists). -/
structure ScanCnt where
  scans : Nat := 0
  runs : Nat := 0
  skips : Nat := 0
  baseVisits : Nat := 0
  steps : Nat := 0
  deriving Repr

def ScanCnt.add (a b : ScanCnt) : ScanCnt :=
  { scans := a.scans + b.scans, runs := a.runs + b.runs, skips := a.skips + b.skips,
    baseVisits := a.baseVisits + b.baseVisits, steps := a.steps + b.steps }

/-- Verbatim `scanPropagatorsSchedAux` with `(runs, skips)` counters (no
`scans`: the caller counts the invocation). -/
def scanCountAux (f : BranchFrame) :
    List (Option (List Domain × PropagationResult)) → List Propagator →
      PruningEvent × List (Option (List Domain × PropagationResult)) × ScanCnt
  | seens, [] => (.stable, seens, {})
  | [], p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens', c) := scanCountAux f [] ps
          (ev, some (watchStamp f p.watches, .stable) :: seens', { c with runs := c.runs + 1 })
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), [], { runs := 1 })
      | .implied l r =>
          if productive l f then
            (.implied l r.clause true false, [], { runs := 1 })
          else
            let (ev, seens', c) := scanCountAux f [] ps
            (ev, some (watchStamp f p.watches, .implied l r) :: seens',
              { c with runs := c.runs + 1 })
  | some (w, r) :: seens, p :: ps =>
      if stampEqB w (watchStamp f p.watches) && !p.watches.isEmpty then
        match r with
        | .stable =>
            let (ev, seens', c) := scanCountAux f seens ps
            (ev, some (w, r) :: seens', { c with skips := c.skips + 1 })
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some (w, r) :: seens,
            { skips := 1 })
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause true false, some (w, r) :: seens, { skips := 1 })
            else
              let (ev, seens', c) := scanCountAux f seens ps
              (ev, some (w, r) :: seens', { c with skips := c.skips + 1 })
      else
        match p.run (frameState f) with
        | .stable =>
            let (ev, seens', c) := scanCountAux f seens ps
            (ev, some (watchStamp f p.watches, .stable) :: seens',
              { c with runs := c.runs + 1 })
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some (w, r) :: seens,
            { runs := 1 })
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause true false, some (w, r) :: seens, { runs := 1 })
            else
              let (ev, seens', c) := scanCountAux f seens ps
              (ev, some (watchStamp f p.watches, .implied l r') :: seens',
                { c with runs := c.runs + 1 })
  | none :: seens, p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens', c) := scanCountAux f seens ps
          (ev, some (watchStamp f p.watches, .stable) :: seens',
            { c with runs := c.runs + 1 })
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), none :: seens, { runs := 1 })
      | .implied l r =>
          if productive l f then
            (.implied l r.clause true false, none :: seens, { runs := 1 })
          else
            let (ev, seens', c) := scanCountAux f seens ps
            (ev, some (watchStamp f p.watches, .implied l r) :: seens',
              { c with runs := c.runs + 1 })

/-- `nextPruningEventSched` (verbatim scan-occurrence logic) + counters. -/
def npeCount (original : List Clause) (props : List Propagator) (sched : PropScheduler)
    (f : BranchFrame) (db : List Clause) : PruningEvent × PropScheduler × ScanCnt :=
  match scanDatabase original f db with
  | .stable =>
      if frameViewedB f then
        let (ev, seen, c) := scanCountAux f sched.seen props
        (ev, { seen := seen }, { c with scans := c.scans + 1 })
      else (.stable, sched, {})
  | .conflict cs => (.conflict cs, sched, {})
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then (.implied l c learnReason fromLearned, sched, {})
      else (.stable, sched, {})

/-- The scan occurrences of ONE step, mirroring the REAL one-scan dispatcher
`schedulerNextSched` (`schedulerNextSchedActive`): the scheduled event prompt
is evaluated once, and — when it yields no productive deduction — the terminal
continuation reads the SAME event (no second scan). -/
def stepScans {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) : ScanCnt × PropScheduler :=
  match cfg.conflict with
  | some _ => ({}, sched)
  | none =>
      match cfg.status with
      | .dead => ({}, sched)
      | .active =>
          let (ev1, s1, c1) := npeCount cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned
          let c : ScanCnt := { c1 with baseVisits := c1.runs + c1.skips }
          match explainedDeductionOf cfg.original cfg.props cfg.branch ev1 with
          | some _ => (c, s1)
          | none => (c, s1)

/-! ## 2. The real-route driver + counting loop -/

/-- Follow the REAL scheduled dispatcher `phaseNextSched` (transitions and
tables), counting the scheduled scans with the twin. Returns `none` on fuel
exhaustion (the real kernels are fuel-free; measurement only). -/
partial def drive {leaf : Assignment → Bool} (fuel : Nat) (cfg : SchedulerConfig leaf)
    (sched : PropScheduler) (acc : ScanCnt) : ScanCnt × Option (DriverResult leaf) :=
  match fuel with
  | 0 => (acc, none)
  | fuel + 1 =>
      let pr := phaseNextSched cfg sched
      let (c, _) := stepScans cfg sched
      let acc := { acc.add c with steps := acc.steps + c.steps + 1 }
      match pr.1 with
      | .sat w => (acc, some (.sat w))
      | .unsat => (acc, some .unsat)
      | _ =>
          match pr.1.successor with
          | some n => drive fuel n pr.2 acc
          | none => (acc, none)

def verdictTag {leaf : Assignment → Bool} : DriverResult leaf → Nat
  | .sat _ => 1
  | .unsat => 2

/-- Best (minimum) real-time window in ns over `reps` runs of `act`, plus the
last result (forces the pure computation inside the timed window). -/
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

structure Totals where
  instances : Nat := 0
  steps : Nat := 0
  scans : Nat := 0
  baseVisits : Nat := 0
  schedVisits : Nat := 0
  skips : Nat := 0
  baseNs : Nat := 0
  schedNs : Nat := 0
  twinNs : Nat := 0
  disagree : Nat := 0
  deriving Repr

def runOneSrc (reps : Nat) (name src : String) (t : Totals) : IO Totals := do
  match LcgHarness.ofSource name src with
  | .error e => IO.eprintln s!"{name}: {e}"; return t
  | .ok inst =>
    match inst.compiled with
    | none => return t
    | some p =>
      if !lcgRouteGateMixed p then
        IO.println s!"{name}: NOT ROUTED (gate off)"
        return t
      let leaf := lcgLeaf p
      -- the certified BASELINE route is the fuel-free kernel solve itself: after
      -- the wiring, `lcgRun` IS the scheduled route, so naming the kernel
      -- explicitly keeps the before/after comparison alive.
      let (baseNs, r0) ← bestNs reps
        (fun _ => LcgPhaseKernel.solve p.domains (seedClauses p.constraints) (lcgProps p)
          (lcgSeedEntailed p)) (.sat [] : DriverResult leaf)
      let (schedNs, r1) ← bestNs reps (fun _ => lcgRunSched p) (.sat [] : DriverResult leaf)
      let r2 := lcgRun p
      let (twinNs, res) ← bestNs 1
        (fun _ => drive (leaf := leaf) 1000000 (SchedulerConfig.init p.domains
          (seedClauses p.constraints) (lcgProps p)) (PropScheduler.init (lcgProps p)) {})
        (({}, none) : ScanCnt × Option (DriverResult leaf))
      let (cnt, rv) := res
      let rvTag := match rv with
        | some r => verdictTag r
        | none => 0
      let dis := if verdictTag r0 == verdictTag r1 && verdictTag r1 == rvTag
          && verdictTag r2 == rvTag then 0 else 1
      if dis == 1 then
        IO.eprintln s!"{name}: VERDICT MISMATCH base={verdictTag r0} sched={verdictTag r1} wired={verdictTag r2} twin={rvTag}"
      IO.println s!"{name} base={baseNs}ns sched={schedNs}ns twin={twinNs}ns steps={cnt.steps} scans={cnt.scans} baseVisits={cnt.baseVisits} schedVisits={cnt.runs} skips={cnt.skips} schedPositions={cnt.runs + cnt.skips}"
      let t' : Totals := { t with instances := t.instances + 1, steps := t.steps + cnt.steps, scans := t.scans + cnt.scans, baseVisits := t.baseVisits + cnt.baseVisits, schedVisits := t.schedVisits + cnt.runs, skips := t.skips + cnt.skips, baseNs := t.baseNs + baseNs, schedNs := t.schedNs + schedNs, twinNs := t.twinNs + twinNs, disagree := t.disagree + dis }
      return t'

def parseArgs : List String → Nat × Nat × Nat × Bool × Bool
  | "--seeds" :: n :: s :: rest =>
      let (a, b, c, d, e) := parseArgs rest
      (n.toNat?.getD a, s.toNat?.getD b, c, d, e)
  | "--reps" :: k :: rest =>
      let (a, b, _, d, e) := parseArgs rest
      (a, b, k.toNat?.getD 3, d, e)
  | "--battery" :: rest =>
      let (a, b, c, _, e) := parseArgs rest
      (a, b, c, true, e)
  | "--heavy" :: rest =>
      let (a, b, c, d, _) := parseArgs rest
      (a, b, c, d, true)
  | _ => (300, 100000, 3, false, false)

def run (args : List String) : IO UInt32 := do
  let (count, start, reps, bat, hv) := parseArgs args
  let mut t : Totals := {}
  if bat then
    for (name, src) in LcgHarness.battery do
      t ← runOneSrc reps name src t
  if hv then
    for (name, src) in LcgHarness.heavy do
      t ← runOneSrc reps name src t
  if !bat && !hv then
    for i in [0:count] do
      t ← runOneSrc reps s!"fuzz{start + i}" (LcgHarness.fuzzSrc (start + i)) t
  IO.println s!"\nSCHED SUMMARY seeds {start}..{start + count - 1}: instances={t.instances} reps={reps}"
  IO.println s!"  steps={t.steps} scans(1-side)={t.scans} baseVisits(1-side)={t.baseVisits} schedVisits(1-side)={t.schedVisits} skips(1-side)={t.skips} disagreeVerdicts={t.disagree}"
  IO.println s!"  schedRuns={t.schedVisits} baselineRuns={t.baseVisits} runElimination={if t.baseVisits == 0 then 0 else 100 * (t.baseVisits - t.schedVisits) / t.baseVisits}% skips={t.skips} of positions={t.schedVisits + t.skips}"
  IO.println s!"  total baselineMs={t.baseNs / 1000000} scheduledMs={t.schedNs / 1000000} twinInstrumentedMs={t.twinNs / 1000000} (sum of per-instance best windows, reps={reps})"
  return 0

end Tests.E1

/-- Entry point for `lake env lean --run`. -/
def main (args : List String) : IO UInt32 := Tests.E1.run args
