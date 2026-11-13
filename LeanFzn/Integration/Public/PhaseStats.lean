/-
Purpose: Dev-only `--phase-stats` wall-clock and VmRSS/VmHWM diagnostics
  (PLAN.md task E1).  Each phase line goes to stderr and reports the
  cumulative wall time since the CLI started, the current resident set and
  the peak resident set from `/proc/self/status`.
Dependencies: the public solve/optimize entries and the compiler pipeline
  stages (Normalize/SetShape/SetExpand/Bounds/Compile/Objective).
DAG: compiler + engine -> this observation-only wrapper -> Driver/Cli.
This module duplicates the composition order of `compileModelFull` and
`coreSolveFullWith` but never changes a verdict, an emitted solution or a
counter: every phased entry returns exactly the value of its unphased twin
on the same inputs (see the differential shell check in
`tmp/design/e1-memory.md`'s validation section).
-/
import LeanFzn.Integration.Public.Solve
import LeanFzn.Integration.Public.Optimize
import LeanFzn.Compiler.Objective

namespace LeanFzn.Core
open LeanFzn LeanFzn.Engine LeanFzn.Semantics LeanFzn.Compiler
open LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Integration

/-- Clock origin for one `--phase-stats` run. -/
structure PhaseCtx where
  startMs : Nat

/-- Start the diagnostic clock.  Called immediately before the model source
    is read, so the `parse` line includes the file read and the parser. -/
def PhaseCtx.new : IO PhaseCtx := do
  return { startMs := ← IO.monoMsNow }

/-- Extract the first integer from a `/proc/self/status` line with the given
    prefix (`VmRSS:` / `VmHWM:`); 0 when the field is absent. -/
private def statusField (line : String) (key : String) : Option Nat :=
  if line.startsWith key then
    String.toNat? (String.ofList (line.toList.filter Char.isDigit))
  else
    none

/-- Current `VmRSS` and `VmHWM` in kB.  A read failure reports zeroes rather
    than disturbing the run. -/
private def readMemKB : IO (Nat × Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let fields := status.splitOn "\n"
    let rss := (fields.findSome? (fun l => statusField l "VmRSS:")).getD 0
    let hwm := (fields.findSome? (fun l => statusField l "VmHWM:")).getD 0
    return (rss, hwm)
  catch _ =>
    return (0, 0)

/-- Emit one phase line: this phase's wall time, the cumulative wall time
    since the CLI started, and the current/peak RSS. -/
def PhaseCtx.report (ps : PhaseCtx) (name : String) (t0 : Nat) : IO Unit := do
  let t1 ← IO.monoMsNow
  let (rss, hwm) ← readMemKB
  IO.eprintln s!"leanfzn: phase {name} ms={t1 - t0} wall_ms={t1 - ps.startMs} rss_kb={rss} hwm_kb={hwm}"

/-- Time a pure phase.  The value is forced through `pure` before the
    clock is read, so a lazily floated pure computation cannot move its work
    past the phase boundary. -/
private def timedVal (ps : PhaseCtx) (name : String) (act : Unit → α) : IO α := do
  let t0 ← IO.monoMsNow
  let v ← pure (act ())
  ps.report name t0
  return v

/-- `compileModelFull` with the four source-level stages reported:
    normalize, set-shape, set-expand, bounds, then `compileModel`
    (`relabel` runs after the last timed boundary). -/
def compileModelFullPhased (ps : PhaseCtx) (m : Model) :
    IO (Except String (CompiledProblem DomConstraint)) := do
  if !arraysOkB m then
    return .error "unsupported array declaration or array argument"
  let m1 ← timedVal ps "normalize" (fun _ => normalizeFull m)
  let sh? ← timedVal ps "set-shape" (fun _ => shapeExpandModel m1)
  match sh? with
  | none => return .error "unsupported set shape"
  | some sh =>
      let se? ← timedVal ps "set-expand" (fun _ => setExpandModel sh.model)
      match se? with
      | none => return .error "unsupported set variable shape"
      | some se =>
          let mb? ← timedVal ps "bounds" (fun _ => boundsModel se.model)
          match mb? with
          | none => return .error "unbounded integer variable without certified bounds"
          | some mb =>
              let p? ← timedVal ps "compile" (fun _ => compileModel mb)
              match p? with
              | .error e => return .error e
              | .ok p => return .ok (relabel m se p)

/-- `compileModelOpt` with the same compile-phase lines; the objective
    index lookup is part of `compile`. -/
def compileModelOptPhased (ps : PhaseCtx) (m : Model) :
    IO (Except String (CompiledProblem DomConstraint × ObjectiveSpec)) := do
  match objectiveOf m.solve with
  | none => return .error "not an optimization model with a variable objective"
  | some (dir, x) =>
      if objVarOkB m x then
        match ← compileModelFullPhased ps (satisfyPart m) with
        | .error e => return .error e
        | .ok p =>
            match nameIndex p.names x.name with
            | none => return .error "objective variable has no search slot"
            | some i => return .ok ({ p with source := m }, ⟨i, dir, x⟩)
      else return .error "objective is not a declared var int"

/-- A cheap upper bound on `(Dom.enum d).length`: the small bitset holds at
    most 64 values, a hole interval at most its span, and the general case
    is exactly its value list.  `Dom.enum` is never materialised just to
    size the round budget below. -/
private def domCardBound (d : Dom) : Nat :=
  match d.rep with
  | .small _ _ _ => 64
  | .holes lo hi _ => if hi < lo then 0 else (hi - lo + 1).toNat
  | .general vs => vs.length

/-- The state-construction / search split of `coreSolveFullWith`.  The
    initial state (domain conversion, propagator registration, the initial
    queue, saved-phase seeding and the priority/order arrays) is timed as
    `initState`; `search-start` is a zero-width boundary marker before the
    entry CDCL loop, whose total is the following line (`search` for one
    solve, `search-end` for a whole optimization run).  The first decision
    is inside the loop and is merged into the search total (see the design
    note); the certified search path is not modified to observe it. -/
def coreSolveFullWithPhased (ps : PhaseCtx) (tag : String)
    (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) : IO (CoreResult × EngineStats) := do
  let q := presolveProblem o p
  let T : LitTable := {}
  let t0 ← IO.monoMsNow
  match hinit : initState q T with
  | none =>
      ps.report s!"{tag}initState" t0
      return (.gaveUp, { gaveUp := 1, gaveUpCause := "entry guard or domain conversion failed" })
  | some st0 =>
      let stSeed := seedPhases st0 prev
      let prio := annotPrioArray q
      let orders := configOrders q o
      ps.report s!"{tag}initState" t0
      let t1 ← IO.monoMsNow
      ps.report s!"{tag}search-start" t1
      let res ← pure (coreSolveFrom q T o stSeed
        ((seedPhases_rootInv (initState_rootInv hinit LitTable.inv_empty) prev).init_congr
          (seedPhases_doms st0 prev))
        ((initState_propsSound hinit).congr (seedPhases_props st0 prev))
        prio orders fuel)
      ps.report s!"{tag}search-end" t1
      return res

/-- `solveModelWithStats` with compile/initState/search phase lines. -/
def solveModelWithPhaseStats (ps : PhaseCtx) (m : Model)
    (o : SearchConfig := {}) (fuel : Nat := coreFuel) :
    IO (Result × EngineStats) := do
  match ← compileModelFullPhased ps m with
  | .error e => return (.unsupported e, {})
  | .ok p =>
      if gateOkFast (propagationProblem p) then
        let (r, st) ← coreSolveFullWithPhased ps "" p o none fuel
        match r with
        | .sat a => return (.sat (p.toStore a), st)
        | .unsat => return (.unsat, st)
        | .gaveUp => return (.unknown (giveUpReason st), st)
      else return (.unsupported "Core requires nonempty finite integer/Boolean domains", {})

/-- One optimization round with the per-round `initState`/search split.
    `coreSolveStatsWith prev p o fuel` is `coreSolveFullPre` on
    `roundConfig o prev`; `coreSolveFullWithPhased` replicates exactly that
    call, so the verdict and counters are the pure loop's. -/
def coreSolveRoundPhased (ps : PhaseCtx) (tag : String)
    (prev : Option (List Value)) (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) : IO (CertVerdict × EngineStats) := do
  let (r, st) ← coreSolveFullWithPhased ps tag p (roundConfig o prev) prev fuel
  match r with
  | .sat a => return (.sat a, st)
  | .unsat => return (.unsat, st)
  | .gaveUp => return (.fail, st)

/-- The streaming branch-and-bound recursion of `optimizeStreamCoreStatsLoop`
    with a `round-k-setup` (bound problem), `round-k-initState`,
    `round-k-search-start` and `round-k-search` line per round.  The emitted
    incumbents and the aggregate counters are those of the pure loop: every
    round runs the same `coreSolveFullPre` on the same `curP`.

    The recursion counts down an explicit budget rather than using
    `termination_by`: `domCardBound` of the objective domain plus two bounds
    the number of rounds, because every successful round strictly decreases
    `meas` (`meas_decr`) and `meas none` is at most the objective-domain
    cardinality plus one, so the final UNSAT/give-up round still runs and the
    zero branch is unreachable.  The budget is computed from the compact
    domain representation, never by enumerating the domain. -/
def optLoopPhased {α : Type} (ps : PhaseCtx) (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    Nat → Nat → Option (List Value) → Option Int → IO (OptRun × List α × EngineStats)
  | 0, _, _, bo => pure (⟨[], false, bo⟩, [], {})
  | n + 1, k, prev, bo => do
      let t0 ← IO.monoMsNow
      let cp := curP p0 spec bo
      let _ ← pure (cp.domains.length + cp.constraints.length)
      ps.report s!"round-{k}-setup" t0
      let (r, st) ← coreSolveRoundPhased ps s!"round-{k}-" prev cp o fuel
      match r with
      | .unsat => pure (⟨[], true, bo⟩, [], st)
      | .fail => pure (⟨[], false, bo⟩, [], st)
      | .sat a =>
          match a[spec.slot]? with
          | some (.int v) =>
              emit (f a) >>= fun _ =>
                optLoopPhased ps o fuel p0 spec f emit n (k + 1) (some a) (some v) >>= fun r =>
                  pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                    f a :: r.2.1, st.add r.2.2)
          | _ => pure (⟨[], false, bo⟩, [], st)

/-- Prepared entry with the same phase split as `coreSolveFullWithPhased`. -/
def coreSolveFullWithPreparedPhased (ps : PhaseCtx) (tag : String)
    (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) (doms : Array DomC)
    (hconv : convertDomains (presolveProblem o p).domains = some doms) :
    IO (CoreResult × EngineStats) := do
  let q := presolveProblem o p
  let T : LitTable := {}
  let t0 ← IO.monoMsNow
  match hinit : initStatePrepared q T doms hconv with
  | none =>
      ps.report s!"{tag}initState" t0
      return (.gaveUp, { gaveUp := 1, gaveUpCause := "entry guard or domain conversion failed" })
  | some st0 =>
      let hinit' : initState q T = some st0 := by
        rw [← initStatePrepared_eq hconv]
        exact hinit
      let stSeed := seedPhases st0 prev
      let prio := annotPrioArray q
      let orders := configOrders q o
      ps.report s!"{tag}initState" t0
      let t1 ← IO.monoMsNow
      ps.report s!"{tag}search-start" t1
      let res ← pure (coreSolveFrom q T o stSeed
        ((seedPhases_rootInv (initState_rootInv hinit' LitTable.inv_empty) prev).init_congr
          (seedPhases_doms st0 prev))
        ((initState_propsSound hinit').congr (seedPhases_props st0 prev))
        prio orders fuel)
      ps.report s!"{tag}search-end" t1
      return res

/-- One optimization round using the converted domains prepared for the run. -/
def coreSolveRoundPreparedPhased (ps : PhaseCtx) (tag : String)
    (prev : Option (List Value)) (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) (doms : Array DomC)
    (hconv : convertDomains (presolveProblem (roundConfig o prev) p).domains = some doms) :
    IO (CertVerdict × EngineStats) := do
  let (r, st) ← coreSolveFullWithPreparedPhased ps tag p (roundConfig o prev) prev fuel doms hconv
  match r with
  | .sat a => return (.sat a, st)
  | .unsat => return (.unsat, st)
  | .gaveUp => return (.fail, st)

/-- The streaming branch-and-bound recursion with the prepared domain array
    shared by every round.  Its counts, emissions and counters are those of
    `optLoopPhased`; only the per-round domain conversion moves out. -/
def optLoopPreparedPhased {α : Type} (ps : PhaseCtx) (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms)
    (f : List Value → α) (emit : α → IO Unit) :
    Nat → Nat → Option (List Value) → Option Int → IO (OptRun × List α × EngineStats)
  | 0, _, _, bo => pure (⟨[], false, bo⟩, [], {})
  | n + 1, k, prev, bo => do
      let t0 ← IO.monoMsNow
      let cp := curP p0 spec bo
      let _ ← pure (cp.domains.length + cp.constraints.length)
      ps.report s!"round-{k}-setup" t0
      have h0' : convertDomains p0.domains = some doms := by
        rwa [presolveProblem_domains] at h0
      have hcp : convertDomains cp.domains = some doms := by
        rw [curP_domains]
        exact h0'
      have hconv : convertDomains (presolveProblem (roundConfig o prev) cp).domains = some doms := by
        rw [presolveProblem_domains]
        exact hcp
      let (r, st) ← coreSolveRoundPreparedPhased ps s!"round-{k}-" prev cp o fuel doms hconv
      match r with
      | .unsat => pure (⟨[], true, bo⟩, [], st)
      | .fail => pure (⟨[], false, bo⟩, [], st)
      | .sat a =>
          match a[spec.slot]? with
          | some (.int v) =>
              emit (f a) >>= fun _ =>
                optLoopPreparedPhased ps o fuel p0 spec doms h0 f emit n (k + 1) (some a) (some v) >>= fun r =>
                  pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                    f a :: r.2.1, st.add r.2.2)
          | _ => pure (⟨[], false, bo⟩, [], st)

/-- `optimizeStreamCoreStats` with compile and per-round phase lines.  The
    ordinary `timing:` line is reproduced so `--stats` output keeps its
    shape (its numbers are wall-clock measurements and always vary). -/
def optimizeStreamCoreStatsPhased (ps : PhaseCtx) (o : SearchConfig) (m : Model)
    (emit : Store → IO Unit) : IO (Except String (OptSummary × EngineStats)) := do
  let t0 ← IO.monoMsNow
  match ← compileModelOptPhased ps m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      let t1 ← IO.monoMsNow
      let r ←
        match hdoms : convertDomains (presolveProblem o p).domains with
        | some doms =>
            optLoopPreparedPhased ps o coreFuel p spec doms hdoms
              (fun a => p.toStore a) emit
              (domCardBound (p.domainsArray.getD spec.slot Dom.empty) + 2) 1 none none
        | none =>
            optLoopPhased ps o coreFuel p spec (fun a => p.toStore a) emit
              (domCardBound (p.domainsArray.getD spec.slot Dom.empty) + 2) 1 none none
      ps.report "search-end" t1
      let t2 ← IO.monoMsNow
      if o.stats then
        IO.eprintln s!"leanfzn: timing: compile_ms={t1 - t0} search_ms={t2 - t1}"
      return .ok (⟨p, r.1, r.2.1⟩, r.2.2)

end LeanFzn.Core
