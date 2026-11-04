/-
File: Tests/E1/FamInventory.lean

Purpose (PLAN task G0, TEST-ONLY, UNCERTIFIED): inventory of the compiled
constraint-family population and per-family propagator-run cost attribution.
No search is performed: the inventory modes only parse and compile, and the
cost modes time the registered propagators on the sampled states of a
bounded scheduled walk.

Modes:

  --files FILE...                parse + compile inventory (satisfy route)
  --optfiles FILE...             parse + compile inventory (optimize route)
  --battery                      the same inventory for the 43-case harness
                                 battery (in-process sources)
  --cost FUEL SAMPLES FILE...    per-family run attribution on the heuristic
                                 satisfiability configuration of each file
  --costopt BOUND FUEL SAMPLES FILE...
                                 the same on the bounded optimization
                                 configuration (`curP po spec (some bound)`)

Each inventory line prints the raw source constraint-name histogram, the
compiled family histogram, the registered-propagator family histogram, the
propagator/watch/seed counts and the route gate result. Each cost line
prints per-family accumulated propagator-run nanoseconds, run counts and
emission counts (sorted by time), on the same sampling schedule as
`tests_heur_timing` (first SAMPLE sampled active steps, every 1500 active
steps, in-process wall clock, `IO.lazyPure`-forced).

Run from the repository root:

  lake env lean --run Tests/E1/FamInventory.lean -- --files FILE...
-/
import LeanFzn.Legacy.Integration.LcgHeur
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepSched
import LeanFzn.Legacy.Integration.LcgOptimize
import Tests.UIP.LcgHarnessBattery
open LeanFzn
open LeanFzn.Solver.Propagation LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.Core

namespace Tests.E1.FamInventory

/-! ## Naming and histograms -/

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
  | .setInSlot .. => "setInSlot"
  | .setInReifSlot .. => "setInReifSlot"
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

/-- Insert or bump a (name, count) pair in a histogram (kept name-sorted). -/
def bump (h : List (String × Nat)) (name : String) : List (String × Nat) :=
  if h.any (·.1 == name) then
    h.map fun p => if p.1 == name then (p.1, p.2 + 1) else p
  else
    (h ++ [(name, 1)]).mergeSort (fun a b => a.1 ≤ b.1)

def renderHist (h : List (String × Nat)) : String :=
  "[" ++ ",".intercalate (h.map fun p => s!"{p.1}x{p.2}") ++ "]"

/-- Flushed print (a killed run must not lose the lines already measured). -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-! ## Inventory (parse + compile only) -/

/-- One inventory line for a compiled problem. -/
def invLine (label : String) (p : LeanFzn.Compiler.CompiledProblem
    LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) (route : String) : IO Unit := do
  let props := LeanFzn.Integration.lcgProps p
  let watches := props.foldl (fun a pr => a + pr.watches.length) 0
  let seeds := LeanFzn.Compiler.seedClauses p.constraints
  let fam := p.constraints.foldl (fun h dc => bump h (dcName dc)) []
  let propFam := (p.constraints.filter fun dc =>
    (LeanFzn.Solver.Propagation.propagatorOfProved dc).isSome).foldl
    (fun h dc => bump h (dcName dc)) []
  let famOff := (p.constraints.filter fun dc =>
    LeanFzn.Solver.UIP.LcgFamilies.lcgFamB dc == false).foldl
    (fun h dc => bump h (dcName dc)) []
  let domSum := p.domains.foldl (fun a d => a + d.length) 0
  let domMax := p.domains.foldl (fun a d => max a d.length) 0
  say s!"INV {label} route={route} constraints={p.constraints.length} props={props.length} \
watches={watches} seeds={seeds.length} doms={p.domains.length} domSum={domSum} domMax={domMax} \
fam={renderHist fam} propfam={renderHist propFam} famOffGate={renderHist famOff}"

/-- Raw source constraint-name histogram (before compilation). -/
def rawLine (label : String)
    (m : LeanFzn.Model) : IO Unit := do
  let h := m.constraints.foldl (fun h c => bump h c.name.name) []
  say s!"RAW {label} n={m.constraints.length} {renderHist h}"

/-- Inventory of one satisfiability file. -/
def invSat (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"INV {path} parse=ERROR {e.take 120}"
  | .ok m =>
    rawLine path m
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"INV {path} compile=ERROR {e.take 160}"
    | .ok p =>
      let routed := LeanFzn.Integration.lcgRouteGateMixed p
      invLine path p (if routed then "lcg" else "chrono")

/-- Inventory of one optimization file (the CLI's `compileModelOpt` route). -/
def invOpt (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"INV {path} parse=ERROR {e.take 120}"
  | .ok m =>
    rawLine path m
    match LeanFzn.Compiler.compileModelOpt m with
    | .error e => say s!"INV {path} compileOpt=ERROR {e.take 160}"
    | .ok (po, _) => invLine path po "optimize"

/-! ## Per-family run attribution on the sampled walk -/

/-- Per-family accumulated propagator-run cost. -/
structure FamStat where
  ns : Nat := 0
  runs : Nat := 0
  implied : Nat := 0
  conflict : Nat := 0

def FamStat.add (a b : FamStat) : FamStat :=
  { ns := a.ns + b.ns, runs := a.runs + b.runs,
    implied := a.implied + b.implied, conflict := a.conflict + b.conflict }

/-- Bump a family's statistic in an association list. -/
def bumpFam (t : List (String × FamStat)) (n : String) (f : FamStat) :
    List (String × FamStat) :=
  if t.any (fun p => p.1 == n) then
    t.map fun p => if p.1 == n then (p.1, p.2.add f) else p
  else t ++ [(n, f)]

/-- Force `act` inside the clock window (`IO.lazyPure` prevents dead-code
    elimination of unused pure expressions). -/
def timeIt {α : Type} (act : Unit → α) : IO (Nat × α) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  return (t1 - t0, a)

/-- Time every propagator of the paired list on the frame state, accumulating
    per family; returns the total nanoseconds and the updated table. -/
partial def timeProps (pairs : List (String × LeanFzn.Solver.Propagation.Propagator))
    (f : LeanFzn.Solver.Propagation.BranchFrame) (t : List (String × FamStat)) :
    IO (Nat × List (String × FamStat)) := do
  match pairs with
  | [] => return (0, t)
  | (n, pr) :: rest =>
      let (ns, r) ← timeIt (fun _ => pr.run (LeanFzn.Solver.Propagation.frameState f))
      let st := match r with
        | .stable => { ns := ns, runs := 1 }
        | .implied .. => { ns := ns, runs := 1, implied := 1 }
        | .conflict .. => { ns := ns, runs := 1, conflict := 1 }
      let (tl, t') ← timeProps rest f (bumpFam t n st)
      return (ns + tl, t')

structure CostAcc where
  steps : Nat := 0
  active : Nat := 0
  sampled : Nat := 0
  sampleNs : Nat := 0
  propNs : Nat := 0
  fam : List (String × FamStat) := []

/-- The family name paired with each registered propagator (same order as
    `lcgProps`/`heurProps`). -/
def propNames (p : LeanFzn.Compiler.CompiledProblem
    LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) : List String :=
  p.constraints.filterMap fun dc =>
    (LeanFzn.Solver.Propagation.propagatorOfProved dc).map (fun _ => dcName dc)

/-- Bounded scheduled walk on the heuristic configuration (the same sampling
    schedule as `tests_heur_timing`: first `samples` sampled active steps,
    every 1500 active steps). -/
partial def costWalk {leaf : Assignment → Bool} (fuel samples : Nat)
    (cfg : LeanFzn.Solver.UIP.SchedulerConfig leaf)
    (sched : LeanFzn.Solver.Propagation.PropScheduler)
    (pairs : List (String × LeanFzn.Solver.Propagation.Propagator))
    (acc : CostAcc) : IO CostAcc := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
      let pr := LeanFzn.Solver.UIP.phaseNextSched cfg sched
      let acc := { acc with steps := acc.steps + 1 }
      let isActive := cfg.conflict.isNone && cfg.status == .active
      let acc := if isActive then { acc with active := acc.active + 1 } else acc
      let acc ←
        if isActive && acc.active % 1500 == 1 && acc.sampled < samples then do
          let s0 ← IO.monoNanosNow
          let (tprop, fam') ← timeProps pairs cfg.branch.frame acc.fam
          let s1 ← IO.monoNanosNow
          let acc' : CostAcc := { acc with sampled := acc.sampled + 1, sampleNs := acc.sampleNs + (s1 - s0), propNs := acc.propNs + tprop, fam := fam' }
          pure acc'
        else pure acc
      match pr.1 with
      | .sat _ => return acc
      | .unsat => return acc
      | _ =>
        match pr.1.successor with
        | some n => costWalk fuel samples n pr.2 pairs acc
        | none => return acc

/-- Render the per-family table sorted by accumulated time (descending). -/
def renderFamCost (t : List (String × FamStat)) : String :=
  let sorted := t.mergeSort fun a b => a.2.ns ≥ b.2.ns
  String.intercalate " " (sorted.map fun p =>
    let us := p.2.ns / 1000
    s!"{p.1}:{us}us/{p.2.runs}i{p.2.implied}c{p.2.conflict}")

/-- Per-family attribution on the heuristic presentation of `p`. -/
def costReport (label : String) (fuel samples : Nat)
    (p : LeanFzn.Compiler.CompiledProblem
      LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) : IO Unit := do
  let hd := LeanFzn.Integration.LcgHeur.heurDomains p
  let props := LeanFzn.Integration.LcgHeur.heurProps p
  let leaf := LeanFzn.Integration.lcgLeaf p
  let cfg : LeanFzn.Solver.UIP.SchedulerConfig leaf :=
    LeanFzn.Solver.UIP.SchedulerConfig.init hd
      (LeanFzn.Compiler.seedClauses p.constraints) props
  let sched := LeanFzn.Solver.Propagation.PropScheduler.init props
  let pairs := (propNames p).zip props
  let t0 ← IO.monoNanosNow
  let acc ← costWalk fuel samples cfg sched pairs {}
  let t1 ← IO.monoNanosNow
  let share := if acc.propNs == 0 then 0
    else 100 * acc.propNs / max (t1 - t0) 1
  say s!"COST {label} steps={acc.steps} active={acc.active} sampled={acc.sampled} \
propNs={acc.propNs / 1000000}ms walkNs={(t1 - t0) / 1000000}ms propShareOfWalk={share}% \
namePairs={pairs.length}"
  say s!"FAMCOST {label} {renderFamCost acc.fam}"

def costSat (fuel samples : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"COST {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"COST {path} compile=ERROR {e.take 160}"
    | .ok p => costReport path fuel samples p

def costOpt (bound : Int) (fuel samples : Nat) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"COST {path} parse=ERROR {e.take 120}"
  | .ok m =>
    match LeanFzn.Compiler.compileModelOpt m with
    | .error e => say s!"COST {path} compileOpt=ERROR {e.take 160}"
    | .ok (po, spec) => costReport path fuel samples (LeanFzn.Integration.curP po spec (some bound))

def inventoryBattery : IO Unit := do
  for (name, src) in LcgHarness.battery do
    match LcgHarness.ofSource name src with
    | .error e => say s!"INV battery:{name} ERROR {e}"
    | .ok inst =>
      match inst.model with
      | some m => rawLine s!"battery:{name}" m
      | none => pure ()
      match inst.compiled with
      | some p =>
        let routed := LeanFzn.Integration.lcgRouteGateMixed p
        invLine s!"battery:{name}" p (if routed then "lcg" else "chrono")
      | none => say s!"INV battery:{name} compile=none"

/-- Inventory dispatching on the solve directive (satisfy vs optimize). -/
def invAuto (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"INV {path} parse=ERROR {e.take 120}"
  | .ok m =>
    rawLine path m
    match m.solve with
    | .satisfy _ =>
      match LeanFzn.Compiler.compileModelFull m with
      | .error e => say s!"INV {path} compile=ERROR {e.take 160}"
      | .ok p =>
        let routed := LeanFzn.Integration.lcgRouteGateMixed p
        invLine path p (if routed then "lcg" else "chrono")
    | .minimize _ _ | .maximize _ _ =>
      match LeanFzn.Compiler.compileModelOpt m with
      | .error e => say s!"INV {path} compileOpt=ERROR {e.take 160}"
      | .ok (po, _) => invLine path po "optimize"

def run (args : List String) : IO UInt32 := do
  match args with
  | "--files" :: files =>
    for f in files do invSat f
    return 0
  | "--optfiles" :: files =>
    for f in files do invOpt f
    return 0
  | "--auto" :: files =>
    for f in files do invAuto f
    return 0
  | "--battery" :: _ =>
    inventoryBattery
    return 0
  | "--cost" :: fuelS :: samplesS :: files =>
    let fuel := fuelS.toNat?.getD 4000
    let samples := samplesS.toNat?.getD 5
    for f in files do costSat fuel samples f
    return 0
  | "--costopt" :: boundS :: fuelS :: samplesS :: files =>
    let bound := Int.ofNat (boundS.toNat?.getD 0)
    let fuel := fuelS.toNat?.getD 1000000
    let samples := samplesS.toNat?.getD 5
    for f in files do costOpt bound fuel samples f
    return 0
  | _ =>
    IO.eprintln "usage: FamInventory (--files|--optfiles|--auto) FILE... | --battery | \
--cost FUEL SAMPLES FILE... | --costopt BOUND FUEL SAMPLES FILE..."
    return 2

end Tests.E1.FamInventory

/-- Entry point for `lake env lean --run`. -/
def main (args : List String) : IO UInt32 := Tests.E1.FamInventory.run args
