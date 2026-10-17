import LeanFzn.Integration.CertifiedSolve
import Tests.UIP.LcgHarnessBattery

/-!
File: Tests/E1/P3bGateTiming.lean

P3b measurement runner: the route gate before/after linearisation.

The CLI solve path's route gate (`LeanFzn.Integration.lcgRouteGateMixed`)
contains the mixed kit gate `LcgMixedCompiledKit.mixedKitGateB`, whose
per-domain `decide ((d.map Value.intView).Nodup)` is quadratic in the domain
size.  P3b added the sort-based twin `mixedKitGateFastB` (proved equal by
`mixedKitGateFastB_eq`) and the route now runs on it.  This runner reports, per
FILE (all timings are compiled in-process wall clocks, pure results forced
inside the timer with `IO.lazyPure`):

* `fastMs`   — the fast per-domain view duplicate check over ALL domains
  (`viewsNodupFastB`, the check the route gate now uses);
* `oldBigMs` / `oldBigCmp` — the OLD quadratic decider on the SINGLE largest
  domain (bounded work, so the runner itself stays usable) and its comparison
  budget |d|*(|d|-1)/2;
* `oldAllCmp` — the comparison budget of the old decider over ALL domains
  (Σ |d|*(|d|-1)/2), i.e. the reason the old gate takes minutes: the old
  number is the work the route gate did per evaluation;
* `routeGateMs` — the full route gate `lcgRouteGateMixed` (gateOk ∧
  domPruningOkB ∧ fast kit gate).

Usage: `lake build tests_p3b_gate` then
`./.lake/build/bin/tests_p3b_gate FILE...`
-/

namespace Tests.E1.P3bGateTiming

open LeanFzn

/-- Flushed print (a killed run must not lose the files already measured). -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- The pairwise comparison budget of the quadratic `Nodup` decider on one
domain of `n` values. -/
def quadCmp (n : Nat) : Nat := n * (n - 1) / 2

def profileFile (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let lcgp := LeanFzn.Integration.toLCG p
      let doms := lcgp.domains
      let domN := doms.length
      let domSum := doms.foldl (fun a d => a + d.length) 0
      let domMax := doms.foldl (fun a d => max a d.length) 0
      let allCmp := doms.foldl (fun a d => a + quadCmp d.length) 0
      -- the fast check (the route gate's actual per-domain test), all domains
      let t0 ← IO.monoNanosNow
      let fastOk ← IO.lazyPure fun _ =>
        doms.all (fun d => LeanFzn.Solver.UIP.LcgMixedCompiledKit.viewsNodupFastB
          (d.map LeanFzn.Semantics.Value.intView))
      let t1 ← IO.monoNanosNow
      -- the OLD quadratic decider on the largest domain only (bounded)
      let big := doms.foldl (fun a d => if a.length < d.length then d else a) []
      let t2 ← IO.monoNanosNow
      let oldBigOk ← IO.lazyPure fun _ =>
        decide ((big.map LeanFzn.Semantics.Value.intView).Nodup)
      let t3 ← IO.monoNanosNow
      -- the full route gate (the gate the CLI evaluates)
      let t4 ← IO.monoNanosNow
      let routed ← IO.lazyPure fun _ => LeanFzn.Integration.lcgRouteGateMixed p
      let t5 ← IO.monoNanosNow
      say s!"GATE {path} domN={domN} domSum={domSum} domMax={domMax} \
        fast={fastOk} fastMs={(t1 - t0) / 1000000} \
        oldBig={oldBigOk} oldBigMs={(t3 - t2) / 1000000} oldBigCmp={quadCmp big.length} \
        oldAllCmp={allCmp} route={routed} routeGateMs={(t5 - t4) / 1000000}"

/-- `--crosscheck FILE...`: evaluate BOTH gates in full (the equality theorem is
`mixedKitGateFastB_eq`; this is the runtime sanity check). The old gate is the
quadratic one, so only use files whose Σ|d|²/2 budget is small. -/
def crosscheckFile (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match LeanFzn.Parser.parseModel src with
  | .error e => say s!"FILE {path} parse=ERROR {e.take 120}"
  | .ok m =>
    let ms := { m with solve := .satisfy [] }
    match LeanFzn.Compiler.compileModelFull ms with
    | .error e => say s!"FILE {path} compile=ERROR {e.take 120}"
    | .ok p =>
      let lcgp := LeanFzn.Integration.toLCG p
      let t0 ← IO.monoNanosNow
      let slowOk ← IO.lazyPure fun _ =>
        LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateB lcgp
      let t1 ← IO.monoNanosNow
      let fastOk ← IO.lazyPure fun _ =>
        LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB lcgp
      let t2 ← IO.monoNanosNow
      say s!"XCHECK {path} slowGate={slowOk} slowMs={(t1 - t0) / 1000000} \
        fastGate={fastOk} fastMs={(t2 - t1) / 1000000} equal={slowOk == fastOk}"

/-- `--battery-crosscheck`: evaluate BOTH gates on every instance of the
`LcgHarness` battery (43 instances, all small) and report mismatches. Kernel
statement of the same fact: `mixedKitGateFastB_eq`. -/
def batteryCrosscheck : IO Unit := do
  let mut n := 0
  let mut bad := 0
  for (name, src) in LcgHarness.battery do
    match LeanFzn.Parser.parseModel src with
    | .error e =>
        bad := bad + 1
        say s!"XBATT {name} parseError {e.take 80}"
    | .ok m =>
      let ms := { m with solve := .satisfy [] }
      match LeanFzn.Compiler.compileModelFull ms with
      | .error e =>
          bad := bad + 1
          say s!"XBATT {name} compileError {e.take 80}"
      | .ok p =>
        let lcgp := LeanFzn.Integration.toLCG p
        let slowOk ← IO.lazyPure fun _ =>
          LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateB lcgp
        let fastOk ← IO.lazyPure fun _ =>
          LeanFzn.Solver.UIP.LcgMixedCompiledKit.mixedKitGateFastB lcgp
        n := n + 1
        if slowOk != fastOk then
          bad := bad + 1
          say s!"XBATT {name} MISMATCH slow={slowOk} fast={fastOk}"
  say s!"XBATT TOTAL instances={n} mismatches={bad}"

def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println "usage: tests_p3b_gate FILE... | --crosscheck FILE... | --battery-crosscheck"
      return 2
  | ["--battery-crosscheck"] =>
      batteryCrosscheck
      return 0
  | "--crosscheck" :: files =>
      for f in files do
        crosscheckFile f
      return 0
  | files =>
      for f in files do
        profileFile f
      return 0

end Tests.E1.P3bGateTiming

def main (args : List String) : IO UInt32 := Tests.E1.P3bGateTiming.run args
