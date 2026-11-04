/-
N1 spike runner (branch task/n1-spike only; never merged as is).

Usage:
  tests_core_spike [--engine=core|kernel] [--var=minc|annot]
    [--val=min|max|median|act|annot|incumbent] [--fuel=N] [--stats]
    [--compare] FILE.fzn

Prints the verdict and, on SAT, the emitted FlatZinc solution; counters go
to stderr with --stats.  `--compare` also runs the kernel and reports a
verdict disagreement on stderr.
-/
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Compiler.Normalize
import LeanFzn.Legacy.Integration.CertifiedSolve
import LeanFzn.Legacy.Integration.SearchConfig
import LeanFzn.Legacy.Integration.StrategyDriver
import LeanFzn.Legacy.Integration.LcgHeur
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepSched
import LeanFzn.Engine

open LeanFzn LeanFzn.Parser LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP
open LeanFzn.Semantics
open LeanFzn.Engine

namespace Tests.Engine

structure RunArgs where
  engine : String := "core"
  var : VarStrategy := .minc
  val : ValStrategy := .act
  fuel : Nat := 1000000
  /-- Bounded kernel walk budget (scheduler steps); measurement only. -/
  kwalk : Option Nat := none
  stats : Bool := false
  compare : Bool := false
  path : Option String := none
  deriving Repr

def parseVar : String → Except String VarStrategy
  | "minc" => .ok .minc
  | "annot" => .ok .annot
  | "act" => .ok .act
  | "obj" => .ok .obj
  | s => .error s!"invalid --var={s}"

def parseVal : String → Except String ValStrategy
  | "min" => .ok .min
  | "max" => .ok .max
  | "median" => .ok .median
  | "act" => .ok .act
  | "annot" => .ok .annot
  | "incumbent" => .ok .incumbent
  | s => .error s!"invalid --val={s}"

def parseArgs (args : List String) : Except String RunArgs := do
  let mut r : RunArgs := {}
  for arg in args do
    if arg == "--stats" then r := { r with stats := true }
    else if arg == "--compare" then r := { r with compare := true }
    else if arg.startsWith "--engine=" then
      let v := (arg.drop "--engine=".length).toString
      if v == "core" || v == "kernel" then r := { r with engine := v }
      else throw s!"invalid --engine={v}"
    else if arg.startsWith "--var=" then
      r := { r with var := ← parseVar (arg.drop "--var=".length).toString }
    else if arg.startsWith "--val=" then
      r := { r with val := ← parseVal (arg.drop "--val=".length).toString }
    else if arg.startsWith "--fuel=" then
      let v := (arg.drop "--fuel=".length).toString
      match v.toNat? with
      | some n => r := { r with fuel := n }
      | none => throw s!"invalid --fuel={v}"
    else if arg.startsWith "--kwalk=" then
      let v := (arg.drop "--kwalk=".length).toString
      match v.toNat? with
      | some n => r := { r with kwalk := some n }
      | none => throw s!"invalid --kwalk={v}"
    else if arg.startsWith "--" then throw s!"unknown flag {arg}"
    else r := { r with path := some arg }
  if r.path.isNone then throw "missing FILE.fzn"
  return r

def verdictName : LeanFzn.Engine.CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

def kernelVerdictName : LeanFzn.Solver.Core.SearchResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .unknown => "unknown"

def emitCoreStats (s : LeanFzn.Engine.EngineStats) (wall : Nat) : IO Unit :=
  IO.eprintln s!"core stats: decisions={s.decisions} propagations={s.propagations} \
conflicts={s.conflicts} learned={s.learned} gaveUp={s.gaveUp} wall={wall}ms"

def emitKernelStats (s : LeanFzn.Solver.Propagation.SearchStats) (wall : Nat) : IO Unit :=
  IO.eprintln s!"kernel stats: decisions={s.decisions} steps={s.steps} \
propagations={s.propagations} conflicts={s.conflicts} learned={s.learnedClauses} wall={wall}ms"

/-- Bounded kernel walk: run the kernel's scheduled dispatcher for at most
`fuel` transitions and return the final configuration.  The counters in
`cfg.stats` are the kernel's own `SearchStats`, so this is the exact kernel
inner loop (not a reimplementation); it is used only because the complete
kernel entry has no step budget and does not reach a 10 s cap on the
C-panel. -/
def kernelWalk (fuel : Nat) {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (cfg : SchedulerConfig leaf) (sched : PropScheduler) : SchedulerConfig leaf :=
  match fuel with
  | 0 => cfg
  | f + 1 =>
      let (tr, sched') := phaseNextSched cfg sched
      match tr.successor with
      | some cfg' => kernelWalk f cfg' sched'
      | none => cfg

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
      IO.eprintln s!"tests_core_spike: {e}"
      return 2
  | .ok r =>
    let path := r.path.getD ""
    let src ←
      try IO.FS.readFile path
      catch e =>
        IO.eprintln s!"tests_core_spike: cannot read '{path}': {e}"
        return 2
    match Parser.parseModel src with
    | .error e =>
        IO.eprintln s!"tests_core_spike: parse error: {e}"
        return 2
    | .ok model =>
      if !LeanFzn.Checker.wellFormedFastB model then
        IO.eprintln "tests_core_spike: model is not well-formed"
        return 2
      match model.solve with
      | .minimize _ _ | .maximize _ _ =>
          IO.eprintln "tests_core_spike: optimization is outside the N1 spike"
          return 2
      | .satisfy _ =>
        match compileModelFull model with
        | .error e =>
            IO.eprintln s!"tests_core_spike: compile error: {e}"
            return 2
        | .ok p =>
          let o : SearchConfig := { var := r.var, val := r.val }
          if r.engine == "kernel" then
            match r.kwalk with
            | some kf =>
                let start ← IO.monoMsNow
                let hd := LcgHeur.heurDomains p
                let props := LcgHeur.heurProps p
                let leaf := lcgLeaf p
                let cfg0 : SchedulerConfig leaf :=
                  SchedulerConfig.init hd
                    (LeanFzn.Compiler.seedClauses p.constraints) props
                let sched := PropScheduler.init props
                let s ← IO.lazyPure (fun _ => (kernelWalk kf cfg0 sched).stats)
                let wall := (← IO.monoMsNow) - start
                IO.eprintln s!"kernel walk stats: steps={s.steps} \
decisions={s.decisions} propagations={s.propagations} \
conflicts={s.conflicts} learned={s.learnedClauses} wall={wall}ms"
                return 0
            | none =>
                let start ← IO.monoMsNow
                let (res, ks) := solveSearchConfigStats p o
                let wall := (← IO.monoMsNow) - start
                if r.stats then emitKernelStats ks wall
                match res with
                | .sat a =>
                    IO.println (emitCertifiedSolution model (p.toStore a))
                    return 0
                | .unsat =>
                    IO.println "=====UNSATISFIABLE====="
                    return 1
                | .unknown =>
                    IO.eprintln "tests_core_spike: kernel unknown"
                    return 3
          else
            let start ← IO.monoMsNow
            let (res, cs) := coreSolveFull p o r.fuel
            let wall := (← IO.monoMsNow) - start
            if r.stats then emitCoreStats cs wall
            if r.compare then
              let kres := solveSearchConfig p o
              let kv := kernelVerdictName kres
              let cv := verdictName res
              if kv != cv then
                IO.eprintln s!"tests_core_spike: WARNING verdict disagreement: core={cv} kernel={kv}"
            match res with
            | .sat a =>
                IO.println (emitCertifiedSolution model (p.toStore a))
                return 0
            | .unsat =>
                IO.println "=====UNSATISFIABLE====="
                return 1
            | .gaveUp =>
                IO.eprintln s!"tests_core_spike: gave up (fuel={r.fuel})"
                return 3

end Tests.Engine

def main (args : List String) : IO UInt32 := Tests.Engine.main args
