/-
File: Tests/Integration/SeedRunner.lean

Purpose (PLAN F4, TEST-ONLY runner around the certified entries): run one
optimization model through either the linear certified stream
(`optimizeStream (lcgSolver o)`, the `--opt=linear` route) or the configured
seeded stream (`optimizeStreamSeedConfig o`, the `--opt=seeded` route with the
F2/F3 policy surface), and print a stable one-line result for the measurement
matrix:

  RESULT mode=... var=... val=... act=... complete=... sols=...
         solves=... obj=... bound=... seeds=... ms=... file=...

The runner itself makes NO claim: every emitted solution comes from the
certified drivers (`optimizeStream_eq`, `optimizeStreamSeedConfig_eq`), and a
`complete=1` line is the drivers' certified strict-bound infeasibility.  A
process killed by the external measurement cap prints no `RESULT` line (and
no `==========`), exactly the "budget exhausted => no claim" policy.  The
runner always exits 0 after a returned run, 4 for an incomplete returned run,
and 3/2 on compile/parse errors; `linear` never has seed sizes (`seeds=-`).

Usage (from the repo root):
  .lake/build/bin/tests_seed_runner seeded FILE [--var=annot --val=annot ...]
  .lake/build/bin/tests_seed_runner linear FILE [--var=annot --val=annot ...]

The flags are the public `parseSolveFlags` surface; `--opt` is taken from the
mode argument (so `--opt=seeded`'s not-yet-wired CLI gate is not involved).

DAG: LcgOptimize + LcgSeedConfig -> this test leaf.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.LcgOptimize
import LeanFzn.Legacy.Integration.LcgSeedConfig
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

namespace Tests.Integration.SeedRunner

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Solver.Propagation.DomainFiltering

private def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

private def varName : VarStrategy → String
  | .minc => "minc"
  | .annot => "annot"
  | .act => "act"
  | .domwdeg => "domwdeg"
  | .obj => "obj"

private def valName : ValStrategy → String
  | .min => "min"
  | .max => "max"
  | .median => "median"
  | .act => "act"
  | .annot => "annot"
  | .incumbent => "incumbent"

private def seedsString : List Nat → String
  | [] => "-"
  | xs => ",".intercalate (xs.map toString)

private def getLastObj (run : OptRun) : Option Int :=
  run.sols.getLast?.map Prod.snd

private def optionInt : Option Int → String
  | none => "-"
  | some i => toString i

/-- The optimization driver over the selected entry, with a compact progress
line per certified incumbent (flushed, so an external kill keeps the prefix). -/
private def runOne (seeded : Bool) (o : SearchConfig) (m : Model) :
    IO (Except String (OptRun × List Nat × Nat)) := do
  let n : IO.Ref Nat ← IO.mkRef 0
  let emit : Store → IO Unit := fun store => do
    let i ← n.get
    n.set (i + 1)
    say s!"c {i} obj={optionInt (m.solve.objective store)}"
  let t0 ← IO.monoMsNow
  if seeded then
    match ← optimizeStreamSeedConfig o m emit with
    | .error e => pure (.error e)
    | .ok s =>
        let t1 ← IO.monoMsNow
        pure (.ok (s.run, s.seeds, t1 - t0))
  else
    match ← optimizeStream (lcgSolver o) m emit with
    | .error e => pure (.error e)
    | .ok s =>
        let t1 ← IO.monoMsNow
        pure (.ok (s.run, [], t1 - t0))

private def usage : String :=
  "usage: tests_seed_runner linear|seeded FILE [--var=... --val=... --heur-act ...]"

/-- No-argument mode is the gate's self-test: both entries must agree on a
tiny complete optimization fixture for every static value presentation (the
full gate runs every executable with no arguments).  Returns 0 only when both
runs complete with the same objective and the seeded trace has one seed per
solve. -/
private def smoke : IO UInt32 := do
  let src := "var 0..4: x;\nvar 0..4: y;\nvar 0..9: z;\n\
    constraint int_lin_eq([1,2,-1],[x,y,z],0);\nsolve maximize z;\n"
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"seed-runner smoke: parse error: {e}"
      return 1
  | .ok m =>
      let mut ok := true
      for v in [ValStrategy.annot, .min, .max, .median, .act, .incumbent] do
        let o : SearchConfig := { var := .annot, val := v }
        let lr ← runOne false o m
        let sr ← runOne true o m
        match lr, sr with
        | .ok (lr, _, _), .ok (sr, seeds, _) =>
            let lok := lr.complete && sr.complete &&
              getLastObj lr == getLastObj sr &&
              seeds.length == sr.sols.length + 1
            if !lok then
              ok := false
              IO.eprintln s!"seed-runner smoke: FAIL val={valName v} \
                (linear complete={lr.complete} obj={optionInt (getLastObj lr)}, \
                seeded complete={sr.complete} obj={optionInt (getLastObj sr)}, \
                seeds={seedsString seeds} sols={sr.sols.length})"
        | .error e, _ =>
            ok := false
            IO.eprintln s!"seed-runner smoke: linear error (val={valName v}): {e}"
        | _, .error e =>
            ok := false
            IO.eprintln s!"seed-runner smoke: seeded error (val={valName v}): {e}"
      if ok then
        say "seed-runner smoke: OK"
        pure 0
      else
        pure 1

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => smoke
  | mode :: file :: flags =>
      let seeded ←
        match mode with
        | "seeded" => pure true
        | "linear" => pure false
        | _ =>
            IO.eprintln s!"tests_seed_runner: unknown mode '{mode}'"
            IO.eprintln usage
            return 2
      let (o0, srcs) ←
        match parseSolveFlags flags with
        | .error e =>
            IO.eprintln s!"tests_seed_runner: {e}"
            return 2
        | .ok v => pure v
      if !srcs.isEmpty then
        IO.eprintln s!"tests_seed_runner: unexpected positional arguments {srcs}"
        return 2
      let o : SearchConfig := { o0 with opt := if seeded then .seeded else .linear }
      let source ←
        try
          pure (some (← IO.FS.readFile file))
        catch e =>
          IO.eprintln s!"tests_seed_runner: cannot read '{file}': {e}"
          pure none
      let some source := source | return 3
      match Parser.parseModel source with
      | .error e =>
          IO.eprintln s!"tests_seed_runner: parse error: {e}"
          return 2
      | .ok m =>
          if !LeanFzn.Checker.wellFormedFastB m then
            IO.eprintln s!"tests_seed_runner: model is not well-formed"
            return 2
          match ← runOne seeded o m with
          | .error e =>
              IO.eprintln s!"tests_seed_runner: {e}"
              return 3
          | .ok (run, seeds, ms) =>
              let solves := if seeded then toString seeds.length else "-"
              say s!"RESULT\tmode={mode}\tvar={varName o.var}\tval={valName o.val}\t\
                act={if o.actBump then 1 else 0}\tcomplete={if run.complete then 1 else 0}\t\
                sols={run.sols.length}\tsolves={solves}\tobj={optionInt (getLastObj run)}\t\
                bound={optionInt run.lastBound}\tseeds={seedsString seeds}\tms={ms}\tfile={file}"
              if run.complete then pure 0 else pure 4
  | _ =>
      IO.eprintln usage
      return 2

end Tests.Integration.SeedRunner

def main (args : List String) : IO UInt32 := Tests.Integration.SeedRunner.run args
