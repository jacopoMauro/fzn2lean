/-
File: Tests/Legacy/Integration/BisectRunner.lean

Purpose (PLAN F4, TEST-ONLY runner around the certified bisection driver):
exercise `optimizeBisect` without touching the `leanfzn` CLI, and compare its
terminal optimum with the complete linear route on tiny fixtures.

  * `smoke`     -- no arguments: maximize and minimize fixtures; the bisection
                   run and the linear `optimizeCertified` run must both be
                   complete and end at the same objective value; the streaming
                   wrapper must cover the returned run's incumbents;
  * `exhausted` -- no arguments: a vacuous `BisectProbe` returns `.exhausted`
                   on every round; the driver must fall back to the complete
                   linear route and still finish with the linear optimum;
  * `run FILE [flags]` -- run `optimizeBisect` on a model.  The runner adds
                   `--opt=bisect` itself, so the flags are the remaining
                   search options (`--var=annot --val=annot`, ...).  The
                   stable `RESULT` line is measurement evidence, not a proof.

The runner itself makes NO claim: every emitted solution comes from the
certified driver.  A process killed by the external measurement cap prints no
`RESULT` line and no completeness marker.

DAG: OptimizeBisect + LcgOptimize + Parser -> this test leaf.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.OptimizeBisect
import LeanFzn.Legacy.Integration.LcgOptimize
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

namespace Tests.Legacy.Integration.BisectRunner

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration

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

private def getLastObj (run : OptRun) : Option Int :=
  run.sols.getLast?.map Prod.snd

private def optionInt : Option Int → String
  | none => "-"
  | some i => toString i

/-- A probe with no terminal result: every round is `.exhausted`.  The
    `sat_sound`/`unsat_sound` fields are vacuous. -/
private def exhaustedProbe
    (p0 : CompiledProblem LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint)
    (spec : ObjectiveSpec) : BisectProbe p0 spec where
  probe := fun _ _ => .exhausted
  sat_sound := by
    intro prev mid a v h
    cases h
  unsat_sound := by
    intro prev mid h
    cases h

/-- The two tiny fixtures.  The maximize one has several improving values and
    the minimize one has a nonempty lower bound, so both directions exercise
    the normalized-key interval. -/
private def maxFixture : String :=
  "var 0..4: x;\nvar 0..4: y;\nvar 0..8: z;\n\
   constraint int_lin_eq([1,1,-1],[x,y,z],0);\nsolve maximize z;\n"

private def minFixture : String :=
  "var 0..8: x;\nvar 0..8: y;\nvar 0..16: z;\n\
   constraint int_lin_eq([1,1,-1],[x,y,z],0);\nsolve minimize z;\n"

private def parse (src : String) : IO (Option Model) := do
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"bisect-runner: parse error: {e}"
      pure none
  | .ok m => pure (some m)

/-- Compare a bisection run with a complete linear run on `m`. -/
private def compareWithLinear (name : String) (o : SearchConfig) (m : Model) :
    IO Bool := do
  match optimizeBisect o m, optimizeCertified (lcgSolver o) m with
  | .ok bs, .ok (_, ref) =>
      let okComplete := bs.run.complete && ref.complete
      let okObj := getLastObj bs.run == getLastObj ref
      let okProbes := bs.probes > 0
      if !okComplete then
        IO.eprintln s!"bisect-runner smoke: FAIL {name}: incomplete run"
      if !okObj then
        IO.eprintln s!"bisect-runner smoke: FAIL {name}: objective mismatch"
      if !okProbes then
        IO.eprintln s!"bisect-runner smoke: FAIL {name}: no bisection probe"
      pure (okComplete && okObj && okProbes)
  | .error e, _ =>
      IO.eprintln s!"bisect-runner smoke: FAIL {name}: bisect error: {e}"
      pure false
  | _, .error e =>
      IO.eprintln s!"bisect-runner smoke: FAIL {name}: linear error: {e}"
      pure false

/-- Exercise the streaming wrapper: with a no-op emitter the trace must cover
    the returned run's incumbents, and the run must still be complete. -/
private def streamSmoke : IO Bool := do
  let o : SearchConfig := { var := .annot, val := .annot }
  match ← parse maxFixture with
  | none => pure false
  | some m =>
      match ← optimizeBisectStream o m (fun _ => pure ()) with
      | .error e =>
          IO.eprintln s!"bisect-runner stream: FAIL: {e}"
          pure false
      | .ok summary =>
          let okComplete := summary.run.complete
          let okNonempty := !summary.emitted.isEmpty
          let okMembers := summary.emitted.all (fun t => summary.run.sols.contains t)
          let okLast := summary.emitted.getLast? == summary.run.sols.getLast?
          if okComplete && okNonempty && okMembers && okLast then
            say "bisect-runner stream: OK"
            pure true
          else
            IO.eprintln
              s!"bisect-runner stream: FAIL complete={okComplete} nonempty={okNonempty} members={okMembers} last={okLast}"
            pure false

/-- The no-argument smoke test. -/
private def smoke : IO UInt32 := do
  let o : SearchConfig := { var := .annot, val := .annot }
  match ← parse maxFixture with
  | none => pure 1
  | some maxM =>
      match ← parse minFixture with
      | none => pure 1
      | some minM =>
          let okMax ← compareWithLinear "maximize" o maxM
          let okMin ← compareWithLinear "minimize" o minM
          let okStream ← streamSmoke
          if okMax && okMin && okStream then
            say "bisect-runner smoke: OK"
            pure 0
          else
            pure 1

/-- Exercise the `.exhausted` branch: the driver must return the complete
    linear fallback and never invent a bisection claim. -/
private def exhaustedSmoke : IO UInt32 := do
  let o : SearchConfig := { var := .annot, val := .annot }
  match ← parse maxFixture with
  | none => pure 1
  | some m =>
      match compileModelOpt m with
      | .error e =>
          IO.eprintln s!"bisect-runner exhausted: compile error: {e}"
          pure 1
      | .ok (p, spec) =>
          match rootBounds? p spec with
          | none =>
              IO.eprintln "bisect-runner exhausted: no root bounds"
              pure 1
          | some (lo, hi) =>
              let bis := bisectLoop (exhaustedProbe p spec) (lcgSolver o)
                ((hi - lo).toNat + 1) lo hi [] none 0
              let lin := optLoop (lcgSolver o) p spec none
              let ok := bis.complete && lin.complete &&
                (bis.sols.getLast?.map Prod.snd == lin.sols.getLast?.map Prod.snd)
              if ok then
                say "bisect-runner exhausted: OK (linear fallback)"
                pure 0
              else
                IO.eprintln "bisect-runner exhausted: FAIL"
                pure 1

/-- Parse the public flags with `--opt=bisect` prepended, so incompatible
    options are rejected by the same parser as the CLI. -/
private def parseCfg (flags : List String) : Except String SearchConfig :=
  match parseSolveFlags ("--opt=bisect" :: flags) with
  | .error e => .error e
  | .ok (o, srcs) =>
      if !srcs.isEmpty then
        .error s!"unexpected positional arguments {srcs}"
      else
        .ok o

private def loadModel (file : String) : IO (Except String Model) := do
  let source ←
    try
      pure (some (← IO.FS.readFile file))
    catch e =>
      IO.eprintln s!"tests_bisect_runner: cannot read '{file}': {e}"
      pure none
  match source with
  | none => pure (.error "read")
  | some source =>
      match Parser.parseModel source with
      | .error e => pure (.error e)
      | .ok m =>
          if !LeanFzn.Checker.wellFormedFastB m then
            pure (.error "model is not well-formed")
          else
            pure (.ok m)

private def report (o : SearchConfig) (summary : BisectSummary) (ms : Nat)
    (file : String) : IO Unit :=
  say s!"RESULT\tmode=bisect\tvar={varName o.var}\tval={valName o.val}\t\
    act={if o.actBump then 1 else 0}\t\
    complete={if summary.run.complete then 1 else 0}\tsols={summary.run.sols.length}\t\
    probes={summary.probes}\tobj={optionInt (getLastObj summary.run)}\t\
    bound={optionInt summary.run.lastBound}\tms={ms}\tfile={file}"

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => smoke
  | ["exhausted"] => exhaustedSmoke
  | file :: flags =>
      match parseCfg flags with
      | .error e =>
          IO.eprintln s!"tests_bisect_runner: {e}"
          return 2
      | .ok o =>
          match ← loadModel file with
          | .error e =>
              IO.eprintln s!"tests_bisect_runner: {e}"
              return 3
          | .ok m =>
              let t0 ← IO.monoMsNow
              match optimizeBisect o m with
              | .error e =>
                  IO.eprintln s!"tests_bisect_runner: {e}"
                  return 3
              | .ok summary =>
                  let t1 ← IO.monoMsNow
                  report o summary (t1 - t0) file
                  if summary.run.complete then pure 0 else pure 4

end Tests.Legacy.Integration.BisectRunner

def main (args : List String) : IO UInt32 := Tests.Legacy.Integration.BisectRunner.run args
