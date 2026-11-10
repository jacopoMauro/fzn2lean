/-
File: Tests/Legacy/Integration/BudgetRunner.lean

Purpose (PLAN F5, TEST-ONLY runner around the budgeted/restart entries): run
one optimization model through

  * `plain`     -- the complete configured seeded route
                   (`lcgSeedSolverConfig o`, the F4 `--opt=seeded` route),
  * `probe`     -- the same route with the deterministic budget probes of
                   `lcgSeedSolverBudget o [B1,B2,...]` in front of every
                   seeded round, or
  * `portfolio` -- the pure restart/portfolio driver
                   (`optimizeRestartConfig kind base count o`).

It prints a stable one-line result for the measurement matrix:

  RESULT mode=... budgets=... var=... val=... act=... complete=... sols=...
         solves=... obj=... bound=... seeds=... ms=... file=...

The runner itself makes NO claim: every emitted solution comes from the
certified drivers.  A `complete=1` line is the final complete segment's
certified strict-bound infeasibility (`optimizePortfolioConfig_optimal` /
`optimizePortfolioConfig_unsat`); a budget probe that exhausts supports no
claim and the driver falls back to the complete route.  A process killed by
the external measurement cap prints no `RESULT` line (and no `==========`),
exactly the "budget exhausted => no claim" policy.

This executable tests historical budget/portfolio adapters. It does not
describe the current Core-only CLI's restart or optimization behavior.
The no-argument mode is a smoke test: plain, probe and the `none` portfolio
must agree on a tiny complete optimization fixture.

Usage (from the repo root):
  .lake/build/bin/tests_budget_runner plain FILE [--var=annot --val=annot ...]
  .lake/build/bin/tests_budget_runner probe 2000,4000,8000 FILE [flags]
  .lake/build/bin/tests_budget_runner portfolio none|luby|geom BASE COUNT FILE [flags]

DAG: LcgSeedConfig + OptimizeBudget + Parser + Checker -> this test leaf.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.LcgSeedConfig
import LeanFzn.Legacy.Integration.OptimizeBudget
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check

namespace Tests.Legacy.Integration.BudgetRunner

open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Integration

private def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

private def varName : VarStrategy → String
  | .minc => "minc"
  | .annot => "annot"
  | .act => "act"
  | .domwdeg => "domwdeg"
  | .wdeg => "wdeg"
  | .obj => "obj"

private def valName : ValStrategy → String
  | .min => "min"
  | .max => "max"
  | .median => "median"
  | .split => "split"
  | .act => "act"
  | .annot => "annot"
  | .incumbent => "incumbent"

private def seedsString : List Nat → String
  | [] => "-"
  | xs => ",".intercalate (xs.map toString)

private def natString : List Nat → String
  | [] => "-"
  | xs => ",".intercalate (xs.map toString)

private def getLastObj (run : OptRun) : Option Int :=
  run.sols.getLast?.map Prod.snd

private def optionInt : Option Int → String
  | none => "-"
  | some i => toString i

private def parseBudgets (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else s.splitOn "," |>.mapM (fun t => t.toNat?)

private def restartKind? : String → Option RestartKind
  | "none" => some .none
  | "luby" => some .luby
  | "geom" => some .geom
  | _ => none

/-- The streaming seeded loop at any `SeedCertSolver`, with a compact
progress line per certified incumbent (flushed, so an external kill keeps the
prefix).  Used for `plain` and `probe`; both share the same presentation and
emission path so their wall times are comparable. -/
private def runStream (S : SeedCertSolver) (o : SearchConfig) (m : Model)
    (tag : String) : IO (Except String (OptRun × List Nat × Nat)) := do
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      let p' := lcgConfigProblem p o
      let n : IO.Ref Nat ← IO.mkRef 0
      let t0 ← IO.monoMsNow
      let emit : Store → IO Unit := fun store => do
        let i ← n.get
        n.set (i + 1)
        let t ← IO.monoMsNow
        say s!"c {i} {tag} t={t - t0} obj={optionInt (m.solve.objective store)}"
      let r ← optimizeStreamSeedLoop S p' spec (fun a => p.toStore a) emit
        none (SeedDb.nil p'.domains)
      let t1 ← IO.monoMsNow
      pure (.ok (r.1, r.2, t1 - t0))

/-- The pure restart/portfolio driver (no streaming; an external kill leaves
no `RESULT` line). -/
private def runPortfolio (kind : RestartKind) (base count : Nat)
    (o : SearchConfig) (m : Model) : IO (Except String (PortfolioSummary × Nat)) := do
  let t0 ← IO.monoMsNow
  match optimizeRestartConfig kind base count o m with
  | .error e => pure (.error e)
  | .ok s =>
      let t1 ← IO.monoMsNow
      pure (.ok (s, t1 - t0))

private def usage : String :=
  "usage: tests_budget_runner plain FILE [--var=... --val=...]\n" ++
  "       tests_budget_runner probe B1,B2,... FILE [flags]\n" ++
  "       tests_budget_runner portfolio none|luby|geom BASE COUNT FILE [flags]"

/-- No-argument mode is the gate's self-test: plain, probe and the `none`
portfolio must agree on a tiny complete optimization fixture (same objective,
all complete), and the seed traces must have one entry per solve. -/
private def smoke : IO UInt32 := do
  let src := "var 0..2: x;\nvar 0..2: y;\nvar 0..2: z;\n\
    constraint int_lin_eq([1,1,-1],[x,y,z],0);\nsolve maximize z;\n"
  match Parser.parseModel src with
  | .error e =>
      IO.eprintln s!"budget-runner smoke: parse error: {e}"
      return 1
  | .ok m =>
      let o : SearchConfig := { var := .annot, val := .annot }
      let plain ← runStream (lcgSeedSolverConfig o) o m "smoke-plain"
      let probe ← runStream (lcgSeedSolverBudget o [1, 2, 3, 7]) o m "smoke-probe"
      let port ← runPortfolio .none 1 0 o m
      let okP :=
        match plain, probe with
        | .ok (lr, _, _), .ok (pr, seeds, _) =>
            lr.complete && pr.complete && getLastObj lr == getLastObj pr &&
              seeds.length == pr.sols.length + 1
        | _, _ => false
      let okR :=
        match plain, port with
        | .ok (lr, _, _), .ok (sr, _) =>
            lr.complete && sr.complete && getLastObj lr == sr.sols.getLast?.map Prod.snd
        | _, _ => false
      if !okP then
        IO.eprintln "budget-runner smoke: FAIL (plain vs probe)"
      if !okR then
        IO.eprintln "budget-runner smoke: FAIL (plain vs portfolio none)"
      if okP && okR then
        say "budget-runner smoke: OK"
        pure 0
      else
        pure 1

/-- Parse the public solve flags and reject positional leftovers. -/
private def parseCfg (flags : List String) : Except String SearchConfig :=
  match parseSolveFlags flags with
  | .error e => .error e
  | .ok (o, srcs) =>
      if !srcs.isEmpty then
        .error s!"unexpected positional arguments {srcs}"
      else if o.timeLimit.isSome then
        .error "the test runner uses an external wall cap; --time-limit is not wired"
      else if o.restart != .none || o.restartBase != 100 then
        .error "use the positional restart arguments, not --restart/--restart-base"
      else if o.portfolio.isSome then
        .error "use the positional portfolio arguments, not --portfolio"
      else if o.seed.isSome then
        .error "--seed is not implemented (F5/F6)"
      else
        .ok { o with opt := .seeded }

private def loadModel (file : String) : IO (Except String Model) := do
  let source ←
    try
      pure (some (← IO.FS.readFile file))
    catch e =>
      IO.eprintln s!"tests_budget_runner: cannot read '{file}': {e}"
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

private def report (mode budgets : String) (o : SearchConfig) (run : OptRun)
    (seeds : List Nat) (ms : Nat) (file : String) : IO Unit :=
  say s!"RESULT\tmode={mode}\tbudgets={budgets}\tvar={varName o.var}\t\
    val={valName o.val}\tact={if o.actBump then 1 else 0}\t\
    complete={if run.complete then 1 else 0}\tsols={run.sols.length}\t\
    solves={seeds.length}\tobj={optionInt (getLastObj run)}\t\
    bound={optionInt run.lastBound}\tseeds={seedsString seeds}\tms={ms}\tfile={file}"

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => smoke
  | "plain" :: file :: flags =>
      match parseCfg flags with
      | .error e =>
          IO.eprintln s!"tests_budget_runner: {e}"
          return 2
      | .ok o =>
          match ← loadModel file with
          | .error e =>
              IO.eprintln s!"tests_budget_runner: {e}"
              return 3
          | .ok m =>
              match ← runStream (lcgSeedSolverConfig o) o m "plain" with
              | .error e =>
                  IO.eprintln s!"tests_budget_runner: {e}"
                  return 3
              | .ok (run, seeds, ms) =>
                  report "plain" "-" o run seeds ms file
                  if run.complete then pure 0 else pure 4
  | "probe" :: budgetArg :: file :: flags =>
      match parseBudgets budgetArg with
      | none =>
          IO.eprintln s!"tests_budget_runner: bad budget list '{budgetArg}'"
          return 2
      | some budgets =>
          match parseCfg flags with
          | .error e =>
              IO.eprintln s!"tests_budget_runner: {e}"
              return 2
          | .ok o =>
              match ← loadModel file with
              | .error e =>
                  IO.eprintln s!"tests_budget_runner: {e}"
                  return 3
              | .ok m =>
                  match ← runStream (lcgSeedSolverBudget o budgets) o m "probe" with
                  | .error e =>
                      IO.eprintln s!"tests_budget_runner: {e}"
                      return 3
                  | .ok (run, seeds, ms) =>
                      report "probe" (natString budgets) o run seeds ms file
                      if run.complete then pure 0 else pure 4
  | "portfolio" :: kindArg :: baseArg :: countArg :: file :: flags =>
      match restartKind? kindArg, baseArg.toNat?, countArg.toNat? with
      | some kind, some base, some count =>
          match parseCfg flags with
          | .error e =>
              IO.eprintln s!"tests_budget_runner: {e}"
              return 2
          | .ok o =>
              match ← loadModel file with
              | .error e =>
                  IO.eprintln s!"tests_budget_runner: {e}"
                  return 3
              | .ok m =>
                  match ← runPortfolio kind base count o m with
                  | .error e =>
                      IO.eprintln s!"tests_budget_runner: {e}"
                      return 3
                  | .ok (s, ms) =>
                      let run : OptRun := ⟨s.sols, s.complete, s.lastBound⟩
                      report "portfolio" s!"{kindArg}:{base}:{count}" o run
                        s.seeds ms file
                      if s.complete then pure 0 else pure 4
      | _, _, _ =>
          IO.eprintln s!"tests_budget_runner: bad portfolio arguments"
          return 2
  | _ =>
      IO.eprintln usage
      return 2

end Tests.Legacy.Integration.BudgetRunner

def main (args : List String) : IO UInt32 := Tests.Legacy.Integration.BudgetRunner.run args
