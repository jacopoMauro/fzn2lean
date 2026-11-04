/-
Purpose: executable regression for the F1 option surface: default mapping,
legacy aliases, preset override order, repeated/unknown option rejection, and
the "not implemented yet" gate. No solver run; this is parser policy only.
Dependencies/DAG: Integration.SearchConfig -> this test leaf.
-/
import LeanFzn.Legacy.Integration.SearchConfig

namespace SearchConfigTest
open LeanFzn.Integration

private def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

private def expectError (name : String) (r : Except String α) (fragment : String) :
    IO Bool := do
  match r with
  | .error msg =>
      if containsSubstr msg fragment then
        pure true
      else
        IO.eprintln s!"FAIL {name}: error '{msg}' does not contain '{fragment}'"
        pure false
  | .ok _ =>
      IO.eprintln s!"FAIL {name}: expected an error"
      pure false

private def expectOk (name : String) (r : Except String (SearchConfig × List String))
    (p : SearchConfig × List String → Bool) : IO Bool := do
  match r with
  | .error msg =>
      IO.eprintln s!"FAIL {name}: unexpected error '{msg}'"
      pure false
  | .ok v =>
      if p v then pure true
      else
        IO.eprintln s!"FAIL {name}: wrong parse result {repr v}"
        pure false

def run : IO UInt32 := do
  let ok ← IO.mkRef true
  let check (b : Bool) : IO Unit := do
    if !b then ok.set false
  check (← expectOk "empty" (parseSolveFlags [])
    (fun (c, src) => c = { (default : SearchConfig) with var := .act, val := .min } &&
      c.engine = .core && src = []))
  check (← expectOk "core-default-var-only" (parseSolveFlags ["--var=minc"])
    (fun (c, _) => c.engine = .core && c.var = .minc && c.val = .act))
  check (← expectOk "core-default-preset" (parseSolveFlags ["--strategy=default"])
    (fun (c, _) => c = (default : SearchConfig)))
  check (← expectOk "source" (parseSolveFlags ["a.fzn", "--stats", "b.fzn"])
    (fun (c, src) => c.stats && src = ["a.fzn", "b.fzn"]))
  check (← expectOk "legacy" (parseSolveFlags
      ["--heur-obj-prio", "--heur-obj-bias", "--heur-act"])
    (fun (c, _) => c.objPrio && c.objBias && c.actBump &&
      c.toHeurOpts.objPrio && c.toHeurOpts.objBias && c.toHeurOpts.actBump))
  check (← expectOk "var-obj" (parseSolveFlags ["--var=obj"])
    (fun (c, _) => c.var = .obj && c.toHeurOpts.objPrio && c.engine = .kernel))
  check (← expectOk "limit" (parseSolveFlags ["--time-limit=2500"])
    (fun (c, _) => c.timeLimit = some 2500 && c.engine = .kernel))
  check (← expectOk "default-core-act-min" (parseSolveFlags ["--var=act", "--val=min"])
    (fun (c, _) => c.engine = .core && c.var = .act && c.val = .min))
  check (← expectOk "default-kernel-bisect" (parseSolveFlags ["--opt=bisect"])
    (fun (c, _) => c.engine = .kernel))
  check (← expectOk "default-kernel-opt-fast" (parseSolveFlags ["--strategy=opt-fast"])
    (fun (c, _) => c.engine = .kernel && c.opt = .seeded && c.val = .incumbent))
  check (← expectOk "certified" (parseSolveFlags ["--certified"])
    (fun (c, _) => c = { (default : SearchConfig) with var := .act, val := .min }))
  check (← expectOk "engine-kernel" (parseSolveFlags ["--engine=kernel"])
    (fun (c, _) => c = { (default : SearchConfig) with engine := .kernel }))
  check (← expectOk "engine-core" (parseSolveFlags ["--engine=core"])
    (fun (c, _) => c.engine = .core))
  check (← expectOk "engine-core-linear-options" (parseSolveFlags
      ["--engine=core", "--var=annot", "--val=median"])
    (fun (c, _) => c.engine = .core && c.var = .annot && c.val = .median))
  check (← expectError "engine-core-var-obj" (parseSolveFlags
      ["--engine=core", "--var=obj"])
    "'--var=obj' is not supported by '--engine=core'")
  check (← expectOk "engine-core-val-incumbent" (parseSolveFlags
      ["--engine=core", "--val=incumbent"])
    (fun (c, _) => c.engine = .core && c.val = .incumbent && c.opt = .linear))
  check (← expectError "engine-core-seeded-val-incumbent" (parseSolveFlags
      ["--engine=core", "--opt=seeded", "--val=incumbent"])
    "'--val=incumbent' is not supported by '--engine=core --opt=seeded'")
  check (← expectOk "engine-core-opt-seeded" (parseSolveFlags
      ["--engine=core", "--opt=seeded"])
    (fun (c, _) => c.engine = .core && c.opt = .seeded))
  check (← expectOk "engine-core-restart" (parseSolveFlags
      ["--engine=core", "--restart=luby"])
    (fun (c, _) => c.engine = .core && c.restart = .luby))
  check (← expectError "engine-core-time" (parseSolveFlags
      ["--engine=core", "--time-limit=100"])
    "'--time-limit' is not supported by '--engine=core'")
  check (← expectError "engine-bad" (parseSolveFlags ["--engine=foo"])
    "expected kernel or core")
  check (← expectError "engine-repeated" (parseSolveFlags
      ["--engine=kernel", "--engine=core"])
    "more than once")
  check (← expectOk "preset-default" (parseSolveFlags ["--strategy=default"])
    (fun (c, _) => c = (default : SearchConfig)))
  check (← expectOk "preset-override" (parseSolveFlags
      ["--strategy=annot", "--var=minc", "--val=act"])
    (fun (c, _) => c = (default : SearchConfig)))
  check (← expectOk "preset-annot" (parseSolveFlags ["--strategy=annot"])
    (fun (c, _) => c.var = .annot && c.val = .annot))
  check (← expectOk "var-annot" (parseSolveFlags ["--var=annot"])
    (fun (c, _) => c.var = .annot))
  check (← expectOk "val-annot" (parseSolveFlags ["--val=annot"])
    (fun (c, _) => c.val = .annot))
  check (← expectOk "annot-act" (parseSolveFlags ["--var=annot", "--heur-act"])
    (fun (c, _) => c.var = .annot && c.actBump))
  check (← expectOk "preset-then-explicit" (parseSolveFlags
      ["--strategy=default", "--var=obj", "--stats"])
    (fun (c, _) => c.var = .obj && c.stats))
  check (← expectOk "val-min" (parseSolveFlags ["--val=min"])
    (fun (c, _) => c.val = .min))
  check (← expectOk "val-max" (parseSolveFlags ["--val=max"])
    (fun (c, _) => c.val = .max))
  check (← expectOk "val-median" (parseSolveFlags ["--val=median"])
    (fun (c, _) => c.val = .median))
  check (← expectOk "val-incumbent" (parseSolveFlags ["--val=incumbent"])
    (fun (c, _) => c.val = .incumbent))
  check (← expectOk "annot-min" (parseSolveFlags ["--var=annot", "--val=min"])
    (fun (c, _) => c.var = .annot && c.val = .min))
  check (← expectOk "act-objbias" (parseSolveFlags ["--val=act", "--heur-obj-bias"])
    (fun (c, _) => c.val = .act && c.objBias))
  check (← expectError "annot-objbias" (parseSolveFlags
      ["--strategy=annot", "--heur-obj-bias"])
    "cannot be combined")
  check (← expectError "min-objbias" (parseSolveFlags
      ["--val=min", "--heur-obj-bias"])
    "cannot be combined")
  check (← expectError "incumbent-objbias" (parseSolveFlags
      ["--val=incumbent", "--heur-obj-bias"])
    "cannot be combined")
  check (← expectError "auto" (parseSolveFlags ["--strategy=auto"])
    "not implemented")
  check (← expectOk "restart" (parseSolveFlags
      ["--opt=seeded", "--restart=luby", "--restart-base=200"])
    (fun (c, _) => c.restart = .luby && c.restartBase = 200))
  check (← expectOk "preset-restarts" (parseSolveFlags ["--strategy=restarts"])
    (fun (c, _) => c.opt = .seeded && c.restart = .luby))
  check (← expectOk "restart-linear-core" (parseSolveFlags ["--restart=luby"])
    (fun (c, _) => c.engine = .core && c.restart = .luby))
  check (← expectError "restart-linear-kernel" (parseSolveFlags
      ["--engine=kernel", "--restart=luby"])
    "requires '--opt=seeded'")
  check (← expectError "restart-base-none" (parseSolveFlags ["--restart-base=200"])
    "requires '--restart")
  check (← expectError "restart-portfolio" (parseSolveFlags
      ["--opt=seeded", "--restart=luby", "--portfolio=opt-fast"])
    "cannot be combined")
  check (← expectOk "bisect" (parseSolveFlags ["--opt=bisect"])
    (fun (c, _) => c.opt = .bisect))
  check (← expectOk "bisect-incumbent" (parseSolveFlags
      ["--opt=bisect", "--val=incumbent"])
    (fun (c, _) => c.opt = .bisect && c.val = .incumbent))
  check (← expectOk "bisect-objbias" (parseSolveFlags
      ["--opt=bisect", "--heur-obj-bias"])
    (fun (c, _) => c.opt = .bisect && c.objBias))
  check (← expectError "bisect-time-limit" (parseSolveFlags
      ["--opt=bisect", "--time-limit=100"])
    "not implemented")
  check (← expectError "bisect-restart" (parseSolveFlags
      ["--opt=bisect", "--restart=luby"])
    "requires '--opt=seeded'")
  check (← expectError "bisect-portfolio" (parseSolveFlags
      ["--opt=bisect", "--portfolio=opt-fast"])
    "requires '--opt=seeded'")
  check (← expectOk "portfolio" (parseSolveFlags
      ["--opt=seeded", "--portfolio=opt-fast:1000,opt-fast"])
    (fun (c, _) => c.portfolio.isSome))
  check (← expectError "portfolio-linear" (parseSolveFlags
      ["--portfolio=opt-fast:1000,opt-fast"])
    "requires '--opt=seeded'")
  check (← expectError "portfolio-last-slice" (parseSolveFlags
      ["--opt=seeded", "--portfolio=opt-fast:1000"])
    "last portfolio entry")
  check (← expectError "portfolio-entry-seeded" (parseSolveFlags
      ["--opt=seeded", "--portfolio=annot:1000,opt-fast"])
    "must select '--opt=seeded'")
  check (← expectError "portfolio-outer-var" (parseSolveFlags
      ["--opt=seeded", "--var=annot", "--portfolio=opt-fast"])
    "self-contained")
  check (← expectError "portfolio-val" (parseSolveFlags
      ["--opt=seeded",
       "--portfolio=--opt=seeded --val=annot:1000,--opt=seeded --val=incumbent"])
    "value presentation")
  check (← expectError "portfolio-entry-act" (parseSolveFlags
      ["--opt=seeded", "--portfolio=--opt=seeded --var=act:1000,opt-fast"])
    "F7")
  check (← expectError "portfolio-entry-core" (parseSolveFlags
      ["--opt=seeded", "--portfolio=--engine=core --opt=seeded:1000,opt-fast"])
    "cannot set '--engine=core'")
  check (← expectError "portfolio-entry-stats" (parseSolveFlags
      ["--opt=seeded", "--portfolio=opt-fast --stats:1000,opt-fast"])
    "outer driver flag")
  check (← expectOk "primal-default" (parseSolveFlags [])
    (fun (c, _) => c.primal = .none && c.primalTime = 1000))
  check (← expectOk "primal-dive" (parseSolveFlags ["--primal=dive"])
    (fun (c, _) => c.primal = .dive && c.primalTime = 1000))
  check (← expectOk "primal-time" (parseSolveFlags
      ["--primal=dive", "--primal-time=250"])
    (fun (c, _) => c.primal = .dive && c.primalTime = 250))
  check (← expectOk "primal-none-time" (parseSolveFlags
      ["--primal=none", "--primal-time=1000"])
    (fun (c, _) => c.primal = .none))
  check (← expectError "primal-time-none" (parseSolveFlags ["--primal-time=999"])
    "requires '--primal=dive|lns'")
  check (← expectError "primal-time-zero" (parseSolveFlags
      ["--primal=dive", "--primal-time=0"])
    "must be positive")
  check (← expectError "primal-lns" (parseSolveFlags ["--primal=lns"])
    "F6.2")
  check (← expectError "primal-preset-lns" (parseSolveFlags ["--strategy=lns"])
    "F6.1")
  check (← expectError "primal-time-limit" (parseSolveFlags
      ["--primal=dive", "--time-limit=100"])
    "timed branch-and-bound adapter")
  check (← expectError "primal-seeded" (parseSolveFlags
      ["--primal=dive", "--opt=seeded"])
    "F6.1")
  check (← expectError "primal-bisect" (parseSolveFlags
      ["--primal=dive", "--opt=bisect"])
    "bisect")
  check (← expectError "primal-restart" (parseSolveFlags
      ["--primal=dive", "--opt=seeded", "--restart=luby"])
    "restart driver owns")
  check (← expectError "primal-portfolio" (parseSolveFlags
      ["--primal=dive", "--opt=seeded", "--portfolio=opt-fast"])
    "cannot be combined with '--portfolio'")
  check (← expectError "primal-bad" (parseSolveFlags ["--primal=foo"])
    "invalid value")
  check (← expectError "seed" (parseSolveFlags ["--seed=7"])
    "not implemented")
  check (← expectError "unknown" (parseSolveFlags ["--bogus"]) "unknown option")
  check (← expectError "repeated" (parseSolveFlags ["--var=obj", "--var=minc"])
    "more than once")
  check (← expectError "missing-value" (parseSolveFlags ["--time-limit"])
    "requires a value")
  check (← expectError "bad-nat" (parseSolveFlags ["--time-limit=x"])
    "natural number")
  if ← ok.get then
    IO.println "search-config parser: OK"
    pure 0
  else
    IO.eprintln "search-config parser: FAIL"
    pure 1

end SearchConfigTest

def main : IO UInt32 := SearchConfigTest.run
