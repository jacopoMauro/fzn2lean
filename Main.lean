/-
File: Main.lean

Purpose:
  CLI entry point (`leanfzn`) exposing the verified front door
  (`check`), the solver stack (`solve` with --prop, --mrv, --budget,
  --nogoods), all-solutions enumeration (`enum`), and branch-and-bound
  optimization (`optimize`).

Dependencies:
  LeanFzn (FznCheck.checkModelSolution, `Outcome` classifications),
  solver.Solver (solveModelWith, enumModel, optimizeModel).

Why:
  Both libraries together give the executable its two faces: model and
  solution validation for `check`, and sat/unsat/optimal verdicts with
  emitted solution text for `solve`/`enum`/`optimize`.

DAG:
  LeanFzn + solver/Solver -> Main -> leanfzn executable
-/

import LeanFzn
import solver.Solver
import solver.Direct.Cli

open LeanFzn

/-- The one-line usage summary, printed on argument-level errors. -/
private def usageString : String :=
"usage: leanfzn [FILE|-] | leanfzn check MODEL.fzn SOLUTION.txt | \
  leanfzn solve [--certified] [--prop] [--mrv] [--budget N] [--nogoods] FILE|- | \
  leanfzn enum FILE|- | leanfzn optimize FILE|-"

private def readFileArg (path : String) : IO (Except String String) := do
  try
    return .ok (← IO.FS.readFile path)
  catch e =>
    return .error s!"cannot read '{path}': {e}"

private def readSource (args : List String) : IO (Except String String) := do
  match args with
  | [] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | ["-"] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | [path] =>
      readFileArg path
  | _ =>
      return .error usageString

/-- Read the model source (a file, `-`, or stdin) and parse it; the
    carried error is the message to print after the `leanfzn: `
    prefix (callers exit 2, the CLI-level error class, as in
    `check`). -/
private def parseModelSource (args : List String) : IO (Except String Model) := do
  match ← readSource args with
  | .error e => return .error e
  | .ok src =>
      match Parser.parseModel src with
      | .error e => return .error s!"parse error: {e}"
      | .ok model => return .ok model

/-! ## The `check` subcommand

The CLI front door runs `LeanFzn.Check.checkModelSolution`, the
verified wrapper that establishes both preconditions of
`checkSolutionFull_correct` itself: static well-formedness (through the
fast twin `wellFormedFastB`, proved equivalent to `WellFormed` by
`wellFormedFastB_iff`) and predicate checkability (through
`firstUnsupported`).  Each failure mode gets its own diagnostic and
exit code:

* `0` — solution accepted;
* `1` — solution rejected: a domain, initializer, or constraint
  condition is unsatisfied;
* `2` — malformed model: static well-formedness failed;
* `3` — unsupported predicate: the model uses a constraint name
  without a verified interpretation here (unknown name, a model
  declaration, or an intentionally unsupported global — the list is
  `Globals.globalsUnsupported`);
* `4` — malformed solution string: parse failure, or an assignment to
  a parameter, an unknown name, or the same name twice (A7/A10);
* `2` — usage/IO/parse errors of the CLI itself (kept from the
  previous behaviour; models that fail to parse are reported as parse
  errors with exit 2).
-/

/-- The `check` subcommand: parse the model, run the verified front
    door, and report the classified verdict. -/
private def runCheck (modelPath solPath : String) : IO UInt32 := do
  match ← readFileArg modelPath with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok msrc =>
    match Parser.parseModel msrc with
    | .error e =>
        IO.eprintln s!"leanfzn: parse error: {e}"
        return 2
    | .ok model =>
      match ← readFileArg solPath with
      | .error e =>
          IO.eprintln s!"leanfzn: {e}"
          return 2
      | .ok sol =>
        let outcome := Check.checkModelSolution model sol
        match outcome with
        | .accepted =>
            IO.println "solution accepted"
            return 0
        | .unsatisfied =>
            IO.println "solution rejected: unsatisfied condition"
            return 1
        | .malformedModel reason =>
            IO.eprintln s!"leanfzn: {reason}"
            return 2
        | .unsupportedPredicate name =>
            IO.eprintln
              s!"leanfzn: unsupported predicate: {name} (no verified interpretation)"
            return 3
        | .malformedSolution reason =>
            IO.eprintln s!"leanfzn: malformed solution: {reason}"
            return 4

/-! ## The `solve` subcommand

Runs the composed front door `Solver.solveModelWith`
(`solver/Config.lean`) on the parsed model.  The default
configuration is all switches off with no budget, which dispatches to
the reference `solveModel`; the flags select the other verified entry
points:

* `--prop` — fixpoint propagation with branch pruning;
* `--mrv` — minimum-remaining-values branch ordering;
* `--budget N` — budgeted restarts, which may report `unknown`;
* `--nogoods` — decision-trail NoGood learning.

The supported combinations are each switch alone and `--prop` with
`--mrv` together; other combinations are refused by the solver as
unsupported (exit 3).  A `sat` text is printed exactly as the
verified emitter produced it (it ends with the `----------`
separator, the FlatZinc convention).  Exit codes:

* `0` — a solution was found (SAT soundness:
  `solveModelWith_sat_sound`);
* `1` — unsatisfiable: `=====UNSATISFIABLE=====` on stdout (the
  FlatZinc convention);
* `2` — `unknown`: no verdict (budget exhausted or statically
  refused), reason on stderr; also usage/IO/parse errors;
* `3` — unsupported: model outside the searched fragment or
  configuration, reason on stderr.
-/

/-- Parse the `solve` argument list into a configuration plus the
    remaining source arguments; flags may appear before or after the
    file argument, and an unrecognized `--`-prefixed argument is
    refused. -/
private def parseSolveFlags (args : List String) :
    Except String (Option Solver.SolveConfig × List String) :=
  let rec go (cfg : Solver.SolveConfig) (certified : Bool) :
      List String → Except String (Option Solver.SolveConfig × List String)
    | [] => .ok (if certified then none else some cfg, [])
    | "--certified" :: rest => go cfg true rest
    | "--prop" :: rest => go { cfg with useProp := true } certified rest
    | "--mrv" :: rest => go { cfg with useMrv := true } certified rest
    | "--nogoods" :: rest => go { cfg with nogoods := true } certified rest
    | "--budget" :: n :: rest =>
        match n.toNat? with
        | some b => go { cfg with budget := some b } certified rest
        | none => .error s!"invalid budget '{n}' (expected a natural number)"
    | "--budget" :: _ => .error "option --budget requires a natural number argument"
    | arg :: rest =>
        if arg.startsWith "--" then
          .error s!"unknown option '{arg}'"
        else
          match go cfg certified rest with
          | .ok (cfg', srcArgs) => .ok (cfg', arg :: srcArgs)
          | .error e => .error e
  go ⟨false, false, none, false⟩ false args

/-- The `solve` subcommand: parse the model, run the composed front
    door, and report the verdict. `--certified` routes through the
    LCG fragment path whose SAT/UNSAT theorems are kernel-checked
    end to end (`Direct.solveCertified`). -/
private def runSolve (args : List String) : IO UInt32 := do
  match parseSolveFlags args with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok (none, srcArgs) =>
      -- the certified LCG path
      match ← parseModelSource srcArgs with
      | .error e =>
          IO.eprintln s!"leanfzn: {e}"
          return 2
      | .ok model =>
          if LeanFzn.Check.wellFormedFastB model then
            match LeanFzn.Solver.Direct.solveCertified model with
            | .sat store =>
                -- emit the satisfying assignment as a solution text
                let text := LeanFzn.Solver.Direct.emitCertifiedSolution model store
                IO.println text
                return 0
            | .unsat =>
                IO.println "=====UNSATISFIABLE====="
                return 1
            | .unknown reason =>
                IO.eprintln s!"leanfzn: {reason}"
                return 2
            | .unsupported reason =>
                IO.eprintln s!"leanfzn: {reason}"
                return 3
          else
            IO.eprintln "leanfzn: model is not well-formed"
            return 2
  | .ok (some cfg, srcArgs) =>
      match ← parseModelSource srcArgs with
      | .error e =>
          IO.eprintln s!"leanfzn: {e}"
          return 2
      | .ok model =>
          match Solver.solveModelWith cfg model with
          | .sat text =>
              IO.println text
              return 0
          | .unsat =>
              IO.println "=====UNSATISFIABLE====="
              return 1
          | .unknown reason =>
              IO.eprintln s!"leanfzn: {reason}"
              return 2
          | .unsupported reason =>
              IO.eprintln s!"leanfzn: {reason}"
              return 3

/-! ## The `enum` subcommand

Runs the all-solutions enumerator `Solver.enumModel`
(`solver/Enum.lean`): every reported text is checker-accepted
(`enumModel_sat_sound`) and every accepted assignment is represented
(`enumModel_complete`).  Output follows the FlatZinc convention: each
solution text (already ending in `----------`) on its own lines, then
a final `==========` line.  Exit codes: `0` = enumerated (an empty
enumeration prints the `==========` line only), `1` =
`=====UNSATISFIABLE=====` on stdout, `3` = unsupported (model outside
the searched fragment), reason on stderr; usage/IO/parse errors exit
2.
-/

/-- The `enum` subcommand: enumerate all solutions of the model. -/
private def runEnum (args : List String) : IO UInt32 := do
  match ← parseModelSource args with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok model =>
      match Solver.enumModel model with
      | .sat texts =>
          for text in texts do
            IO.println text
          IO.println "=========="
          return 0
      | .unsat =>
          IO.println "=====UNSATISFIABLE====="
          return 1
      | .unsupported reason =>
          IO.eprintln s!"leanfzn: {reason}"
          return 3

/-! ## The `optimize` subcommand

Runs the branch-and-bound optimizer `Solver.optimizeModelBb`
(`solver/Optimize.lean`): improving-bound rounds of the reference
search, every leaf checked by the verified checker
(`optimizeModelBb_sat_sound`), optimality certified by a later empty
round (`optimizeModelBb_optimal`).  Output: the optimal solution
text, the `==========` separator (FlatZinc convention), and the
objective value on stderr.  Exit codes: `0` = optimal, `1` =
`=====UNSATISFIABLE=====` on stdout, `3` = unsupported (satisfaction
model, objective outside the slot-level scope, or model outside the
searched fragment), reason on stderr; usage/IO/parse errors exit 2.
-/

/-- The `optimize` subcommand: find and print the optimal
    solution. -/
private def runOptimize (args : List String) : IO UInt32 := do
  match ← parseModelSource args with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok model =>
      match Solver.optimizeModelBb model with
      | .optimal text value =>
          IO.println text
          IO.println "=========="
          IO.eprintln s!"objective = {value}"
          return 0
      | .unsat =>
          IO.println "=====UNSATISFIABLE====="
          return 1
      | .unsupported reason =>
          IO.eprintln s!"leanfzn: {reason}"
          return 3

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", modelPath, solPath] =>
      runCheck modelPath solPath
  | "solve" :: rest =>
      runSolve rest
  | "enum" :: rest =>
      runEnum rest
  | "optimize" :: rest =>
      runOptimize rest
  | _ =>
      match ← readSource args with
      | .error e =>
          IO.eprintln s!"leanfzn: {e}"
          return 2
      | .ok src =>
          match Parser.parseModel src with
          | .ok model =>
              IO.println (repr model)
              return 0
          | .error e =>
              IO.eprintln s!"leanfzn: parse error: {e}"
              return 1
