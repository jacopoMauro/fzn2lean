/-
Purpose: Public parser/checker CLI and Core-only solver command.
Dependencies: Parser, runtime Checker, common flags and Integration.Public.Driver.
DAG: shared language tools + Core public API -> Cli.Main -> leanfzn.
The list-based solver is isolated under Legacy and is never dispatched here.
-/

import LeanFzn.Parser.Parser
import LeanFzn.Checker.Runtime.Check
import LeanFzn.Integration.Config.Parse
import LeanFzn.Integration.Public.Driver

namespace LeanFzn.Cli
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration
open LeanFzn.Integration.Report


open LeanFzn

/-- The one-line usage summary, printed on argument-level errors. -/
private def usageString : String :=
  "usage: leanfzn [FILE|-] | leanfzn check MODEL.fzn SOLUTION.txt | \
  leanfzn solve [OPTIONS] FILE|-"

private def readFileArg (path : String) : IO (Except String String) := do
  try
    return .ok (← IO.FS.readFile path)
  catch e =>
    return .error s!"cannot read '{path}': {e}"

/-- Argument-level source failure, split into the protocol's early error
    classes: a usage error, a file read failure, or a model parse failure. -/
private inductive SourceError where
  | usage (message : String)
  | fileIO (message : String)
  | modelParse (message : String)

private def SourceError.message : SourceError → String
  | .usage m | .fileIO m | .modelParse m => m

private def SourceError.kind : SourceError → ErrorKind
  | .usage _ => .usage
  | .fileIO _ => .fileIO
  | .modelParse _ => .modelParse

private def readSource (args : List String) : IO (Except SourceError String) := do
  match args with
  | [] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | ["-"] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | [path] =>
      match ← readFileArg path with
      | .ok src => return .ok src
      | .error e => return .error (.fileIO e)
  | _ =>
      return .error (.usage usageString)

/-- Read the model source (a file, `-`, or stdin) and parse it; the carried
    error keeps its usage/file/parse class and message for the CLI. -/
private def parseModelSource (args : List String) : IO (Except SourceError Model) := do
  match ← readSource args with
  | .error e => return .error e
  | .ok src =>
      match Parser.parseModel src with
      | .error e => return .error (.modelParse s!"parse error: {e}")
      | .ok model => return .ok model

/-- Select the report mode and remove its flags from the solver arguments.
    Exactly `--report=text` and `--report=jsonl-v1` are accepted, and the last
    accepted value wins.  A bare or unknown value is a usage error and never
    selects the JSONL protocol. -/
def parseReportMode (args : List String) : Except String (ReportMode × List String) :=
  let rec go (xs : List String) (mode : ReportMode) (kept : List String) :
      Except String (ReportMode × List String) :=
    match xs with
    | [] => .ok (mode, kept.reverse)
    | arg :: rest =>
        match arg with
        | "--report=text" => go rest .text kept
        | "--report=jsonl-v1" => go rest .jsonlV1 kept
        | "--report" =>
            .error "option '--report' requires a value: --report=text or --report=jsonl-v1"
        | _ =>
            if arg.startsWith "--report=" then
              .error s!"invalid value '{(arg.drop "--report=".length).toString}' for --report: expected text or jsonl-v1"
            else go rest mode (arg :: kept)
  go args .text []

/-! ## The `check` subcommand

The CLI front door runs `LeanFzn.Checker.checkModelSolutionFast`, which
returns exactly the outcome of `LeanFzn.Checker.checkModelSolution`
(`checkModelSolutionFast_eq`), the verified wrapper that establishes
both preconditions of
`checkSolutionFull_correct` itself: static well-formedness (through the
fast twin `wellFormedFastB`, proved equivalent to `WellFormed` by
`wellFormedFastB_iff`) and predicate checkability (through
`firstUnsupported`).  Each failure mode gets its own diagnostic and
exit code:

The input may contain several solutions, each terminated by a
`----------` line (`LeanFzn.Checker.splitSolutions`); every solution is checked
and the first one that is not accepted determines the exit code.

* `0` — solution (every solution) accepted;
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
        let sols := LeanFzn.Checker.splitSolutions sol
        if sols.isEmpty then
          IO.eprintln "leanfzn: malformed solution: no solution in the input"
          return 4
        -- check every solution; report the first that is not accepted
        let n := sols.length
        let label (i : Nat) : String := if n == 1 then "" else s!"solution {i + 1} of {n}: "
        for (s, i) in sols.zipIdx do
          match LeanFzn.Checker.checkModelSolutionFast model s with
          | .accepted => pure ()
          | .unsatisfied =>
              IO.println s!"{label i}solution rejected: unsatisfied condition"
              return 1
          | .malformedModel reason =>
              IO.eprintln s!"leanfzn: {reason}"
              return 2
          | .unsupportedPredicate name =>
              IO.eprintln
                s!"leanfzn: unsupported predicate: {name} (no verified interpretation)"
              return 3
          | .malformedSolution reason =>
              IO.eprintln s!"leanfzn: {label i}malformed solution: {reason}"
              return 4
        IO.println (if n == 1 then "solution accepted" else s!"all {n} solutions accepted")
        return 0

/-! ## The Core-only `solve` command

Satisfaction, linear optimization and seeded optimization use only the array
engine. A Core give-up is explicit unknown/incomplete (exit 4), retaining
already streamed incumbents. Completion markers require certified completion.
Kernel-only options and `--engine=kernel` are usage errors; no option silently
selects another engine. The preserved old API lives in LeanFzn/Legacy.
-/

private def runSolveWithSink (sink : ReportSink) (args : List String) : IO UInt32 := do
  -- Dev diagnostic only (PLAN E1): consumed before the option parser so it
  -- never becomes part of the certified `SearchConfig`.
  let phaseStats := args.elem "--phase-stats"
  let args := args.filter (· != "--phase-stats")
  if phaseStats && sink.mode == .jsonlV1 then
    let message :=
      "--phase-stats is a development diagnostic and cannot be combined with --report=jsonl-v1"
    IO.eprintln s!"leanfzn: {message}"
    return (← sink.finishError .usage message)
  match LeanFzn.Core.parseSolveFlags args with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return (← sink.finishError .usage e)
  | .ok (o, srcArgs) =>
      let ps? ← if phaseStats then some <$> LeanFzn.Core.PhaseCtx.new else pure none
      let parseStart := match ps? with
        | some ps => ps.startMs
        | none => 0
      match ← parseModelSource srcArgs with
      | .error e =>
          IO.eprintln s!"leanfzn: {e.message}"
          return (← sink.finishError e.kind e.message)
      | .ok model =>
          let rc ← match ps? with
            | some ps =>
                ps.report "parse" parseStart
                LeanFzn.Core.runModelPhasedWithSink sink ps o model
            | none => LeanFzn.Core.runModelWithSink sink o model
          if o.threads > 1 then
            -- The portfolio's other workers may still be inside a long pure
            -- search round; exit directly so a completed proof is reported at
            -- its own wall time instead of after task-manager finalization.
            (← IO.getStdout).flush
            (← IO.getStderr).flush
            IO.Process.exit (UInt8.ofNat rc.toNat)
          return rc

private def runSolve (args : List String) : IO UInt32 := do
  match parseReportMode args with
  | .error e =>
      -- The protocol is not selected: a plain text usage error, no handshake.
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok (mode, args) =>
      let sink ← ReportSink.new mode
      -- In JSONL mode the handshake is the first stdout line, even when a
      -- later argument, source read or model parse fails.
      sink.start
      runSolveWithSink sink args

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", modelPath, solPath] =>
      runCheck modelPath solPath
  | "solve" :: rest =>
      runSolve rest
  | _ =>
      match ← readSource args with
      | .error e =>
          IO.eprintln s!"leanfzn: {e.message}"
          return 2
      | .ok src =>
          match Parser.parseModel src with
          | .ok model =>
              IO.println (repr model)
              return 0
          | .error e =>
              IO.eprintln s!"leanfzn: parse error: {e}"
              return 1

end LeanFzn.Cli
