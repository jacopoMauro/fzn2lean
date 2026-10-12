/-
File: LeanFzn/Cli/Main.lean

Purpose:
  CLI entry point (`leanfzn`) exposing the verified front door
  (`check`) and the certified LCG LeanFzn.Solver (`solve`).

Dependencies:
  LeanFzn (FznCheck.checkModelSolution, wellFormedFastB),
  LeanFzn.Integration.CertifiedSolve (solveCertified, emitCertifiedSolution).

Why:
  The executable's two faces are model/solution validation for
  `check`, and the certified sat/unsat verdicts of `solve` (source
  level SAT/UNSAT theorems: `solveCertified_sat_correct` /
  `solveCertified_unsat_correct`), with emitted solution text.

DAG:
  LeanFzn + LeanFzn/Compiler/Cli -> Main -> leanfzn executable
-/

import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Integration.CertifiedSolve

namespace LeanFzn.Cli
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn

/-- The one-line usage summary, printed on argument-level errors. -/
private def usageString : String :=
  "usage: leanfzn [FILE|-] | leanfzn check MODEL.fzn SOLUTION.txt | \
  leanfzn solve [--certified] FILE|-"

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

/-! ## The `solve` subcommand

Runs `LeanFzn.Integration.solveCertified`: compile the finite int/bool fragment and
propagate and learn clauses before splitting its explicit pending frontier.
Both SAT and parameter-honest
UNSAT have kernel-checked source-level proofs. The traversal is FUEL-FREE:
termination is kernel-checked by the frontier-cost measure, so an accepted
finite model always receives a verdict — there is no search budget and
no fuel-exhaustion `unknown` outcome.

`--certified` is a temporary accepted alias (the command is
certified with or without it); it exists to keep old invocations
working and will be removed in a later release.  No other LeanFzn.Solver
flags are accepted.

A `sat` text is printed exactly as the verified emitter produced it
(it ends with the `----------` separator, the FlatZinc convention).
Exit codes:

* `0` — a solution was found (SAT soundness:
  `solveCertified_sat_correct`, multi-value domains included);
* `1` — unsatisfiable: `=====UNSATISFIABLE=====` on stdout (the
  FlatZinc convention; multi-value domains included);
* `2` — not well-formed: no verdict (a statically malformed
  model), reason on stderr; also usage/IO/parse errors;
* `3` — unsupported: model outside the certified gate (empty or
  non-int/bool-viewed domains, or compilation failure), reason on
  stderr.
-/

/-- Parse the `solve` argument list: the optional `--certified` alias
    plus the source argument (file, `-`, or stdin via absence). -/
private def parseSolveFlags (args : List String) :
    Except String (List String) :=
  let rec go : List String → Except String (List String)
    | [] => .ok []
    | "--certified" :: rest => go rest
    | arg :: rest =>
        if arg.startsWith "--" then
          .error s!"unknown option '{arg}'"
        else
          match go rest with
          | .ok srcArgs => .ok (arg :: srcArgs)
          | .error e => .error e
  go args

/-- The `solve` subcommand: parse the model, run the certified front
    door, and report the verdict. -/
private def runSolve (args : List String) : IO UInt32 := do
  match parseSolveFlags args with
  | .error e =>
      IO.eprintln s!"leanfzn: {e}"
      return 2
  | .ok srcArgs =>
      match ← parseModelSource srcArgs with
      | .error e =>
          IO.eprintln s!"leanfzn: {e}"
          return 2
      | .ok model =>
          if LeanFzn.Checker.wellFormedFastB model then
            match LeanFzn.Integration.solveCertified model with
            | .sat store =>
                -- emit the satisfying assignment as a solution text
                let text := LeanFzn.Integration.emitCertifiedSolution model store
                IO.println text
                return 0
            | .unsat =>
                IO.println "=====UNSATISFIABLE====="
                return 1
            | .unknown reason =>
                -- FUEL-FREE: unreachable on the active path (the
                -- traversal terminates by the kernel-checked
                -- measure); retained only for the result type.
                IO.eprintln s!"leanfzn: internal: {reason}"
                return 2
            | .unsupported reason =>
                IO.eprintln s!"leanfzn: {reason}"
                return 3
          else
            IO.eprintln "leanfzn: model is not well-formed"
            return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", modelPath, solPath] =>
      runCheck modelPath solPath
  | "solve" :: rest =>
      runSolve rest
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

end LeanFzn.Cli
