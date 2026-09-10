import LeanFzn

open LeanFzn

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
      return .error "usage: leanfzn [FILE|-] | leanfzn check MODEL.fzn SOLUTION.txt"

/-- The `check` subcommand: parse the model, run the full solution
    checker, and report the verdict.  Exit codes: 0 = accepted,
    1 = rejected, 2 = usage/IO/parse error. -/
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
          if Globals.checkSolutionFull model sol then
            IO.println "solution accepted"
            return 0
          else
            IO.println "solution rejected"
            return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", modelPath, solPath] =>
      runCheck modelPath solPath
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
