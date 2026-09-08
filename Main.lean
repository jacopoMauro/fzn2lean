import LeanFzn

open LeanFzn

private def readSource (args : List String) : IO (Except String String) := do
  match args with
  | [] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | ["-"] =>
      return .ok (← (← IO.getStdin).readToEnd)
  | [path] =>
      try
        return .ok (← IO.FS.readFile path)
      catch e =>
        return .error s!"cannot read '{path}': {e}"
  | _ =>
      return .error "usage: leanfzn [FILE|-]"

def main (args : List String) : IO UInt32 := do
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
