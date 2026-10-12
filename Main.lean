/- Stable executable entrypoint; command behavior lives in the CLI component. -/
import LeanFzn.Cli.Main

def main (args : List String) : IO UInt32 := LeanFzn.Cli.main args
