import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Objective
import LeanFzn.Parser.Parser
import LeanFzn.Compiler.Domain
open LeanFzn.Compiler.Domains
open LeanFzn LeanFzn.Compiler

/-!
# Challenge scan

`challenge_scan [--full|--opt] FILE...` parses each FlatZinc file and runs the
compiler front door, printing one `STATUS<TAB>path<TAB>detail` line per
file (`OK`, `REJECT`, `PARSEERR`).  Used to measure which benchmark
files the certified fragment accepts (PLAN.md task X1).  Also prints
the constraint name of every constraint, as `CNAME<TAB>name`, once per
file and name, for frequency tables.
-/

def scanOne (full opt : Bool) (path : String) : IO Unit := do
  let src ← IO.FS.readFile path
  match Parser.parseModel src with
  | .error e => IO.println s!"PARSEERR\t{path}\t{e.take 80}"
  | .ok m =>
    let names := (m.constraints.map (fun c => c.name.name)).eraseDups
    for n in names do IO.println s!"CNAME\t{n}"
    let r : Except String Unit :=
      if opt then (compileModelOpt m).map (fun _ => ())
      else if full then (compileModelFull m).map (fun _ => ())
      else (compileModel m).map (fun _ => ())
    match r with
    | .ok _ => IO.println s!"OK\t{path}\t"
    | .error e =>
      IO.println s!"REJECT\t{path}\t{e}"
      -- diagnostics: force `satisfy` and probe each constraint name alone
      if full then
        let ms := { m with solve := .satisfy [] }
        match compileModelFull ms with
        | .ok _ => IO.println s!"DIAG\t{path}\tcompiles-as-satisfy"
        | .error e2 => IO.println s!"DIAG\t{path}\t{e2}"
        if arraysOkB ms then
          let n := normalizeFull ms
          match slotsChecked n with
          | .error e4 => IO.println s!"SLOTERR\t{path}\t{e4}"
          | .ok slots =>
            let aux := modelAuxSlots n
            let nm := (slots ++ aux).map Prod.fst
            let mut errs : List (String × String) := []
            for c in modelExpand n do
              match compileConstraint (parEnv n) nm c with
              | .ok _ => pure ()
              | .error e5 =>
                  let k := (c.name.name, e5)
                  if !(errs.contains k) then errs := errs ++ [k]
            for (cn, e5) in errs do IO.println s!"PROBE\t{cn}\t{e5}"

def main (args : List String) : IO UInt32 := do
  let (full, opt, files) := match args with
    | "--opt" :: rest => (true, true, rest)
    | "--full" :: rest => (true, false, rest)
    | _ => (false, false, args)
  for f in files do scanOne full opt f
  return 0
