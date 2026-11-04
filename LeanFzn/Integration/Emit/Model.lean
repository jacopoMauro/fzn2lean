/-
Purpose: Render source-model stores independently of any solving backend.
Dependencies: Emit.Basic supplies FlatZinc scalar rendering and separators.
DAG: source store -> shared output -> public Core or explicit legacy driver.
-/
import LeanFzn.Integration.Emit.Basic

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics

/-- Emit a solution text for the certified path's satisfying store
    (the FlatZinc convention, ending with the `----------`
    separator). Every declared variable must read a value — the
    SAT theorem guarantees it; a `none` read is a loud failure. -/
def certifiedEntries (m : Model) (store : Store) : List String :=
  m.variables.filterMap fun d =>
    match store (VarDeclItem.name d) with
    | some v => some (emitDeclEntry d v)
    | none => panic!
      s!"internal error: certified store has no value for \
         '{(VarDeclItem.name d).name}'"

/-- One complete solution text (entries then the separator). An
    optimisation driver (O1) can concatenate several of these and append
    `optimumMarker`. -/
def emitCertifiedSolution (m : Model) (store : Store) : String :=
  let entries := certifiedEntries m store
  "\n".intercalate entries ++ (if entries.isEmpty then "" else "\n") ++ solutionSeparator


end LeanFzn.Integration
