/-
Runtime tests for the N9 certified Core search loop.

Run with:
  lake env lean --run Tests/Engine/SearchTest.lean

The checks are executable observations on small compiled problems; the
contractual guarantees are the theorems `coreSolve_sat`, `coreSolve_unsat`,
`search_sat`/`search_unsat`, and the `solveSearchConfigCore_*` seam
theorems.
-/
import LeanFzn.Legacy.Integration.CoreSolve

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

namespace Tests.Engine

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"SearchTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-- A compiled problem with the supplied domains and constraints. -/
def mkProblem (ds : List Dom) (dcs : List DomConstraint) :
    CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := dcs
    objective := ()
    source := default
    toStore := fun _ _ => none }

/-- One integer variable with values `0,1,2`, constrained to be at most 1. -/
def satProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b111⟩] [.leConstHi 0 1]

/-- An empty Boolean clause: no assignment can satisfy it, and its seed is
    the empty clause. -/
def rootUnsatProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b11⟩] [.boolClauseSlot [] []]

/-- Two ternary slots multiplied into a fixed 1: the minimum-value decision
    `x = 0` collides with the dedicated `int_times` propagator, so first-UIP
    analysis learns a nonempty unit clause and backjumps; `x = 1, y = 1`
    then satisfies the problem. -/
def conflictProblem : CompiledProblem DomConstraint :=
  mkProblem
    [⟨.small false 0 0b111⟩, ⟨.small false 0 0b111⟩, ⟨.small false 0 0b10⟩]
    [.timesSlot 0 1 2]

/-- The same SAT problem with a constraint whose second slot is out of range;
    `initState` must reject it before any propagation. -/
def malformedProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b11⟩] [.neSlot 0 5]

def config : SearchConfig := {}

def verdictName : CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

def sameResult : SearchResult → SearchResult → Bool
  | .sat a, .sat b => a == b
  | .unsat, .unsat => true
  | .unknown, .unknown => true
  | _, _ => false

/-- Check that a Core SAT answer is a member of the box and is accepted. -/
def checkSatAnswer (label : String) (p : CompiledProblem DomConstraint)
    (a : List Value) : IO Unit := do
  check s!"{label}: SAT assignment in allAssigns"
    ((allAssigns p.domains).contains a)
  check s!"{label}: SAT assignment accepted" (accepts p a)

/-- No enumerated box member is accepted. -/
def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

def run : IO UInt32 := do
  -- 1. SAT with one variable and a unary constraint.
  match coreSolveFull satProblem config coreFuel with
  | (.sat a, _) =>
      checkSatAnswer "sat" satProblem a
  | (r, _) => fail s!"sat: unexpected verdict {verdictName r}"

  -- 2. Root UNSAT through an empty seed clause.
  match coreSolveFull rootUnsatProblem config coreFuel with
  | (.unsat, _) =>
      check "unsat: no accepted enumerated assignment" (noAccepted rootUnsatProblem)
  | (r, _) => fail s!"unsat: unexpected verdict {verdictName r}"

  -- 3. A decision followed by a propagation conflict and first-UIP learning.
  match coreSolveFull conflictProblem config coreFuel with
  | (.sat a, st) =>
      checkSatAnswer "conflict" conflictProblem a
      check "conflict: stats.conflicts > 0" (st.conflicts > 0)
      check "conflict: stats.learned > 0" (st.learned > 0)
  | (r, st) =>
      fail s!"conflict: unexpected verdict {verdictName r} (conflicts={st.conflicts})"

  -- 4. Fuel exhaustion makes no claim.
  match coreSolveFull satProblem config 0 with
  | (.gaveUp, st) =>
      check "fuel: stats.gaveUp = 1" (st.gaveUp == 1)
  | (r, _) => fail s!"fuel: unexpected verdict {verdictName r}"

  -- 5. A malformed out-of-range constraint gives up without a claim.
  match coreSolveFull malformedProblem config coreFuel with
  | (.gaveUp, _) => pure ()
  | (r, _) => fail s!"malformed: unexpected verdict {verdictName r}"

  -- 6a. The seam agrees with Core when Core decides SAT.
  let satCore := coreSolve satProblem config coreFuel
  let satSeam := solveSearchConfigCore satProblem config
  check "seam: SAT verdict agrees with core"
    (match satCore, satSeam with
     | .sat a, .sat b => (allAssigns satProblem.domains).contains b &&
         accepts satProblem b && a == b
     | _, _ => false)
  -- 6b. The seam agrees with Core when Core decides UNSAT.
  check "seam: UNSAT verdict agrees with core"
    (match coreSolve rootUnsatProblem config coreFuel, solveSearchConfigCore rootUnsatProblem config with
     | .unsat, .unsat => true
     | _, _ => false)
  -- 6c. On a Core give-up the seam is exactly the kernel fallback.
  check "seam: gaveUp falls back to kernel"
    (match coreSolve malformedProblem config coreFuel with
     | .gaveUp =>
         sameResult (solveSearchConfigCore malformedProblem config)
           (solveSearchConfig malformedProblem config)
     | _ => false)

  IO.println "SearchTest: OK"
  return 0

end Tests.Engine

open Tests.Engine in
def main : IO UInt32 := Tests.Engine.run
