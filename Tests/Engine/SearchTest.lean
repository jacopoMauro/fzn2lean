/-
Runtime tests for the N9 certified Core search loop.

Run with:
  lake env lean --run Tests/Engine/SearchTest.lean

The checks are executable observations on small compiled problems; the
contractual guarantees are the theorems `coreSolve_sat`, `coreSolve_unsat`,
`search_sat`/`search_unsat`. Public adapter behavior is checked separately in
`Tests/Integration/Public/Runtime.lean`.
-/
import LeanFzn.Engine.Search

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
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray
    toStore := fun _ _ => none }

/-- One integer variable with values `0,1,2`, constrained to be at most 1. -/
def satProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b111⟩] [.leConstHi 0 1]

/-- An empty Boolean clause: no assignment can satisfy it, and its seed is
    the empty clause. -/
def rootUnsatProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small false 0 0b11⟩] [.boolClauseSlot [] []]

/-- A nonempty Boolean clause: the dedicated clause propagator must turn the
    first decision into a unit propagation.  With the seed-clause-only route
    this problem instead reaches a rejected leaf and gives up. -/
def boolClauseProblem : CompiledProblem DomConstraint :=
  mkProblem [⟨.small true 0 0b11⟩, ⟨.small true 0 0b11⟩]
    [.boolClauseSlot [0, 1] []]

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

/-- Check that a Core SAT answer is a member of the box and is accepted. -/
def checkSatAnswer (label : String) (p : CompiledProblem DomConstraint)
    (a : List Value) : IO Unit := do
  check s!"{label}: SAT assignment in allAssigns"
    ((allAssigns p.domains).contains a)
  check s!"{label}: SAT assignment accepted" (accepts p a)

/-- No enumerated box member is accepted. -/
def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

/-- Split decisions are active only under `--val=split`. -/
def splitConfig : SearchConfig := { val := .split }

/-- Follow the split branch that contains `target` until the domain is fixed.
    Returns the number of split decisions and the final domain.  A `none`
    means the policy made no progress or lost the target within the fuel. -/
def followSplit (d : DomC) (target : Int) : Nat → Option (Nat × DomC)
  | 0 => none
  | fuel + 1 =>
      if d.size == 1 then some (0, d)
      else
        match selectValue 0 d splitConfig .none none with
        | none => none
        | some l =>
            let l := if Literal.valueHolds l (.int target) then l else l.negate
            let d' := d.applyLit l
            if d'.mem (.int target) then
              match followSplit d' target fuel with
              | some (k, df) => some (k + 1, df)
              | none => none
            else none

/-- A wide interval with a sparse hole and a negative lower bound: every
    step keeps the target, strictly shrinks the domain, and reaches it in
    logarithmic depth. -/
def checkSplitDepth (label : String) (src : Dom) (target : Int)
    (maxSteps : Nat) : IO Unit := do
  match DomC.ofDom? src with
  | none => fail s!"{label}: conversion rejected"
  | some d =>
      check s!"{label}: target is a member"
        (d.mem (.int target) == true)
      match followSplit d target 32 with
      | none => fail s!"{label}: split search did not reach the target"
      | some (steps, df) =>
          check s!"{label}: logarithmic depth ({steps} ≤ {maxSteps})"
            (steps ≤ maxSteps)
          check s!"{label}: fixed at target" (df.fixedValue == some (.int target))

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

  -- 2b. A nonempty Boolean clause propagates through its dedicated prop.
  match coreSolveFull boolClauseProblem config coreFuel with
  | (.sat a, st) =>
      checkSatAnswer "bool clause" boolClauseProblem a
      check "bool clause: at least one propagation" (st.propagations > 0)
  | (r, st) =>
      fail s!"bool clause: unexpected verdict {verdictName r} (propagations={st.propagations})"

  -- 3. A decision followed by a propagation conflict and first-UIP learning.
  match coreSolveFull conflictProblem config coreFuel with
  | (.sat a, st) =>
      checkSatAnswer "conflict" conflictProblem a
      check "conflict: stats.conflicts > 0" (st.conflicts > 0)
      check "conflict: stats.learned > 0" (st.learned > 0)
      check "conflict: stats.maxLevel ≥ 1" (1 ≤ st.maxLevel)
  | (r, st) =>
      fail s!"conflict: unexpected verdict {verdictName r} (conflicts={st.conflicts})"

  -- 4. Fuel exhaustion makes no claim.
  match coreSolveFull satProblem config 0 with
  | (.gaveUp, st) =>
      check "fuel: stats.gaveUp = 1" (st.gaveUp == 1)
  | (r, _) => fail s!"fuel: unexpected verdict {verdictName r}"

  -- 4b. The conflict budget stops the loop with the counter exactly at the
  -- budget and a diagnostic cause; the verdict is a give-up, not a claim.
  match coreSolveFull conflictProblem { config with conflictLimit := some 1 } coreFuel with
  | (.gaveUp, st) =>
      check "conflict limit: stats.gaveUp = 1" (st.gaveUp == 1)
      check "conflict limit: one conflict" (st.conflicts == 1)
      check "conflict limit: cause" (st.gaveUpCause == "conflict limit reached")
  | (r, st) =>
      fail s!"conflict limit: unexpected verdict {verdictName r} (conflicts={st.conflicts})"

  -- 4c. A zero budget gives up before any drain and claims nothing.
  match coreSolveFull satProblem { config with conflictLimit := some 0 } coreFuel with
  | (.gaveUp, st) =>
      check "conflict limit zero: no conflicts" (st.conflicts == 0)
      check "conflict limit zero: cause" (st.gaveUpCause == "conflict limit reached")
  | (r, _) => fail s!"conflict limit zero: unexpected verdict {verdictName r}"

  -- 5. A malformed out-of-range constraint gives up without a claim.
  match coreSolveFull malformedProblem config coreFuel with
  | (.gaveUp, _) => pure ()
  | (r, _) => fail s!"malformed: unexpected verdict {verdictName r}"

  -- 6. Interval splitting: 1024 values are located in ten decisions, and
    -- holes, negative bounds and adjacent endpoints are handled.  These
    -- checks exercise the policy and both `applyLit` branches; the
    -- contractual coverage/reduction statements are `split_mem_cover`,
    -- `split_left_reduces` and `split_right_reduces`.
  checkSplitDepth "split wide" ⟨.holes 0 1023 []⟩ 1023 11
  checkSplitDepth "split wide low" ⟨.holes 0 1023 []⟩ 0 11
  checkSplitDepth "split hole" ⟨.holes 0 1023 [500]⟩ 501 11
  checkSplitDepth "split negative" ⟨.holes (-1024) 1023 []⟩ 700 12
  checkSplitDepth "split adjacent low" ⟨.holes 4 5 []⟩ 4 1
  checkSplitDepth "split adjacent high" ⟨.holes 4 5 []⟩ 5 1
  checkSplitDepth "split singleton" ⟨.holes 7 7 []⟩ 7 0
  checkSplitDepth "split sparse wide" ⟨.general [.int 0, .int 1000000]⟩ 1000000 1
  checkSplitDepth "split sparse wide low" ⟨.general [.int 0, .int 1000000]⟩ 0 1
  checkSplitDepth "split sparse negative"
    ⟨.general [.int (-1000000000), .int 0, .int 1000000000]⟩ (-1000000000) 2

  -- 7. Bound decisions still learn and backjump on a propagating conflict.
  match coreSolveFull conflictProblem splitConfig coreFuel with
  | (.sat a, st) =>
      checkSatAnswer "split conflict" conflictProblem a
      check "split conflict: stats.conflicts > 0" (st.conflicts > 0)
      check "split conflict: stats.learned > 0" (st.learned > 0)
  | (r, st) =>
      fail s!"split conflict: unexpected verdict {verdictName r} (conflicts={st.conflicts})"

  IO.println "SearchTest: OK"
  return 0

end Tests.Engine

open Tests.Engine in
def main : IO UInt32 := Tests.Engine.run
