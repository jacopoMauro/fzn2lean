/-
Runtime tests for the N3 compact domain store.

Run with:
  lake env lean --run Tests/Engine/DomTest.lean

The tests compare `DomC` operations against the compiled `Dom` denotation
(`Dom.enum`) on small `.small`, `.holes` and `.general` inputs.  They are
runtime checks only; the contractual statements are `DomC.mem_iff`,
`DomC.ofDom?_wf` and `fitsB_iff_mem_allAssigns` in `LeanFzn.Engine.Dom`.
-/
import LeanFzn.Engine.Dom

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"DomTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-- Probe values used to compare membership tests. -/
def probeValues : List Value :=
  [.bool false, .bool true,
   .int (-3), .int (-2), .int (-1), .int 0, .int 1, .int 2, .int 3,
   .int 4, .int 5, .int 6, .int 7, .int 8, .int 9, .int 10, .int 11,
   .int 12, .int 13, .int 14, .int 99, .int 100,
   .setOfInt (.enumeration [1]), .array []]

/-- Integer probes for the integer-view operations. -/
def intProbes : List Int :=
  [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 99, 100]

/-- Integer view of a compiled domain's enumeration. -/
def intViewValues (d : Dom) : List Int :=
  (Dom.enum d).filterMap Value.intView

def minInt? : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl min x)

def maxInt? : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl max x)

/-- Conversion cases whose `Dom.enum` is already canonical (no duplicates
    and no reordering), so `toValueList` must reproduce it exactly. -/
def canonicalCases : List (String × Dom) :=
  [ ("small true empty", ⟨.small true 0 0⟩),
    ("small true false", ⟨.small true 0 1⟩),
    ("small true true", ⟨.small true 0 2⟩),
    ("small true both", ⟨.small true 0 3⟩),
    ("small true high bits", ⟨.small true 0 0b1011⟩),
    ("small false", ⟨.small false 10 0b1011⟩),
    ("small false singleton", ⟨.small false (-5) 1⟩),
    ("small false bit63", ⟨.small false 0 (UInt64.ofNat (1 <<< 63))⟩),
    ("holes", ⟨.holes 0 10 [3, 7]⟩),
    ("holes singleton", ⟨.holes 5 5 []⟩),
    ("holes empty", ⟨.holes 5 4 []⟩),
    ("holes two values", ⟨.holes 0 3 [1, 2]⟩) ]

/-- General inputs exercise the entry fallback; their stored list may be
    order- and multiplicity-preserving, so only membership is compared
    against the original enumeration. -/
def generalCases : List (String × Dom) :=
  [ ("general ints unsorted", ⟨.general [.int 1, .int 3, .int 2]⟩),
    ("general ints duplicate", ⟨.general [.int 2, .int 2, .int 5]⟩),
    ("general ints sparse", ⟨.general [.int 1, .int 100]⟩),
    ("general bools", ⟨.general [.bool true, .bool false]⟩),
    ("general single int", ⟨.general [.int (-5)]⟩),
    ("general wide dense",
      ⟨.general ((List.range 5000).map fun i => .int (Int.ofNat i))⟩) ]

/-- Shapes that entry conversion is allowed to reject (`none` is a give-up). -/
def giveUpCases : List (String × Dom) :=
  [ ("general empty", ⟨.general []⟩),
    ("general mixed", ⟨.general [.int 1, .bool true]⟩),
    ("general set head", ⟨.general [.setOfInt (.enumeration [1])]⟩),
    ("general array head", ⟨.general [.array []]⟩),
    ("general wide sparse", ⟨.general [.int 0, .int 100000]⟩) ]

/-- Check conversion, membership, size and fixed-value consistency.  With
    `exactEnum = true`, the converted domain's enumeration must equal
    `Dom.enum d`; otherwise only membership is required. -/
def checkDom (label : String) (d : Dom) (exactEnum : Bool) : IO Unit := do
  match DomC.ofDom? d with
  | none => fail s!"{label}: ofDom? returned none"
  | some c =>
      for v in probeValues do
        check s!"{label}: mem {repr v}"
          (c.mem v == (Dom.enum d).contains v)
      for x in intProbes do
        check s!"{label}: memIntView {x}"
          (c.memIntView x ==
            (Dom.enum d).any fun v => v.intView == some x)
      check s!"{label}: lo?" (c.lo? == minInt? (intViewValues d))
      check s!"{label}: hi?" (c.hi? == maxInt? (intViewValues d))
      if exactEnum then
        check s!"{label}: toValueList" (c.toValueList == Dom.enum d)
      check s!"{label}: size" (c.size == c.toValueList.length)
      match c.toValueList with
      | [] =>
          check s!"{label}: fixedValue empty" c.fixedValue.isNone
      | [v] =>
          check s!"{label}: fixedValue singleton" (c.fixedValue == some v)
      | _ =>
          check s!"{label}: fixedValue non-singleton" c.fixedValue.isNone

/-- Check the restriction operations against their intended integer-view
    semantics on the denotation of `c`. -/
def checkOps (label : String) (c : DomC) : IO Unit := do
  for k in intProbes do
    let le := c.setLe k
    let ge := c.setGe k
    for x in intProbes do
      check s!"{label}: setLe {k} at {x}"
        (le.memIntView x == (c.memIntView x && decide (x ≤ k)))
      check s!"{label}: setGe {k} at {x}"
        (ge.memIntView x == (c.memIntView x && decide (k ≤ x)))
  for x in intProbes do
    let r := c.removeIntView x
    let f := c.fixIntView x
    for y in intProbes do
      check s!"{label}: removeIntView {x} at {y}"
        (r.memIntView y == (c.memIntView y && !(x == y)))
      check s!"{label}: fixIntView {x} at {y}"
        (f.memIntView y == (c.memIntView y && x == y))
  for v in probeValues do
    let r := c.remove v
    for w in probeValues do
      check s!"{label}: remove {repr v} at {repr w}"
        (r.mem w == (c.mem w && !(v == w)))

/-- A compiled problem carrying just the supplied domains. -/
def mkProblem (ds : List Dom) : CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := []
    objective := ()
    source := default
    toStore := fun _ _ => none }

/-- Reference fit computed from the compiled denotation. -/
def fitsExpected (ds : List Dom) (a : List Value) : Bool :=
  a.length == ds.length &&
    (List.range a.length).all fun i =>
      match a[i]? with
      | some v => (Dom.enum (ds.getD i Dom.empty)).contains v
      | none => true

def fitDomains : List Dom :=
  [⟨.small true 0 3⟩,
   ⟨.holes 0 10 [3, 7]⟩,
   ⟨.general [.int 1, .int 100]⟩]

def fitAssignments : List (List Value) :=
  [ [],
    [.bool false],
    [.bool false, .int 5],
    [.bool false, .int 5, .int 1],
    [.bool true, .int 5, .int 1],
    [.bool true, .int 3, .int 1],
    [.bool false, .int 11, .int 1],
    [.bool true, .int 5, .int 2],
    [.bool true, .int 5, .int 100],
    [.bool false, .int 5, .int 1, .bool true],
    [.int 0, .int 5, .int 1] ]

def emptyFitDomains : List Dom :=
  [⟨.holes 5 4 []⟩, ⟨.small true 0 1⟩]

def emptyFitAssignments : List (List Value) :=
  [ [], [.int 5], [.int 5, .bool false], [.int 6, .bool true] ]

/-- Compare `fitsB` with the reference and with `allAssigns` membership. -/
def checkFits (label : String) (ds : List Dom)
    (assignments : List (List Value)) : IO Unit := do
  let p := mkProblem ds
  for a in assignments do
    let got := fitsB (domProblem p) a
    check s!"{label}: fitsB {repr a}" (got == fitsExpected ds a)
    check s!"{label}: fitsB/allAssigns {repr a}"
      (got == (allAssigns p.domains).contains a)

def run : IO UInt32 := do
  for (label, d) in canonicalCases do
    checkDom label d true
    match DomC.ofDom? d with
    | some c => checkOps label c
    | none => fail s!"{label}: ofDom? returned none in checkOps"
  for (label, d) in generalCases do
    checkDom label d false
    match DomC.ofDom? d with
    | some c => checkOps label c
    | none => fail s!"{label}: ofDom? returned none in checkOps"
  for (label, d) in giveUpCases do
    check s!"{label}: expected none" (DomC.ofDom? d).isNone
  checkFits "fit" fitDomains fitAssignments
  checkFits "empty-fit" emptyFitDomains emptyFitAssignments
  IO.println "DomTest: OK"
  return 0

end Tests.Engine

open Tests.Engine in
def main : IO UInt32 := Tests.Engine.run
