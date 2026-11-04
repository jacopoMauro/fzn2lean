/-
Runtime tests for the N3b compact-domain operation-law layer.

Run with:
  lake env lean --run Tests/Engine/DomOpsTest.lean

The tests are differential checks against direct computation on the small
domains below.  They cover `mem_setLe`, `mem_setGe`, `mem_remove`,
`mem_fix`, `mem_applyLit`, and the `some true`/`some false` answers of
`evalLit` against the complete enumeration `DomC.toValueList`.  The
contractual statements are proved in `LeanFzn.Engine.DomOps`; this file is a
runtime regression net only.

The compile-time examples at the end keep `DomC.ofDom?_wf` instantiated at
the strengthened `DomC.WF` for the `.small`, `.holes` and `.general` entry
constructors used by the existing fixtures.
-/
import LeanFzn.Engine.DomOps

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"DomOpsTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-- Integer probes: a contiguous small range plus the values around a
64-bit word boundary. -/
def intProbes : List Int :=
  (List.range 24).map (fun i : Nat => (i : Int) - 3) ++ [60, 61, 62, 63, 64, 65, 66, 99]

/-- Probe values used for the membership differential. -/
def probeValues : List Value :=
  [.bool false, .bool true] ++ intProbes.map Value.int ++
    [.setOfInt (.enumeration [1]), .array []]

/-- Integer literals on slot 0, at every probe bound. -/
def intLiterals : List Literal :=
  (intProbes.map fun k => [posLe 0 k, negLe 0 k, posNe 0 k, negNe 0 k]).flatten

/-- Boolean literals on slot 0. -/
def boolLiterals : List Literal :=
  [posBool 0 false, posBool 0 true,
   (posBool 0 false).negate, (posBool 0 true).negate]

def literals : List Literal := intLiterals ++ boolLiterals

/-- Direct (Boolean) integer-view test for a probe value. -/
def holdsLe (v : Value) (k : Int) : Bool :=
  match v.intView with
  | some i => decide (i ≤ k)
  | none => false

def holdsGe (v : Value) (k : Int) : Bool :=
  match v.intView with
  | some i => decide (k ≤ i)
  | none => false

/-- Small well-formed domains: Booleans, bounds, bitsets across a word
boundary, and holes at the interior, the endpoints, and covering the whole
interval. -/
def domains : List (String × DomC) :=
  [ ("bool 000", .bool 0),
    ("bool 001", .bool 1),
    ("bool 010", .bool 2),
    ("bool 011", .bool 3),
    ("bounds 0..5", .bounds 0 5),
    ("bounds -3..2", .bounds (-3) 2),
    ("bounds singleton", .bounds 2 2),
    ("bounds empty", .bounds 5 4),
    ("bitset 0 [1011]", .bitset 0 #[0b1011]),
    ("bitset 63 high bit", .bitset 63 #[1]),
    ("bitset 60 word boundary", .bitset 60 #[0xFFFFFFFFFFFFFFFF, 0x3]),
    ("bitset empty", .bitset 0 #[]),
    ("holes interior", .boundsHoles 0 10 #[3, 7]),
    ("holes both endpoints", .boundsHoles 0 10 #[0, 10]),
    ("holes cover interval", .boundsHoles 0 1 #[0, 1]),
    ("holes none", .boundsHoles 3 7 #[]),
    ("holes empty interval", .boundsHoles 5 4 #[]) ]

/-- Differential checks for one domain. -/
def checkDomain (label : String) (d : DomC) : IO Unit := do
  -- Enumeration agrees with `mem` on every probe.
  for v in probeValues do
    check s!"{label}: toValueList/mem at {repr v}"
      (d.mem v == d.toValueList.contains v)
  -- Restriction membership laws.
  for k in intProbes do
    for v in probeValues do
      check s!"{label}: mem_setLe {k} at {repr v}"
        ((d.setLe k).mem v == (d.mem v && holdsLe v k))
      check s!"{label}: mem_setGe {k} at {repr v}"
        ((d.setGe k).mem v == (d.mem v && holdsGe v k))
  for w in probeValues do
    for v in probeValues do
      check s!"{label}: mem_remove {repr w} at {repr v}"
        ((d.remove w).mem v == (d.mem v && !(v == w)))
      check s!"{label}: mem_fix {repr w} at {repr v}"
        ((d.fix w).mem v == (d.mem v && (v == w)))
  -- Literal laws and evalLit against the complete enumeration.
  for l in literals do
    for v in probeValues do
      check s!"{label}: mem_applyLit {repr l} at {repr v}"
        ((d.applyLit l).mem v == (d.mem v && Literal.valueHolds l v))
    match d.evalLit l with
    | some true =>
        for v in d.toValueList do
          check s!"{label}: evalLit true {repr l} at {repr v}"
            (Literal.valueHolds l v == true)
        for v in probeValues do
          check s!"{label}: applyLit unchanged {repr l} at {repr v}"
            ((d.applyLit l).mem v == d.mem v)
    | some false =>
        for v in d.toValueList do
          check s!"{label}: evalLit false {repr l} at {repr v}"
            (Literal.valueHolds l v == false)
    | none => pure ()

/-- The malformed-holes regression: `isFixed` (size == 1) is true here even
though the only in-range value 0 is covered by the out-of-range hole 5, so
the old `evalLit` branch would wrongly return `some false`.  The new branch
must be `none`. -/
def checkMalformedHoles : IO Unit := do
  let d : DomC := .boundsHoles 0 1 #[5]
  check "malformed holes: isFixed is true" d.isFixed
  check "malformed holes: evalLit (posNe 0) is none"
    (d.evalLit (posNe 0 0)).isNone
  check "malformed holes: evalLit (negNe 0) is none"
    (d.evalLit (negNe 0 0)).isNone

def run : IO UInt32 := do
  for (label, d) in domains do
    checkDomain label d
  checkMalformedHoles
  IO.println "DomOpsTest: OK"
  return 0

end Tests.Engine

/-! ### Compile-time entry checks for the strengthened `WF` -/

open Tests.Engine in
/-- `ofDom?_wf` still has the strengthened `DomC.WF` as its conclusion. -/
example (d : Dom) (c : DomC) (h : DomC.ofDom? d = some c) : c.WF :=
  DomC.ofDom?_wf d c h

example : (DomC.ofDom? (⟨.small true 0 3⟩ : Dom)).isSome = true := rfl
example : (DomC.ofDom? (⟨.small false 0 5⟩ : Dom)).isSome = true := rfl
example : (DomC.ofDom? (⟨.holes 0 10 [3, 7]⟩ : Dom)).isSome = true := rfl
example : (DomC.ofDom? (⟨.general [.int 1, .int 3]⟩ : Dom)).isSome = true := by decide

open Tests.Engine in
def main : IO UInt32 := Tests.Engine.run
