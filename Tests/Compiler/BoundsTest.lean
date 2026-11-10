/-
Purpose: Regression tests for the U1 verified bound derivation (PLAN.md
task U1): unbounded `var int` declarations are narrowed only by CHECKED
certificates, and a variable with no derivation stays unsupported.

Dependencies: Compiler.Bounds/Normalize, parser, checker, emitter and
Core enumeration; no Legacy imports.
DAG: certified compiler -> this regression executable.

The positive cases cover the case-split rule (including the degenerate
forced-branch shape), the linear rule with unit, positive and negative
coefficients (the latter exercise floor/ceiling division), a row whose
only term is the variable, and multi-pass fixpoint derivation.  Every
accepted assignment is emitted and checked against the ORIGINAL source
model by the independent checker.

The planted near-misses must stay unsupported: a case split with one
side missing, a one-directional implication (two `c \/ r` clauses), a
non-reified equality, a bare `var int`, a partially derived model, a
one-sided inequality, a zero coefficient, and a variable occurring twice
in one row.

The final group bypasses the untrusted recognizer: it takes a genuine
certificate and plants an unsound mutation (narrowed lower bound,
narrowed upper bound, wrong coefficient).  `checkCerts` must reject each
mutation, so a recognizer bug alone can never introduce an incorrect
bound.
-/
import LeanFzn.Compiler.Normalize
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
import LeanFzn.Solver.Core
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

namespace Tests.Compiler.BoundsTest

private def parseOrPanic (src : String) : Model :=
  match Parser.parseModel src with
  | .ok m => m
  | .error e => panic! s!"unexpected parse error: {e}"

structure St where
  passed : Nat
  failed : Nat

def St.check (st : St) (name : String) (ok : Bool) : IO St := do
  if ok then
    IO.println s!"ok {name}"
    pure { st with passed := st.passed + 1 }
  else
    IO.eprintln s!"FAIL {name}"
    pure { st with failed := st.failed + 1 }

/-- The accepted assignment set of the compiled source model, projected
    to the integer components (the Boolean components are dropped).
    `none` means the model did not compile or an accepted assignment
    had an unexpected value kind. -/
def acceptedInts (m : Model) : Option (List (List Int)) :=
  match compileModelFull m with
  | .error _ => none
  | .ok p =>
      let as := (allAssigns p.domains).filter (accepts p)
      as.mapM fun a =>
        a.filterMap fun v =>
          match v with
          | .int i => some i
          | _ => none

/-- Multiset equality on integer tuples, independent of order. -/
def sameIntTuples (a b : List (List Int)) : Bool :=
  a.length == b.length && a.all (fun t => a.count t == b.count t)

def compiles (m : Model) : Bool :=
  match compileModelFull m with
  | .ok _ => true
  | .error _ => false

def unsupported (m : Model) : Bool :=
  match compileModelFull m with
  | .error _ => true
  | .ok _ => false

/-- Core's verdict on the compiled source model. -/
def verdict (m : Model) : String :=
  match compileModelFull m with
  | .error e => "error: " ++ e
  | .ok p =>
      match LeanFzn.Engine.coreSolve p { var := .act, val := .min }
          LeanFzn.Engine.coreFuel with
      | .sat _ => "sat"
      | .unsat => "unsat"
      | .gaveUp => "gaveup"

/-- Emit every accepted assignment and check it against the original
    source model with the verified front-door checker. -/
def witnessesAccepted (m : Model) : IO Bool := do
  match compileModelFull m with
  | .error _ => pure false
  | .ok p =>
      let as := (allAssigns p.domains).filter (accepts p)
      let mut ok := true
      for a in as do
        let sol := emitCertifiedSolution m (p.toStore a)
        if !(LeanFzn.Checker.checkModelSolutionFast m sol == .accepted) then
          ok := false
      pure ok

/-! ## Positive models -/

def positiveTest (st : St) (label src : String)
    (expected : List (List Int)) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"{label}: compiles" (compiles m)
  st ← st.check s!"{label}: accepted integer tuples"
    (match acceptedInts m with
     | some ts => sameIntTuples ts expected
     | none => false)
  st ← st.check s!"{label}: Core is SAT" (verdict m == "sat")
  st ← st.check s!"{label}: witnesses check" (← witnessesAccepted m)
  pure st

/-- A positive model with a companion that removes every solution: the
    tightened interval must not hide the companion, and Core must prove
    UNSAT rather than silently drop it. -/
def unsatTest (st : St) (label src : String) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"{label}: no accepted assignment"
    (match acceptedInts m with
     | some ts => ts.isEmpty
     | none => false)
  st ← st.check s!"{label}: Core is UNSAT" (verdict m == "unsat")
  pure st

/-- A planted near-miss: the recognizer must derive nothing and the
    compiler must return the honest unsupported error, with no invented
    bound. -/
def unsupportedTest (st : St) (label src : String) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"{label}: bounds derive nothing"
    (match boundsModel (normalizeFull m) with
     | none => true
     | some _ => false)
  st ← st.check s!"{label}: compiler rejects" (unsupported m)
  st ← st.check s!"{label}: error is the unbounded-bound error"
    (match compileModelFull m with
     | .error e => e == "unbounded integer variable without certified bounds"
     | .ok _ => false)
  pure st

/-! ## Source models -/

/-- Case split: `c -> r1`, `c \/ r2`, `r1 <-> x = 0`, `r2 <-> x = 10`
    force `x` into the hull `[0, 10]`. -/
def splitWith (extra : String) : String :=
  "var bool: c;\nvar bool: r1;\nvar bool: r2;\nvar int: x;\n" ++
  "constraint int_eq_reif(x, 0, r1);\n" ++
  "constraint int_eq_reif(x, 10, r2);\n" ++
  "constraint bool_clause([r1], [c]);\n" ++
  "constraint bool_clause([c, r2], []);\n" ++
  extra ++ "solve satisfy;\n"

def splitSrc : String := splitWith ""

/-- One side of the split is missing: `x` is not bounded. -/
def splitMissingSrc : String :=
  "var bool: c;\nvar bool: r1;\nvar bool: r2;\nvar int: x;\n" ++
  "constraint int_eq_reif(x, 0, r1);\n" ++
  "constraint int_eq_reif(x, 10, r2);\n" ++
  "constraint bool_clause([r1], [c]);\n" ++
  "solve satisfy;\n"

/-- One-directional implications: both clauses have the shape
    `c \/ r`, so neither branch forces a reified result. -/
def oneDirectionalSrc : String :=
  "var bool: c;\nvar bool: r1;\nvar bool: r2;\nvar int: x;\n" ++
  "constraint int_eq_reif(x, 0, r1);\n" ++
  "constraint int_eq_reif(x, 10, r2);\n" ++
  "constraint bool_clause([c, r1], []);\n" ++
  "constraint bool_clause([c, r2], []);\n" ++
  "solve satisfy;\n"

/-- Non-reified equalities do not derive a bound. -/
def nonReifSrc : String :=
  "var int: x;\nconstraint int_eq(x, 0);\nconstraint int_eq(x, 10);\n" ++
  "solve satisfy;\n"

/-- A bare unbounded variable. -/
def bareSrc : String := "var int: x;\nsolve satisfy;\n"

/-- Only one of two unbounded variables is derivable: the whole model
    stays unsupported (no partial tightening). -/
def partialSrc : String :=
  "var bool: c;\nvar bool: r1;\nvar bool: r2;\nvar int: x;\nvar int: y;\n" ++
  "constraint int_eq_reif(x, 0, r1);\n" ++
  "constraint int_eq_reif(x, 10, r2);\n" ++
  "constraint bool_clause([r1], [c]);\n" ++
  "constraint bool_clause([c, r2], []);\n" ++
  "solve satisfy;\n"

/-- A one-sided inequality gives no lower bound. -/
def oneSidedSrc : String :=
  "var int: x;\nconstraint int_le(x, 5);\nsolve satisfy;\n"

/-- A zero coefficient cannot bound the variable. -/
def linearZeroSrc : String :=
  "var 0..5: y;\nvar int: x;\n" ++
  "constraint int_lin_eq([0, -1], [x, y], 0);\n" ++
  "solve satisfy;\n"

/-- The variable occurs twice in the row; the recognizer must not treat
    the first occurrence as a unique coefficient. -/
def linearDupSrc : String :=
  "var int: x;\nconstraint int_lin_eq([1, 1], [x, x], 0);\n" ++
  "solve satisfy;\n"

/-- Forced clauses with the wrong polarity: neither `forced` nor
    `caseSplit` applies. -/
def forcedWrongPolaritySrc : String :=
  "var bool: c;\nvar bool: r;\nvar int: x;\n" ++
  "constraint int_eq_reif(x, 7, r);\n" ++
  "constraint bool_clause([], [c, r]);\n" ++
  "constraint bool_clause([c], [r]);\n" ++
  "solve satisfy;\n"

/-- The forced-branch clauses `-c \/ r` and `c \/ r` force `r`, hence
    `x = 7`.  The recognizer reaches this through the degenerate
    case split with the same reified equality on both sides. -/
def forcedTrueSrc : String :=
  "var bool: c;\nvar bool: r;\nvar int: x;\n" ++
  "constraint int_eq_reif(x, 7, r);\n" ++
  "constraint bool_clause([r], [c]);\n" ++
  "constraint bool_clause([c, r], []);\n" ++
  "solve satisfy;\n"

/-- Unit-coefficient linear row: `x = y` with `y` in `0..5`. -/
def linearSrc : String :=
  "var int: x;\nvar 0..5: y;\n" ++
  "constraint int_lin_eq([1, -1], [x, y], 0);\n" ++
  "solve satisfy;\n"

/-- The row has only the variable itself: `x = 5`. -/
def linearConstSrc : String :=
  "var int: x;\nconstraint int_lin_eq([1], [x], 5);\n" ++ "solve satisfy;\n"

/-- Positive coefficient two: `2x - y = 1`, `y` in `0..4` gives the
    exact integer hull `x` in `[1, 2]`. -/
def linearFloorSrc : String :=
  "var 0..4: y;\nvar int: x;\n" ++
  "constraint int_lin_eq([2, -1], [x, y], 1);\n" ++
  "solve satisfy;\n"

/-- Negative coefficient two: `-2x + y = -1` is the same relation. -/
def linearNegSrc : String :=
  "var 0..4: y;\nvar int: x;\n" ++
  "constraint int_lin_eq([-2, 1], [x, y], -1);\n" ++
  "solve satisfy;\n"

/-- Multi-pass fixpoint: `y` is derived from `z`, then `x` from `y`. -/
def chainSrc : String :=
  "var 0..5: z;\nvar int: y;\nvar int: x;\n" ++
  "constraint int_lin_eq([1, -1], [y, z], 0);\n" ++
  "constraint int_lin_eq([1, -1], [x, y], 0);\n" ++
  "solve satisfy;\n"

/-! ## Certificate checker with planted unsound mutations -/

def firstCertFor (m : Model) (x : Ident) : Option BoundCert :=
  let certs := (deriveCerts m (m.variables.length + 1) (nativeEnv m) []).2
  certs.find? (fun c => c.var.name = x.name)

def bumpCoeff (c : BoundCert) : BoundCert :=
  match c.rule with
  | .linear row coeff => { c with rule := .linear row (coeff + 1) }
  | r => { c with rule := r }

/-- Take a genuine certificate from the recognizer and plant an unsound
    mutation; the verified checker must reject it. -/
def checkerRejects (st : St) (label src : String) (x : Ident)
    (mutate : BoundCert → BoundCert) : IO St := do
  let m := normalizeFull (parseOrPanic src)
  let mut st := st
  match firstCertFor m x with
  | none =>
      st ← st.check s!"{label}: recognizer produced a certificate" false
      pure st
  | some cert =>
      st ← st.check s!"{label}: planted mutation rejected"
        (match checkCerts m (nativeEnv m) [mutate cert] with
         | none => true
         | some _ => false)
      pure st

/-! ## Driver -/

def diag (n : Nat) : List (List Int) :=
  (List.range n).map (fun k => [Int.ofNat k, Int.ofNat k])

def triag (n : Nat) : List (List Int) :=
  (List.range n).map (fun k => [Int.ofNat k, Int.ofNat k, Int.ofNat k])

def run : IO UInt32 := do
  let mut st : St := { passed := 0, failed := 0 }

  -- Case split: positive, companion UNSAT, planted near-misses.
  st ← positiveTest st "U1 case split" splitSrc [[0], [10]]
  st ← unsatTest st "U1 case split excludes both anchors"
    (splitWith "constraint int_ne(x, 0);\nconstraint int_ne(x, 10);\n")
  st ← unsupportedTest st "U1 plant missing split side" splitMissingSrc
  st ← unsupportedTest st "U1 plant one-directional implication" oneDirectionalSrc
  st ← unsupportedTest st "U1 plant non-reified equality" nonReifSrc
  st ← unsupportedTest st "U1 plant bare unbounded variable" bareSrc
  st ← unsupportedTest st "U1 plant partial derivation" partialSrc
  st ← unsupportedTest st "U1 plant one-sided inequality" oneSidedSrc
  st ← unsupportedTest st "U1 plant zero coefficient" linearZeroSrc
  st ← unsupportedTest st "U1 plant duplicate occurrence" linearDupSrc
  st ← unsupportedTest st "U1 plant forced wrong polarity" forcedWrongPolaritySrc

  -- Forced branch and linear rule positives.
  st ← positiveTest st "U1 forced true branch" forcedTrueSrc [[7], [7]]
  st ← positiveTest st "U1 linear unit coefficient" linearSrc (diag 6)
  st ← positiveTest st "U1 linear constant row" linearConstSrc [[5]]
  st ← positiveTest st "U1 linear positive coefficient floor/ceil"
    linearFloorSrc [[1, 1], [3, 2]]
  st ← positiveTest st "U1 linear negative coefficient floor/ceil"
    linearNegSrc [[1, 1], [3, 2]]
  st ← positiveTest st "U1 multi-pass chain" chainSrc (triag 6)

  -- The checker rejects unsound mutations of genuine certificates.
  let x := Ident.mk "x"
  st ← checkerRejects st "U1 checker narrowed split lower bound" splitSrc x
    (fun c => { c with lo := c.lo + 1 })
  st ← checkerRejects st "U1 checker narrowed split upper bound" splitSrc x
    (fun c => { c with hi := c.hi - 1 })
  st ← checkerRejects st "U1 checker wrong linear coefficient" linearFloorSrc x
    bumpCoeff
  st ← checkerRejects st "U1 checker narrowed linear lower bound" linearFloorSrc x
    (fun c => { c with lo := c.lo + 1 })
  st ← checkerRejects st "U1 checker narrowed linear upper bound" linearFloorSrc x
    (fun c => { c with hi := c.hi - 1 })

  IO.println s!"BoundsTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "BoundsTest: OK"
    return 0
  else
    return 1

end Tests.Compiler.BoundsTest

def main : IO UInt32 := Tests.Compiler.BoundsTest.run
