/-
Purpose: Regression tests for the certified literal folding passes (PLAN.md
tasks L1, L2 and L3): ground decisions, literal reification results and
constant-set cardinality.
Dependencies: Compiler.LiteralFold/Normalize, parser, checker, emitter and
Core enumeration; no Legacy imports.
DAG: certified compiler -> this regression executable.

Every ground shape (`int_eq/ne/le/lt/ge/gt`, `int_lin_eq/le/ne`) is tested
twice: a true instance must be dropped (the compiled problem keeps the full
box), a false instance must become the always-false row (the compiled
problem has no accepted assignment and Core returns `.unsat`).

Every scalar reification symmetric table entry is tested with both literal
results; the folded constraint is checked by name and the accepted
assignment set is compared with the mathematical relation.  The linear
`true` results are checked the same way.  Linear `false` results stay
unfolded and must be rejected by the compiler (honest unsupported), never
silently dropped or rewritten.

`set_card(R,x)` with a literal/range set `R` is folded to `int_eq(x, |R|)`:
`{1,1}` has cardinality one while `{}` and reversed ranges have zero.  Each
positive rewrite has a companion that forces UNSAT, and ground `set_card`
instances are decided after the rewrite.

All SAT witnesses are emitted and checked against the ORIGINAL source model
by the independent checker.
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

namespace Tests.Compiler.LiteralFoldTest

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

/-- A source model with the two test variables `x`, `y` over `0..2` and the
    given constraint texts. -/
def modelWith (cs : List String) : String :=
  "var 0..2: x;\nvar 0..2: y;\n" ++
  String.join (cs.map (fun c => "constraint " ++ c ++ ";\n")) ++
  "solve satisfy;\n"

/-- The names of the constraints after both literal passes. -/
def foldedNames (src : String) : List String :=
  ((foldLiteralsModel (normalizeModel (parseOrPanic src))).constraints.map
    (fun c => c.name.name))

def allPairs : List (Int × Int) :=
  [0, 1, 2].flatMap (fun x => [0, 1, 2].map (fun y => (x, y)))

def pairsWhere (p : Int → Int → Bool) : List (Int × Int) :=
  allPairs.filter (fun q => p q.1 q.2)

/-- Set equality on pair lists, independent of enumeration order. -/
def samePairs (a b : List (Int × Int)) : Bool :=
  a.length == b.length && allPairs.all (fun q => a.count q == b.count q)

/-- The accepted assignment set of the compiled source model, as `(x,y)`
    pairs.  `none` means the model did not compile or an accepted
    assignment had an unexpected shape. -/
def acceptedPairs (m : Model) : Option (List (Int × Int)) :=
  match compileModelFull m with
  | .error _ => none
  | .ok p =>
      let as := (allAssigns p.domains).filter (accepts p)
      as.mapM fun a =>
        match a with
        | [.int x, .int y] => some (x, y)
        | _ => none

/-- Is the accepted assignment set exactly `expected` (up to order)? -/
def acceptedSetIs (m : Model) (expected : List (Int × Int)) : Bool :=
  match acceptedPairs m with
  | some as => samePairs as expected
  | none => false

/-- Core's verdict on the compiled source model, for cross-checking the
    enumeration result on the SAT side. -/
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

/-! ## L1 — ground decisions, every shape -/

/-- A true ground constraint is dropped: the fold leaves no constraint, the
    compiled problem keeps the full box, and every witness checks. -/
def groundTrueTest (st : St) (label c : String) : IO St := do
  let m := parseOrPanic (modelWith [c])
  let mut st := st
  st ← st.check s!"ground true {label}: constraint dropped"
    (foldedNames (modelWith [c]) == [])
  st ← st.check s!"ground true {label}: full box accepted"
    (acceptedSetIs m allPairs)
  st ← st.check s!"ground true {label}: Core is SAT" (verdict m == "sat")
  st ← st.check s!"ground true {label}: witnesses check"
    (← witnessesAccepted m)
  pure st

/-- A false ground constraint becomes `int_lin_le([],[],-1)`: no assignment
    is accepted and Core returns `.unsat`, never a dropped constraint. -/
def groundFalseTest (st : St) (label c : String) : IO St := do
  let m := parseOrPanic (modelWith [c])
  let mut st := st
  st ← st.check s!"ground false {label}: false row emitted"
    (foldedNames (modelWith [c]) == ["int_lin_le"])
  st ← st.check s!"ground false {label}: no assignment accepted"
    (acceptedSetIs m [])
  st ← st.check s!"ground false {label}: Core is UNSAT"
    (verdict m == "unsat")
  pure st

/-! ## L2 — literal reification results -/

/-- A reification with a literal result is rewritten to `expectedName`; the
    accepted assignment set of the compiled model equals the mathematical
    relation `expected`. -/
def reifTest (st : St) (label c expectedName : String)
    (expected : Int → Int → Bool) : IO St := do
  let m := parseOrPanic (modelWith [c])
  let mut st := st
  st ← st.check s!"reif {label}: folded to {expectedName}"
    (foldedNames (modelWith [c]) == [expectedName])
  st ← st.check s!"reif {label}: accepted set matches semantics"
    (acceptedSetIs m (pairsWhere expected))
  st ← st.check s!"reif {label}: Core is SAT" (verdict m == "sat")
  st ← st.check s!"reif {label}: witnesses check"
    (← witnessesAccepted m)
  pure st

/-- The same rewrite with a logically opposite companion constraint: the
    compiled model must be UNSAT (this pins the direction of swaps). -/
def reifUnsatTest (st : St) (label c companion : String) : IO St := do
  let m := parseOrPanic (modelWith [c, companion])
  let mut st := st
  st ← st.check s!"reif {label} + opposite: no assignment accepted"
    (acceptedSetIs m [])
  st ← st.check s!"reif {label} + opposite: Core is UNSAT"
    (verdict m == "unsat")
  pure st

/-- A scalar literal-result shape: folded name, true relation, false
    relation and the two opposite companions. -/
def scalarReif (st : St) (label cTrue cFalse nameTrue nameFalse : String)
    (predTrue predFalse : Int → Int → Bool)
    (oppTrue oppFalse : String) : IO St := do
  let mut st := st
  st ← reifTest st s!"{label} true" cTrue nameTrue predTrue
  st ← reifUnsatTest st s!"{label} true" cTrue oppTrue
  st ← reifTest st s!"{label} false" cFalse nameFalse predFalse
  st ← reifUnsatTest st s!"{label} false" cFalse oppFalse
  pure st

/-- A linear `true` literal result is rewritten to the plain linear form. -/
def linearReifTrue (st : St) (label c name : String)
    (pred : Int → Int → Bool) (opp : String) : IO St := do
  let mut st := st
  st ← reifTest st label c name pred
  st ← reifUnsatTest st label c opp
  pure st

/-- A linear `false` literal result is NOT rewritten; the compiler must
    reject the model (honest unsupported), and the constraint must still be
    present after the pass. -/
def linearReifFalseUnsupported (st : St) (label c name : String) : IO St := do
  let m := parseOrPanic (modelWith [c])
  let mut st := st
  st ← st.check s!"linear false {label}: left unfolded"
    (foldedNames (modelWith [c]) == [name])
  st ← st.check s!"linear false {label}: compiler rejects"
    (match compileModelFull m with
     | .error _ => true
     | .ok _ => false)
  pure st

/-! ## L3 — constant-set cardinality -/

/-- A `set_card` with a literal set folds to `int_eq(x, |R|)` and the
    accepted assignment set is exactly `x = n` (possibly empty when `n` is
    outside the declared box). -/
def setCardTest (st : St) (label c : String) (n : Int) : IO St := do
  let m := parseOrPanic (modelWith [c])
  let mut st := st
  st ← st.check s!"set_card {label}: folded to int_eq"
    (foldedNames (modelWith [c]) == ["int_eq"])
  st ← st.check s!"set_card {label}: accepted set x = {n}"
    (acceptedSetIs m (pairsWhere (fun x _ => decide (x = n))))
  st ← st.check s!"set_card {label}: Core verdict"
    (verdict m == if 0 ≤ n ∧ n ≤ 2 then "sat" else "unsat")
  if 0 ≤ n ∧ n ≤ 2 then
    st ← st.check s!"set_card {label}: witnesses check"
      (← witnessesAccepted m)
  pure st

/-- A folded `set_card` plus a companion that excludes its unique value is
    UNSAT: this pins the rewrite direction, not merely satisfiability. -/
def setCardUnsatTest (st : St) (label c companion : String) : IO St := do
  let m := parseOrPanic (modelWith [c, companion])
  let mut st := st
  st ← st.check s!"set_card {label} + companion: no assignment accepted"
    (acceptedSetIs m [])
  st ← st.check s!"set_card {label} + companion: Core is UNSAT"
    (verdict m == "unsat")
  pure st

/-! ## L4 — scalar parameter substitution and initializer expansion -/

/-- The L4 fragment pass on the source model (array inlining included). -/
def fragmentModelOf (src : String) : Model :=
  fragmentModel (normalizeModel (parseOrPanic src))

/-- Constraint names after the fragment pass alone. -/
def fragmentNames (src : String) : List String :=
  (fragmentModelOf src).constraints.map (fun c => c.name.name)

/-- Constraint names after the whole normalization (fragment + literal folds). -/
def fullNames (src : String) : List String :=
  ((normalizeFull (parseOrPanic src)).constraints.map (fun c => c.name.name))

/-- Number of scalar declarations still carrying an initializer after the
    fragment pass.  Supported int/bool literals are expanded, so this is the
    count of unsupported (identifier/set) initializers still present. -/
def remainingInitCount (src : String) : Nat :=
  ((fragmentModelOf src).variables.filter (fun d =>
    match d with
    | .basic _ _ _ (some _) => true
    | _ => false)).length

/-- The fragment pass keeps the parameter declarations. -/
def paramCount (src : String) : Nat :=
  (fragmentModelOf src).parameters.length

/-- The first constraint's arguments after the fragment pass. -/
def firstFragmentArgs (src : String) : List Expr :=
  match (fragmentModelOf src).constraints with
  | c :: _ => c.args
  | [] => []

/-- The first fragment constraint has a literal second argument (the
    substituted scalar parameter), while the first argument stays a variable. -/
def substitutedSecondArg (src : String) : Bool :=
  match firstFragmentArgs src with
  | [.basic (.ident _), .basic (.lit _)] => true
  | _ => false

/-- Accepted `(x,y)` pairs read from the compiled store by name, so extra
    fixed bool variables and parameter declarations do not disturb the
    comparison. -/
def acceptedXY (m : Model) (xn yn : String) : Option (List (Int × Int)) :=
  match compileModelFull m with
  | .error _ => none
  | .ok p =>
      ((allAssigns p.domains).filter (accepts p)).mapM fun a =>
        match p.toStore a (Ident.mk xn), p.toStore a (Ident.mk yn) with
        | some (.int u), some (.int v) => some (u, v)
        | _, _ => none

def acceptedXYIs (m : Model) (expected : List (Int × Int)) : Bool :=
  match acceptedXY m "x" "y" with
  | some as => samePairs as expected
  | none => false

/-- A supported L4 rewrite: expected fragment names, no supported initializer
    left, the accepted set, a SAT verdict and independently checked witnesses. -/
def fragmentTest (st : St) (label src : String) (names : List String)
    (expected : List (Int × Int)) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"L4 {label}: fragment names {names}"
    (fragmentNames src == names)
  st ← st.check s!"L4 {label}: no supported initializer retained"
    (remainingInitCount src == 0)
  st ← st.check s!"L4 {label}: accepted set"
    (acceptedXYIs m expected)
  st ← st.check s!"L4 {label}: Core is SAT" (verdict m == "sat")
  st ← st.check s!"L4 {label}: witnesses check" (← witnessesAccepted m)
  pure st

/-- The same rewrite with a companion that excludes its unique value. -/
def fragmentUnsatTest (st : St) (label src : String) (names : List String) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"L4 {label}: fragment names {names}"
    (fragmentNames src == names)
  st ← st.check s!"L4 {label}: no assignment accepted" (acceptedXYIs m [])
  st ← st.check s!"L4 {label}: Core is UNSAT" (verdict m == "unsat")
  pure st

/-- An unsupported initializer stays in place and the compiler rejects the
    model (honest unsupported; never silently dropped). -/
def unsupportedInitTest (st : St) (label src : String) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"L4 {label}: initializer retained" (remainingInitCount src > 0)
  st ← st.check s!"L4 {label}: compiler rejects"
    (match compileModelFull m with
     | .error _ => true
     | .ok _ => false)
  pure st

/-- A ground decision after parameter substitution: the folded constraint list
    is `names` and the accepted set is `expected`. -/
def paramGroundTest (st : St) (label src : String) (names : List String)
    (expected : List (Int × Int)) : IO St := do
  let m := parseOrPanic src
  let mut st := st
  st ← st.check s!"L4 {label}: full names {names}" (fullNames src == names)
  st ← st.check s!"L4 {label}: accepted set" (acceptedXYIs m expected)
  st ← st.check s!"L4 {label}: Core verdict"
    (verdict m == if expected.isEmpty then "unsat" else "sat")
  if !expected.isEmpty then
    st ← st.check s!"L4 {label}: witnesses check" (← witnessesAccepted m)
  pure st

def run : IO UInt32 := do
  let st0 : St := { passed := 0, failed := 0 }
  let mut st := st0

  -- L1: scalar ground shapes.
  st ← groundTrueTest st "int_eq" "int_eq(1, 1)"
  st ← groundFalseTest st "int_eq" "int_eq(1, 2)"
  st ← groundTrueTest st "int_ne" "int_ne(1, 2)"
  st ← groundFalseTest st "int_ne" "int_ne(1, 1)"
  st ← groundTrueTest st "int_le" "int_le(1, 2)"
  st ← groundFalseTest st "int_le" "int_le(2, 1)"
  st ← groundTrueTest st "int_lt" "int_lt(1, 2)"
  st ← groundFalseTest st "int_lt" "int_lt(1, 1)"
  st ← groundTrueTest st "int_ge" "int_ge(2, 1)"
  st ← groundFalseTest st "int_ge" "int_ge(1, 2)"
  st ← groundTrueTest st "int_gt" "int_gt(2, 1)"
  st ← groundFalseTest st "int_gt" "int_gt(2, 2)"

  -- L1: linear ground shapes.
  st ← groundTrueTest st "int_lin_eq" "int_lin_eq([2, 3], [4, 5], 23)"
  st ← groundFalseTest st "int_lin_eq" "int_lin_eq([2, 3], [4, 5], 24)"
  st ← groundTrueTest st "int_lin_le" "int_lin_le([2, 3], [4, 5], 23)"
  st ← groundFalseTest st "int_lin_le" "int_lin_le([2, 3], [4, 5], 22)"
  st ← groundTrueTest st "int_lin_ne" "int_lin_ne([2, 3], [4, 5], 24)"
  st ← groundFalseTest st "int_lin_ne" "int_lin_ne([2, 3], [4, 5], 23)"

  -- L2: constant-set membership literal results are handled by
  -- `restrictSetInModel`; the fold leaves them in place.
  st ← reifTest st "set_in_reif true" "set_in_reif(x, {0, 2}, true)"
    "set_in_reif" (fun x _ => decide (x = 0 ∨ x = 2))
  st ← reifTest st "set_in_reif false" "set_in_reif(x, {0, 2}, false)"
    "set_in_reif" (fun x _ => decide (x = 1))
  st ← groundTrueTest st "set_in_reif ground true"
    "set_in_reif(1, {0, 2}, false)"
  st ← groundFalseTest st "set_in_reif ground false"
    "set_in_reif(1, {0, 2}, true)"

  -- L2: scalar reifications, both literal results.
  st ← scalarReif st "int_eq_reif"
    "int_eq_reif(x, y, true)" "int_eq_reif(x, y, false)"
    "int_eq" "int_ne" (· = ·) (· ≠ ·) "int_ne(x, y)" "int_eq(x, y)"
  st ← scalarReif st "int_ne_reif"
    "int_ne_reif(x, y, true)" "int_ne_reif(x, y, false)"
    "int_ne" "int_eq" (· ≠ ·) (· = ·) "int_eq(x, y)" "int_ne(x, y)"
  st ← scalarReif st "int_le_reif"
    "int_le_reif(x, y, true)" "int_le_reif(x, y, false)"
    "int_le" "int_lt" (· ≤ ·) (fun x y => decide (y < x))
    "int_lt(y, x)" "int_le(x, y)"
  st ← scalarReif st "int_lt_reif"
    "int_lt_reif(x, y, true)" "int_lt_reif(x, y, false)"
    "int_lt" "int_le" (· < ·) (fun x y => decide (y ≤ x))
    "int_le(y, x)" "int_lt(x, y)"
  st ← scalarReif st "int_ge_reif"
    "int_ge_reif(x, y, true)" "int_ge_reif(x, y, false)"
    "int_le" "int_lt" (fun x y => decide (y ≤ x)) (· < ·)
    "int_lt(x, y)" "int_le(y, x)"
  st ← scalarReif st "int_gt_reif"
    "int_gt_reif(x, y, true)" "int_gt_reif(x, y, false)"
    "int_lt" "int_le" (fun x y => decide (y < x)) (· ≤ ·)
    "int_le(x, y)" "int_lt(y, x)"

  -- L2: linear reifications, literal `true` only.
  st ← linearReifTrue st "int_lin_eq_reif true"
    "int_lin_eq_reif([1, -1], [x, y], 0, true)" "int_lin_eq"
    (· = ·) "int_lin_ne([1, -1], [x, y], 0)"
  st ← linearReifTrue st "int_lin_le_reif true"
    "int_lin_le_reif([1, -1], [x, y], 0, true)" "int_lin_le"
    (· ≤ ·) "int_lin_eq([1, -1], [x, y], 1)"
  st ← linearReifTrue st "int_lin_ne_reif true"
    "int_lin_ne_reif([1, -1], [x, y], 0, true)" "int_lin_ne"
    (· ≠ ·) "int_lin_eq([1, -1], [x, y], 0)"

  -- L2: linear literal `false` results stay unsupported, never dropped.
  st ← linearReifFalseUnsupported st "int_lin_eq_reif"
    "int_lin_eq_reif([1, -1], [x, y], 0, false)" "int_lin_eq_reif"
  st ← linearReifFalseUnsupported st "int_lin_le_reif"
    "int_lin_le_reif([1, -1], [x, y], 0, false)" "int_lin_le_reif"
  st ← linearReifFalseUnsupported st "int_lin_ne_reif"
    "int_lin_ne_reif([1, -1], [x, y], 0, false)" "int_lin_ne_reif"

  -- L3: constant-set cardinality.  `{1,1}` has one distinct element, `{}`
  -- and the reversed interval `3..1` have cardinality zero, `1..3` has
  -- three.  The companions below force UNSAT.
  st ← setCardTest st "{1,1}" "set_card({1, 1}, x)" 1
  st ← setCardUnsatTest st "{1,1}" "set_card({1, 1}, x)" "int_ne(x, 1)"
  st ← setCardTest st "{}" "set_card({}, x)" 0
  st ← setCardUnsatTest st "{}" "set_card({}, x)" "int_ne(x, 0)"
  st ← setCardTest st "3..1" "set_card(3..1, x)" 0
  st ← setCardUnsatTest st "3..1" "set_card(3..1, x)" "int_ne(x, 0)"
  st ← setCardTest st "1..3" "set_card(1..3, x)" 3
  st ← setCardUnsatTest st "1..3" "set_card(1..3, x)" "int_eq(x, 3)"
  st ← setCardTest st "1..2" "set_card(1..2, x)" 2

  -- L3: ground literal sets are decided after the set-card rewrite.
  st ← groundTrueTest st "set_card {1,1} ground true" "set_card({1, 1}, 1)"
  st ← groundFalseTest st "set_card {1,1} ground false" "set_card({1, 1}, 2)"
  st ← groundTrueTest st "set_card {} ground true" "set_card({}, 0)"
  st ← groundFalseTest st "set_card {} ground false" "set_card({}, 1)"
  st ← groundTrueTest st "set_card 3..1 ground true" "set_card(3..1, 0)"
  st ← groundFalseTest st "set_card 3..1 ground false" "set_card(3..1, 1)"
  st ← groundTrueTest st "set_card 1..3 ground true" "set_card(1..3, 3)"
  st ← groundFalseTest st "set_card 1..3 ground false" "set_card(1..3, 2)"

  -- L1/L2 ordering: a ground reified literal is decided by the ground pass,
  -- both when true and when false.  The constant `r = false` is true iff the
  -- reified relation itself is false.
  st ← groundTrueTest st "int_eq_reif ground true" "int_eq_reif(3, 1, false)"
  st ← groundFalseTest st "int_eq_reif ground false" "int_eq_reif(3, 3, false)"
  st ← groundTrueTest st "int_ne_reif ground true" "int_ne_reif(3, 3, false)"
  st ← groundFalseTest st "int_ne_reif ground false" "int_ne_reif(3, 1, false)"
  st ← groundTrueTest st "int_le_reif ground true" "int_le_reif(2, 1, false)"
  st ← groundFalseTest st "int_le_reif ground false" "int_le_reif(1, 2, false)"
  st ← groundTrueTest st "int_lt_reif ground true" "int_lt_reif(2, 1, false)"
  st ← groundFalseTest st "int_lt_reif ground false" "int_lt_reif(1, 2, false)"
  st ← groundTrueTest st "int_ge_reif ground true" "int_ge_reif(1, 2, false)"
  st ← groundFalseTest st "int_ge_reif ground false" "int_ge_reif(2, 1, false)"
  st ← groundTrueTest st "int_gt_reif ground true" "int_gt_reif(1, 2, false)"
  st ← groundFalseTest st "int_gt_reif ground false" "int_gt_reif(2, 1, false)"
  st ← groundTrueTest st "int_lin_eq_reif ground true"
    "int_lin_eq_reif([2, 3], [4, 5], 24, false)"
  st ← groundFalseTest st "int_lin_eq_reif ground false"
    "int_lin_eq_reif([2, 3], [4, 5], 23, false)"
  st ← groundTrueTest st "int_lin_le_reif ground true"
    "int_lin_le_reif([2, 3], [4, 5], 22, false)"
  st ← groundFalseTest st "int_lin_le_reif ground false"
    "int_lin_le_reif([2, 3], [4, 5], 23, false)"
  st ← groundTrueTest st "int_lin_ne_reif ground true"
    "int_lin_ne_reif([2, 3], [4, 5], 23, false)"
  st ← groundFalseTest st "int_lin_ne_reif ground false"
    "int_lin_ne_reif([2, 3], [4, 5], 24, false)"

  -- L4: scalar parameter substitution in a constraint argument.
  let intParam :=
    "int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
    "constraint int_eq(x, p);\nsolve satisfy;\n"
  st ← fragmentTest st "int parameter" intParam ["int_eq"]
    (pairsWhere (fun x _ => decide (x = 1)))
  st ← st.check "L4 int parameter: declaration retained"
    (paramCount intParam == 1)
  st ← st.check "L4 int parameter: second argument is the literal"
    (substitutedSecondArg intParam)
  st ← fragmentUnsatTest st "int parameter negative"
    ("int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint int_eq(x, p);\nconstraint int_ne(x, 1);\n" ++
     "solve satisfy;\n")
    ["int_eq", "int_ne"]

  let boolParam :=
    "bool: q = true;\nvar bool: b;\nvar 0..2: x;\nvar 0..2: y;\n" ++
    "constraint bool_not(b, q);\nsolve satisfy;\n"
  st ← fragmentTest st "bool parameter" boolParam ["bool_not"] allPairs
  st ← st.check "L4 bool parameter: declaration retained"
    (paramCount boolParam == 1)
  st ← st.check "L4 bool parameter: second argument is the literal"
    (substitutedSecondArg boolParam)
  st ← fragmentUnsatTest st "bool parameter negative"
    ("bool: q = true;\nvar bool: b;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint bool_not(b, q);\nconstraint bool_not(b, false);\n" ++
     "solve satisfy;\n")
    ["bool_not", "bool_not"]

  -- L4: the parameter may occupy either side of the predicate.
  st ← fragmentTest st "int parameter first argument"
    ("int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint int_eq(p, x);\nsolve satisfy;\n")
    ["int_eq"] (pairsWhere (fun x _ => decide (x = 1)))
  st ← fragmentUnsatTest st "int parameter first argument negative"
    ("int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint int_eq(p, x);\nconstraint int_ne(x, 1);\nsolve satisfy;\n")
    ["int_eq", "int_ne"]
  st ← fragmentTest st "bool parameter first argument"
    ("bool: q = true;\nvar bool: b;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint bool_not(q, b);\nsolve satisfy;\n")
    ["bool_not"] allPairs
  st ← fragmentUnsatTest st "bool parameter first argument negative"
    ("bool: q = true;\nvar bool: b;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint bool_not(q, b);\nconstraint bool_not(b, false);\n" ++
     "solve satisfy;\n")
    ["bool_not", "bool_not"]

  -- L4: variable initializer expansion.
  let intInit := "var 0..2: x = 1;\nvar 0..2: y;\nsolve satisfy;\n"
  st ← fragmentTest st "int initializer" intInit ["int_eq"]
    (pairsWhere (fun x _ => decide (x = 1)))
  st ← fragmentUnsatTest st "int initializer negative"
    ("var 0..2: x = 1;\nvar 0..2: y;\nconstraint int_ne(x, 1);\n" ++
     "solve satisfy;\n")
    ["int_ne", "int_eq"]

  st ← fragmentTest st "bool initializer true"
    ("var bool: b = true;\nvar 0..2: x;\nvar 0..2: y;\nsolve satisfy;\n")
    ["bool_not"] allPairs
  st ← fragmentTest st "bool initializer false"
    ("var bool: b = false;\nvar 0..2: x;\nvar 0..2: y;\nsolve satisfy;\n")
    ["bool_not"] allPairs
  st ← fragmentUnsatTest st "bool initializer negative"
    ("var bool: b = true;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint bool_not(b, true);\nsolve satisfy;\n")
    ["bool_not", "bool_not"]

  -- L4: composition order — an initializer that names a scalar parameter
  -- is substituted first and then expanded.
  let paramInit :=
    "int: p = 2;\nvar 0..2: x = p;\nvar 0..2: y;\nsolve satisfy;\n"
  st ← fragmentTest st "initializer reads int parameter" paramInit ["int_eq"]
    (pairsWhere (fun x _ => decide (x = 2)))
  st ← st.check "L4 initializer reads int parameter: declaration retained"
    (paramCount paramInit == 1)
  st ← fragmentTest st "initializer reads bool parameter"
    ("bool: q = true;\nvar bool: b = q;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "solve satisfy;\n")
    ["bool_not"] allPairs
  st ← fragmentUnsatTest st "initializer reads bool parameter negative"
    ("bool: q = true;\nvar bool: b = q;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint bool_not(b, true);\nsolve satisfy;\n")
    ["bool_not", "bool_not"]

  -- L4: ground decisions after parameter substitution.
  st ← paramGroundTest st "int parameter ground true"
    ("int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint int_eq(p, 1);\nsolve satisfy;\n")
    [] allPairs
  st ← paramGroundTest st "int parameter ground false"
    ("int: p = 1;\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "constraint int_eq(p, 2);\nsolve satisfy;\n")
    ["int_lin_le"] []

  -- L4: unsupported initializers stay on the declaration and keep the
  -- model outside the certified fragment.
  st ← unsupportedInitTest st "identifier initializer"
    "var 0..2: y;\nvar 0..2: x = y;\nsolve satisfy;\n"
  st ← unsupportedInitTest st "set initializer"
    ("var set of 0..2: s = {0, 1};\nvar 0..2: x;\nvar 0..2: y;\n" ++
     "solve satisfy;\n")

  IO.println s!"LiteralFoldTest: {st.passed} passed, {st.failed} failed"
  if st.failed == 0 then
    IO.println "LiteralFoldTest: OK"
    return 0
  else
    return 1

end Tests.Compiler.LiteralFoldTest

def main : IO UInt32 := Tests.Compiler.LiteralFoldTest.run
