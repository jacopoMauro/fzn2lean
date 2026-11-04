/-
Runtime tests for the dedicated Boolean propagators in
`LeanFzn/Engine/Props/BoolExt.lean`.

Run with:
  lake env lean --run Tests/Engine/BoolExtTest.lean

Coverage: `bool_not`, `bool_and`, `bool_or`, `bool_eq` and
`array_bool_and` — both propagation directions, forcing, links,
inconsistent fixed boxes, general support pruning, conflicts, malformed
non-Boolean inputs, runtime entailment over the accepted assignments, and
a local differential table against the generic leaf checker.
-/
import LeanFzn.Engine.Props.BoolExt
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.BoolExtTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"BoolExtTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-- A compiled problem carrying just the supplied domains and constraints. -/
def mkProblem (ds : List Dom) (cs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := cs
    objective := ()
    source := default
    toStore := fun _ _ => none }

/-- Convert domains the way the engine does. -/
def convInit (ds : List Dom) : Array DomC :=
  ds.toArray.map fun d => (DomC.ofDom? d).getD DomC.empty

/-! ## Inspecting `PropOut` -/

def isFix {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Bool
  | .fix => true
  | _ => false

def isConflict {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Bool
  | .conflict _ => true
  | _ => false

def conflictClause? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option Clause
  | .conflict c => some (T.decodeClause c.lits)
  | _ => none

def pruneLits? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option (List Literal)
  | .prune ps => some (ps.toList.map fun q => q.1.lit)
  | _ => none

def pruneClauses? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option (List Clause)
  | .prune ps => some (ps.toList.map fun q => T.decodeClause q.2.lits)
  | _ => none

/-- Compare two propagator outputs by kind, decoded clauses and literals. -/
def sameOutput {p : CompiledProblem DomConstraint} {T : LitTable}
    (a b : PropOut p T) : Bool :=
  conflictClause? a == conflictClause? b &&
  pruneLits? a == pruneLits? b &&
  pruneClauses? a == pruneClauses? b &&
  isFix a == isFix b

/-! ## Runtime clause and literal checks -/

/-- Bool-valued clause evaluator over `Literal.eval`. -/
def clauseEval (c : Clause) (b : List Value) : Bool :=
  c.any fun l => l.eval b == some true

/-- Evaluate a literal on an engine view. -/
def litEvalView (view : EngineView) (l : Literal) : Option Bool :=
  (view.doms.getD l.atom.slot DomC.empty).evalLit l

def checkAllFalse (label : String) (view : EngineView) (ls : List Literal) : IO Unit :=
  for l in ls do
    check s!"{label}: {repr l} is false (got {repr (litEvalView view l)})"
      (litEvalView view l == some false)

def checkLitNone (label : String) (view : EngineView) (l : Literal) : IO Unit :=
  check s!"{label}: {repr l} is unassigned (got {repr (litEvalView view l)})"
    (litEvalView view l == none)

/-- Runtime entailment check: every accepted assignment satisfies the clause. -/
def checkClauseEntailedRuntime (label : String)
    (p : CompiledProblem DomConstraint) (c : Clause) : IO Unit :=
  for b in allAssigns p.domains do
    if accepts p b then
      check s!"{label}: clause satisfied by {repr b}" (clauseEval c b)

/-- One expected conflict, with exact clause. -/
def checkConflict (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) (out : PropOut p ({} : LitTable))
    (expected : Clause) : IO Unit :=
  match conflictClause? out with
  | some c => do
      check s!"{label}: clause {repr c} expected {repr expected}" (c == expected)
      checkAllFalse label view c
      checkClauseEntailedRuntime label p c
  | none => fail s!"{label}: expected .conflict, got another output kind"

/-- One expected prune list, exactly ordered, with exact reasons.  Every
emitted reason is checked for runtime entailment and every emitted unit is
checked unassigned. -/
def checkPrunes (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) (out : PropOut p ({} : LitTable))
    (expected : List (Literal × Clause)) : IO Unit :=
  match pruneLits? out, pruneClauses? out with
  | some lits, some cs => do
      check s!"{label}: units {repr lits} expected {repr (expected.map (·.1))}"
        (lits == expected.map (·.1))
      check s!"{label}: reasons {repr cs} expected {repr (expected.map (·.2))}"
        (cs == expected.map (·.2))
      for (lit, reason) in expected do
        checkLitNone label view lit
        checkAllFalse label view (reason.filter (fun l => l != lit))
        checkClauseEntailedRuntime label p reason
  | _, _ => fail s!"{label}: expected a prune, got another output kind"

def checkFix {p : CompiledProblem DomConstraint} {T : LitTable}
    (label : String) (out : PropOut p T) : IO Unit :=
  check s!"{label}: expected .fix" (isFix out)

/-! ## Concrete domains and views -/

/-- Full Boolean domain `{false, true}`. -/
def domB : Dom := ⟨.general [.bool false, .bool true]⟩
/-- Fixed-false Boolean domain. -/
def domBF : Dom := ⟨.general [.bool false]⟩
/-- Fixed-true Boolean domain. -/
def domBT : Dom := ⟨.general [.bool true]⟩
/-- A non-Boolean domain. -/
def domInt : Dom := ⟨.holes 0 5 []⟩

def bcF : DomC := DomC.bool 1
def bcT : DomC := DomC.bool 2
def bcB : DomC := DomC.bool 3
def bcE : DomC := DomC.bool 0
def bcInt : DomC := DomC.bounds 0 5

/-- A two-slot view helper. -/
def view2 (d0 d1 : DomC) : EngineView := { doms := #[d0, d1], level := 0 }

/-- A three-slot view helper. -/
def view3 (d0 d1 d2 : DomC) : EngineView := { doms := #[d0, d1, d2], level := 0 }

/-! ## 1. `bool_not` -/

def pNot : CompiledProblem DomConstraint :=
  mkProblem [domB, domB] [.boolNotSlot 0 1]

theorem hmemNot : DomConstraint.boolNotSlot 0 1 ∈ pNot.constraints := by
  simp [pNot, mkProblem]

def outNot (view : EngineView) : PropOut pNot ({} : LitTable) :=
  (boolNotPropWith pNot ({} : LitTable) 0 1 hmemNot).run view

/-- `j = ¬i` with `i = false` forces `j = true`. -/
def checkNotForward : IO Unit :=
  checkPrunes "not i=false -> j=true" pNot (view2 bcF bcB)
    (outNot (view2 bcF bcB))
    [(posBool 1 true, [posBool 1 true, posBool 0 true])]

/-- `j = ¬i` with `j = true` forces `i = false`. -/
def checkNotBackward : IO Unit :=
  checkPrunes "not j=true -> i=false" pNot (view2 bcB bcT)
    (outNot (view2 bcB bcT))
    [(posBool 0 false, [posBool 0 false, posBool 1 false])]

/-- Both fixed inconsistently. -/
def checkNotConflict : IO Unit :=
  checkConflict "not false/false conflict" pNot (view2 bcF bcF)
    (outNot (view2 bcF bcF)) [posBool 0 true, posBool 1 true]

/-- Both free: every value has support. -/
def checkNotFix : IO Unit :=
  checkFix "not free fix" (outNot (view2 bcB bcB))

/-! ## 2. `bool_and` -/

def pAnd : CompiledProblem DomConstraint :=
  mkProblem [domB, domB, domB] [.boolAndSlot 0 1 2]

theorem hmemAnd : DomConstraint.boolAndSlot 0 1 2 ∈ pAnd.constraints := by
  simp [pAnd, mkProblem]

def outAnd (view : EngineView) : PropOut pAnd ({} : LitTable) :=
  (boolAndPropWith pAnd ({} : LitTable) 0 1 2 hmemAnd).run view

/-- `k = true` forces both operands true. -/
def checkAndKTrue : IO Unit :=
  checkPrunes "and k=true forces" pAnd (view3 bcB bcB bcT)
    (outAnd (view3 bcB bcB bcT))
    [ (posBool 0 true, [posBool 0 true, posBool 2 false])
    , (posBool 1 true, [posBool 1 true, posBool 2 false]) ]

/-- `k = false` with both operands fixed true is inconsistent. -/
def checkAndKFalseConflict : IO Unit :=
  checkConflict "and true/true/false conflict" pAnd (view3 bcT bcT bcF)
    (outAnd (view3 bcT bcT bcF))
    [posBool 0 false, posBool 1 false, posBool 2 true]

/-- Fixed `i = true` links `k` and `j`: with `k = false`, `j` is false. -/
def checkAndILink : IO Unit :=
  checkPrunes "and i=true,k=false -> j=false" pAnd (view3 bcT bcB bcF)
    (outAnd (view3 bcT bcB bcF))
    [(posBool 1 false, [posBool 1 false, posBool 0 false, posBool 2 true])]

/-- Fixed `i = false` forces `k = false`. -/
def checkAndIFalse : IO Unit :=
  checkPrunes "and i=false -> k=false" pAnd (view3 bcF bcB bcB)
    (outAnd (view3 bcF bcB bcB))
    [(posBool 2 false, [posBool 2 false, posBool 0 true])]

/-- Another inconsistent fixed box. -/
def checkAndConflict : IO Unit :=
  checkConflict "and i/j fixed conflict" pAnd (view3 bcT bcF bcT)
    (outAnd (view3 bcT bcF bcT))
    [posBool 0 false, posBool 1 true, posBool 2 false]

/-- General support pruning with one operand fixed false. -/
def checkAndSupport : IO Unit :=
  checkPrunes "and support prune k" pAnd (view3 bcT bcF bcB)
    (outAnd (view3 bcT bcF bcB))
    [(posBool 2 false, [posBool 2 false, posBool 0 false, posBool 1 true])]

/-- A fully free box is a fixpoint. -/
def checkAndFix : IO Unit :=
  checkFix "and free fix" (outAnd (view3 bcB bcB bcB))

/-! ## 3. `bool_or` -/

def pOr : CompiledProblem DomConstraint :=
  mkProblem [domB, domB, domB] [.boolOrSlot 0 1 2]

theorem hmemOr : DomConstraint.boolOrSlot 0 1 2 ∈ pOr.constraints := by
  simp [pOr, mkProblem]

def outOr (view : EngineView) : PropOut pOr ({} : LitTable) :=
  (boolOrPropWith pOr ({} : LitTable) 0 1 2 hmemOr).run view

/-- `k = false` forces both operands false. -/
def checkOrKFalse : IO Unit :=
  checkPrunes "or k=false forces" pOr (view3 bcB bcB bcF)
    (outOr (view3 bcB bcB bcF))
    [ (posBool 0 false, [posBool 0 false, posBool 2 true])
    , (posBool 1 false, [posBool 1 false, posBool 2 true]) ]

/-- `k = true` with both operands fixed false is inconsistent. -/
def checkOrKTrueConflict : IO Unit :=
  checkConflict "or false/false/true conflict" pOr (view3 bcF bcF bcT)
    (outOr (view3 bcF bcF bcT))
    [posBool 0 true, posBool 1 true, posBool 2 false]

/-- Fixed `i = false` links `k` and `j`: with `k = true`, `j` is true. -/
def checkOrILink : IO Unit :=
  checkPrunes "or i=false,k=true -> j=true" pOr (view3 bcF bcB bcT)
    (outOr (view3 bcF bcB bcT))
    [(posBool 1 true, [posBool 1 true, posBool 0 true, posBool 2 false])]

/-- Fixed `i = true` forces `k = true`. -/
def checkOrITrue : IO Unit :=
  checkPrunes "or i=true -> k=true" pOr (view3 bcT bcB bcB)
    (outOr (view3 bcT bcB bcB))
    [(posBool 2 true, [posBool 2 true, posBool 0 false])]

/-- Another inconsistent fixed box. -/
def checkOrConflict : IO Unit :=
  checkConflict "or i/j fixed conflict" pOr (view3 bcF bcT bcF)
    (outOr (view3 bcF bcT bcF))
    [posBool 0 true, posBool 1 false, posBool 2 true]

/-- A fully free box is a fixpoint. -/
def checkOrFix : IO Unit :=
  checkFix "or free fix" (outOr (view3 bcB bcB bcB))

/-! ## 4. `bool_eq` -/

def pEq : CompiledProblem DomConstraint :=
  mkProblem [domB, domB] [.boolEqSlot 0 1]

theorem hmemEq : DomConstraint.boolEqSlot 0 1 ∈ pEq.constraints := by
  simp [pEq, mkProblem]

def outEq (view : EngineView) : PropOut pEq ({} : LitTable) :=
  (boolEqPropWith pEq ({} : LitTable) 0 1 hmemEq).run view

/-- Fixed `i = false` forces `j = false`. -/
def checkEqForward : IO Unit :=
  checkPrunes "eq i=false -> j=false" pEq (view2 bcF bcB)
    (outEq (view2 bcF bcB))
    [(posBool 1 false, [posBool 1 false, posBool 0 true])]

/-- Fixed `j = true` forces `i = true`. -/
def checkEqBackward : IO Unit :=
  checkPrunes "eq j=true -> i=true" pEq (view2 bcB bcT)
    (outEq (view2 bcB bcT))
    [(posBool 0 true, [posBool 0 true, posBool 1 false])]

/-- Disjoint fixed singleton domains conflict. -/
def checkEqConflict : IO Unit :=
  checkConflict "eq false/true conflict" pEq (view2 bcF bcT)
    (outEq (view2 bcF bcT)) [posBool 0 true, posBool 1 false]

/-- Both free: a fixpoint. -/
def checkEqFix : IO Unit :=
  checkFix "eq free fix" (outEq (view2 bcB bcB))

/-! ## 5. `array_bool_and` -/

def pArr : CompiledProblem DomConstraint :=
  mkProblem [domB, domB, domB] [.arrayBoolAndSlot [0, 1] 2]

theorem hmemArr : DomConstraint.arrayBoolAndSlot [0, 1] 2 ∈ pArr.constraints := by
  simp [pArr, mkProblem]

def outArr (view : EngineView) : PropOut pArr ({} : LitTable) :=
  (arrayBoolAndPropWith pArr ({} : LitTable) [0, 1] 2 hmemArr).run view

def pArrEmpty : CompiledProblem DomConstraint :=
  mkProblem [domB] [.arrayBoolAndSlot [] 0]

theorem hmemArrEmpty : DomConstraint.arrayBoolAndSlot [] 0 ∈ pArrEmpty.constraints := by
  simp [pArrEmpty, mkProblem]

def outArrEmpty (view : EngineView) : PropOut pArrEmpty ({} : LitTable) :=
  (arrayBoolAndPropWith pArrEmpty ({} : LitTable) [] 0 hmemArrEmpty).run view

/-- The empty conjunction forces `k = true`. -/
def checkArrEmpty : IO Unit :=
  checkPrunes "array empty -> k=true" pArrEmpty (view2 bcB bcB)
    (outArrEmpty (view2 bcB bcB))
    [(posBool 0 true, [posBool 0 true])]

/-- All-true sources force `k = true`. -/
def checkArrAllTrue : IO Unit :=
  checkPrunes "array all-true -> k=true" pArr (view3 bcT bcT bcB)
    (outArr (view3 bcT bcT bcB))
    [(posBool 2 true, [posBool 2 true, posBool 0 false, posBool 1 false])]

/-- A false source forces `k = false`. -/
def checkArrFalseSource : IO Unit :=
  checkPrunes "array false source -> k=false" pArr (view3 bcF bcB bcB)
    (outArr (view3 bcF bcB bcB))
    [(posBool 2 false, [posBool 2 false, posBool 0 true])]

/-- `k = false` with all other sources true forces the last source false. -/
def checkArrLast : IO Unit :=
  checkPrunes "array last source -> false" pArr (view3 bcT bcB bcF)
    (outArr (view3 bcT bcB bcF))
    [(posBool 1 false, [posBool 1 false, posBool 0 false, posBool 2 true])]

/-- All sources true with `k = false` conflicts. -/
def checkArrConflict : IO Unit :=
  checkConflict "array true/true/false conflict" pArr (view3 bcT bcT bcF)
    (outArr (view3 bcT bcT bcF))
    [posBool 0 false, posBool 1 false, posBool 2 true]

/-- A free array is a fixpoint. -/
def checkArrFix : IO Unit :=
  checkFix "array free fix" (outArr (view3 bcB bcB bcB))

/-- A non-Boolean source view is malformed: the run is `.fix`. -/
def checkArrMalformed : IO Unit :=
  checkFix "array non-Boolean source fix" (outArr (view3 bcInt bcB bcB))

/-! ## 6. Malformed fixed-arity inputs -/

def checkMalformed : IO Unit := do
  checkFix "not malformed i" ((boolNotPropWith pNot ({} : LitTable) 0 1 hmemNot).run
    (view2 bcInt bcB))
  checkFix "not malformed j" ((boolNotPropWith pNot ({} : LitTable) 0 1 hmemNot).run
    (view2 bcB bcInt))
  checkFix "and malformed i" ((boolAndPropWith pAnd ({} : LitTable) 0 1 2 hmemAnd).run
    (view3 bcInt bcB bcB))
  checkFix "or malformed i" ((boolOrPropWith pOr ({} : LitTable) 0 1 2 hmemOr).run
    (view3 bcInt bcB bcB))
  checkFix "eq malformed i" ((boolEqPropWith pEq ({} : LitTable) 0 1 hmemEq).run
    (view2 bcInt bcB))
  checkFix "not out-of-range i" ((boolNotPropWith pNot ({} : LitTable) 0 1 hmemNot).run
    ({ doms := #[], level := 0 }))

/-! ## 7. Differential table -/

/-- Local version of the production adapter, routing the five dedicated
Boolean families to the new builders and everything else to the generic
leaf checker. -/
def propsOfTest (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .boolNotSlot i j =>
        boolNotPropWith p T i j (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolAndSlot i j k =>
        boolAndPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolOrSlot i j k =>
        boolOrPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .boolEqSlot i j =>
        boolEqPropWith p T i j (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayBoolAndSlot is k =>
        arrayBoolAndPropWith p T is k (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- The fully generic table: every constraint goes to the leaf checker.
This is the comparison baseline; `propsOf` itself now includes the
dedicated Boolean builders after integration, so it cannot serve as
the generic side of the differential. -/
def propsOfLeaf (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    propCheckV2With p T x.1 init
      (hinit x.1 (List.mem_toArray.mp x.2))
      (List.mem_toArray.mp x.2)

/-- Apply one propagator batch of prunings to the domain array. -/
def applyPrunes (doms : Array DomC) (ps : Array (PLit × EClause p T)) : Array DomC :=
  ps.foldl (fun ds q =>
    let s := atomSlot q.1.lit.atom
    ds.set! s ((ds.getD s DomC.empty).applyLit q.1.lit)) doms

/-- One sweep over all propagators, applying prunings in place. -/
def sweep {p : CompiledProblem DomConstraint} {T : LitTable}
    (props : List (PropV2 p T)) (view : EngineView) (doms : Array DomC)
    (count : Nat) (changed : Bool) :
    Option (Array DomC × Nat × Bool) :=
  match props with
  | [] => some (doms, count, changed)
  | pr :: rest =>
      match pr.run { view with doms := doms } with
      | .fix => sweep rest view doms count changed
      | .conflict _ => none
      | .prune ps =>
          let doms' := applyPrunes doms ps
          sweep rest view doms' (count + ps.size) (changed || doms' != doms)

structure DiffResult where
  conflict : Bool
  doms : Array DomC
  fuel : Nat
  prunes : Nat
  deriving Repr

def runLoop {p : CompiledProblem DomConstraint} {T : LitTable}
    (props : List (PropV2 p T)) (view : EngineView) : Nat → DiffResult
  | 0 => { conflict := false, doms := view.doms, fuel := 0, prunes := 0 }
  | f + 1 =>
      match sweep props view view.doms 0 false with
      | none => { conflict := true, doms := view.doms, fuel := 1, prunes := 0 }
      | some (doms, count, changed) =>
          if changed then
            let r := runLoop props { view with doms := doms } f
            { r with fuel := r.fuel + 1, prunes := r.prunes + count }
          else
            { conflict := false, doms := doms, fuel := 1, prunes := count }

/-- A fixed-view fixture: the propagator table must agree with the
generic checker on the conflict verdict. -/
def checkFixedAgreement (label : String) (p : CompiledProblem DomConstraint)
    (hready : initReady p (convInit p.domains) = true) : IO Unit := do
  let T : LitTable := {}
  let init := convInit p.domains
  let hinit := initReady_spec hready
  let dedicated := propsOfTest p T init hinit
  let generic := propsOfLeaf p T init hinit
  let view : EngineView := { doms := init, level := 0 }
  let rd := sweep dedicated.toList view init 0 false
  let rg := sweep generic.toList view init 0 false
  check s!"{label}: dedicated/generic conflict verdict" (rd.isNone == rg.isNone)
  IO.println s!"  fixed {label}: dedicated conflict={rd.isNone} \
generic conflict={rg.isNone}"

def domZero : Dom := ⟨.holes 0 0 []⟩

def pFixNotGood : CompiledProblem DomConstraint :=
  mkProblem [domBF, domBT] [.boolNotSlot 0 1]
def pFixNotBad : CompiledProblem DomConstraint :=
  mkProblem [domBF, domBF] [.boolNotSlot 0 1]
def pFixAndBad : CompiledProblem DomConstraint :=
  mkProblem [domBT, domBT, domBF] [.boolAndSlot 0 1 2]
def pFixOrBad : CompiledProblem DomConstraint :=
  mkProblem [domBF, domBF, domBT] [.boolOrSlot 0 1 2]
def pFixEqBad : CompiledProblem DomConstraint :=
  mkProblem [domBF, domBT] [.boolEqSlot 0 1]
def pFixArrBad : CompiledProblem DomConstraint :=
  mkProblem [domBT, domBT, domBF] [.arrayBoolAndSlot [0, 1] 2]

theorem hreadyFixNotGood : initReady pFixNotGood (convInit pFixNotGood.domains) = true := by
  simp [initReady, pFixNotGood, mkProblem, convInit, domBF, domBT, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyFixNotBad : initReady pFixNotBad (convInit pFixNotBad.domains) = true := by
  simp [initReady, pFixNotBad, mkProblem, convInit, domBF, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyFixAndBad : initReady pFixAndBad (convInit pFixAndBad.domains) = true := by
  simp [initReady, pFixAndBad, mkProblem, convInit, domBT, domBF, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyFixOrBad : initReady pFixOrBad (convInit pFixOrBad.domains) = true := by
  simp [initReady, pFixOrBad, mkProblem, convInit, domBF, domBT, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyFixEqBad : initReady pFixEqBad (convInit pFixEqBad.domains) = true := by
  simp [initReady, pFixEqBad, mkProblem, convInit, domBF, domBT, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyFixArrBad : initReady pFixArrBad (convInit pFixArrBad.domains) = true := by
  simp [initReady, pFixArrBad, mkProblem, convInit, domBT, domBF, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

/-- First slot of the searched prefix that is not fixed yet. -/
def firstUnfixed (doms : Array DomC) (n : Nat) : Option Nat :=
  (List.range n).find? fun s => !(doms.getD s DomC.empty).isFixed

/-- Branch a slot to a Boolean singleton if that value is in the initial
domain. -/
def branchDoms (p : CompiledProblem DomConstraint) (doms : Array DomC)
    (s : Nat) (v : Bool) : Option (Array DomC) :=
  if Dom.memBool (p.domains.getD s Dom.empty) (.bool v) then
    some (doms.set! s (DomC.bool (if v then 2 else 1)))
  else none

/-- Depth-first search with propagation to a local fixpoint.  The count is
the number of branch decisions taken on the successful path (0 on a
conflict). -/
def dfsDecisions (p : CompiledProblem DomConstraint)
    (props : List (PropV2 p ({} : LitTable))) (view : EngineView) :
    Nat → Bool × Nat
  | 0 => (false, 0)
  | fuel + 1 =>
      let r := runLoop props view 32
      if r.conflict then (false, 0)
      else
        match firstUnfixed r.doms p.domains.length with
        | none => (accepts p (assignmentOfDoms r.doms), 0)
        | some s =>
            match branchDoms p r.doms s true with
            | some ds =>
                let (sat, k) := dfsDecisions p props { view with doms := ds } fuel
                if sat then (true, k + 1)
                else
                  match branchDoms p r.doms s false with
                  | some ds2 =>
                      let (sat2, k2) := dfsDecisions p props { view with doms := ds2 } fuel
                      (sat2, k2 + 1)
                  | none => (false, 0)
            | none =>
                match branchDoms p r.doms s false with
                | some ds2 =>
                    let (sat2, k2) := dfsDecisions p props { view with doms := ds2 } fuel
                    (sat2, k2 + 1)
                | none => (false, 0)

def pSynAnd : CompiledProblem DomConstraint :=
  mkProblem [domB, domB, domBT] [.boolAndSlot 0 1 2]

def pSynOr : CompiledProblem DomConstraint :=
  mkProblem [domB, domB, domBF] [.boolOrSlot 0 1 2]

theorem hreadySynAnd : initReady pSynAnd (convInit pSynAnd.domains) = true := by
  simp [initReady, pSynAnd, mkProblem, convInit, domB, domBT, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadySynOr : initReady pSynOr (convInit pSynOr.domains) = true := by
  simp [initReady, pSynOr, mkProblem, convInit, domB, domBF, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

/-- Run the dedicated and generic tables on one synthetic instance and
compare the satisfiability verdict and the number of branch decisions. -/
def checkSynthetic (label : String) (p : CompiledProblem DomConstraint)
    (hready : initReady p (convInit p.domains) = true) (expectDedicated : Bool) :
    IO Unit := do
  let T : LitTable := {}
  let init := convInit p.domains
  let hinit := initReady_spec hready
  let dedicated := propsOfTest p T init hinit
  let generic := propsOfLeaf p T init hinit
  let view : EngineView := { doms := init, level := 0 }
  let (rdSat, rdDec) := dfsDecisions p dedicated.toList view 64
  let (rgSat, rgDec) := dfsDecisions p generic.toList view 64
  check s!"{label}: sat verdict dedicated={rdSat} generic={rgSat}" (rdSat == rgSat)
  check s!"{label}: expected sat={expectDedicated}" (rdSat == expectDedicated)
  check s!"{label}: dedicated decisions {rdDec} < generic {rgDec}" (rdDec < rgDec)
  IO.println s!"  synthetic {label}: dedicated decisions={rdDec} \
generic decisions={rgDec} sat={rdSat}"

def checkDifferentials : IO Unit := do
  checkFixedAgreement "not-good" pFixNotGood hreadyFixNotGood
  checkFixedAgreement "not-bad" pFixNotBad hreadyFixNotBad
  checkFixedAgreement "and-bad" pFixAndBad hreadyFixAndBad
  checkFixedAgreement "or-bad" pFixOrBad hreadyFixOrBad
  checkFixedAgreement "eq-bad" pFixEqBad hreadyFixEqBad
  checkFixedAgreement "array-bad" pFixArrBad hreadyFixArrBad
  checkSynthetic "and-forcing" pSynAnd hreadySynAnd true
  checkSynthetic "or-forcing" pSynOr hreadySynOr true

end Tests.Engine.BoolExtTest

open Tests.Engine.BoolExtTest in
def main : IO UInt32 := do
  checkNotForward
  checkNotBackward
  checkNotConflict
  checkNotFix
  checkAndKTrue
  checkAndKFalseConflict
  checkAndILink
  checkAndIFalse
  checkAndConflict
  checkAndSupport
  checkAndFix
  checkOrKFalse
  checkOrKTrueConflict
  checkOrILink
  checkOrITrue
  checkOrConflict
  checkOrFix
  checkEqForward
  checkEqBackward
  checkEqConflict
  checkEqFix
  checkArrEmpty
  checkArrAllTrue
  checkArrFalseSource
  checkArrLast
  checkArrConflict
  checkArrFix
  checkArrMalformed
  checkMalformed
  checkDifferentials
  IO.println "BoolExtTest: OK"
  return 0
