/-
Runtime tests for the dedicated binary order / Boolean-integer bridge
propagators in `LeanFzn/Engine/Props/Order.lean`.

Run with:
  lake env lean --run Tests/Engine/OrderTest.lean

Coverage: constant bounds, `le`/`lt`, `eq` (including Boolean and
Boolean/integer clashes), `bool2int`, the three reifications in both
polarities plus `r`-pruning and inconsistent-`r` conflicts, runtime
entailment over the accepted assignments, malformed inputs, and a local
differential table comparing the dedicated builders against
`Search.propsOf` (generic checker) to a small propagation fixpoint.
-/
import LeanFzn.Engine.Props.Order
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.OrderTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"OrderTest FAIL: {msg}"
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

/-- Convert domains the way the engine does; used to build `eq`'s `init`. -/
def convInit (ds : List Dom) : Array DomC :=
  ds.toArray.map fun d => (DomC.ofDom? d).getD DomC.empty

/-! ## Inspecting `PropOut` -/

def isFix {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Bool
  | .fix => true
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

/-- One expected single-literal prune, with exact reason clause. -/
def checkPrune (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) (out : PropOut p ({} : LitTable))
    (lit : Literal) (reason : Clause) : IO Unit :=
  match pruneLits? out, pruneClauses? out with
  | some lits, some [c] => do
      check s!"{label}: unit {repr lits} expected [{repr lit}]" (lits == [lit])
      check s!"{label}: reason {repr c} expected {repr reason}" (c == reason)
      checkLitNone label view lit
      checkAllFalse label view (reason.filter (fun l => l != lit))
      checkClauseEntailedRuntime label p reason
  | _, _ => fail s!"{label}: expected one prune, got another output kind"

def checkFix {p : CompiledProblem DomConstraint} {T : LitTable}
    (label : String) (out : PropOut p T) : IO Unit :=
  check s!"{label}: expected .fix" (isFix out)

/-! ## Concrete domains -/

def dom0_10 : Dom := ⟨.holes 0 10 []⟩
def dom0_5 : Dom := ⟨.holes 0 5 []⟩
def dom5_10 : Dom := ⟨.holes 5 10 []⟩
def dom3_8 : Dom := ⟨.holes 3 8 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩

/-- A two-slot view helper. -/
def view2 (d0 d1 : DomC) : EngineView := { doms := #[d0, d1], level := 0 }

/-- A three-slot view helper. -/
def view3 (d0 d1 d2 : DomC) : EngineView := { doms := #[d0, d1, d2], level := 0 }

/-- A one-slot view helper. -/
def view1 (d0 : DomC) : EngineView := { doms := #[d0], level := 0 }

/-! ## 1. Constant bounds -/

def pLeConstHi : CompiledProblem DomConstraint :=
  mkProblem [dom0_10] [.leConstHi 0 5]

theorem hmemLeConstHi : DomConstraint.leConstHi 0 5 ∈ pLeConstHi.constraints := by
  simp [pLeConstHi, mkProblem]

def outLeConstHi (view : EngineView) : PropOut pLeConstHi ({} : LitTable) :=
  (leConstHiPropWith pLeConstHi ({} : LitTable) 0 5 hmemLeConstHi).run view

def checkLeConstHi : IO Unit := do
  checkPrune "leConstHi prune" pLeConstHi (view1 (DomC.bounds 0 10))
    (outLeConstHi (view1 (DomC.bounds 0 10))) (posLe 0 5) [posLe 0 5]
  checkConflict "leConstHi conflict" pLeConstHi (view1 (DomC.bounds 7 10))
    (outLeConstHi (view1 (DomC.bounds 7 10))) [posLe 0 5]

def pLeConstLo : CompiledProblem DomConstraint :=
  mkProblem [dom0_10] [.leConstLo 0 5]

theorem hmemLeConstLo : DomConstraint.leConstLo 0 5 ∈ pLeConstLo.constraints := by
  simp [pLeConstLo, mkProblem]

def outLeConstLo (view : EngineView) : PropOut pLeConstLo ({} : LitTable) :=
  (leConstLoPropWith pLeConstLo ({} : LitTable) 0 5 hmemLeConstLo).run view

def checkLeConstLo : IO Unit := do
  checkPrune "leConstLo prune" pLeConstLo (view1 (DomC.bounds 0 10))
    (outLeConstLo (view1 (DomC.bounds 0 10))) (negLe 0 4) [negLe 0 4]
  checkConflict "leConstLo conflict" pLeConstLo (view1 (DomC.bounds 0 3))
    (outLeConstLo (view1 (DomC.bounds 0 3))) [negLe 0 4]

def pLtConstHi : CompiledProblem DomConstraint :=
  mkProblem [dom0_10] [.ltConstHi 0 5]

theorem hmemLtConstHi : DomConstraint.ltConstHi 0 5 ∈ pLtConstHi.constraints := by
  simp [pLtConstHi, mkProblem]

def outLtConstHi (view : EngineView) : PropOut pLtConstHi ({} : LitTable) :=
  (ltConstHiPropWith pLtConstHi ({} : LitTable) 0 5 hmemLtConstHi).run view

def checkLtConstHi : IO Unit := do
  checkPrune "ltConstHi prune" pLtConstHi (view1 (DomC.bounds 0 10))
    (outLtConstHi (view1 (DomC.bounds 0 10))) (posLe 0 4) [posLe 0 4]
  checkConflict "ltConstHi conflict" pLtConstHi (view1 (DomC.bounds 6 10))
    (outLtConstHi (view1 (DomC.bounds 6 10))) [posLe 0 4]

def pLtConstLo : CompiledProblem DomConstraint :=
  mkProblem [dom0_10] [.ltConstLo 0 5]

theorem hmemLtConstLo : DomConstraint.ltConstLo 0 5 ∈ pLtConstLo.constraints := by
  simp [pLtConstLo, mkProblem]

def outLtConstLo (view : EngineView) : PropOut pLtConstLo ({} : LitTable) :=
  (ltConstLoPropWith pLtConstLo ({} : LitTable) 0 5 hmemLtConstLo).run view

def checkLtConstLo : IO Unit := do
  checkPrune "ltConstLo prune" pLtConstLo (view1 (DomC.bounds 0 10))
    (outLtConstLo (view1 (DomC.bounds 0 10))) (negLe 0 5) [negLe 0 5]
  checkConflict "ltConstLo conflict" pLtConstLo (view1 (DomC.bounds 0 5))
    (outLtConstLo (view1 (DomC.bounds 0 5))) [negLe 0 5]

/-! ## 2. `leSlot` / `ltSlot` / `eqSlot` -/

def pLe : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.leSlot 0 1]

theorem hmemLe : DomConstraint.leSlot 0 1 ∈ pLe.constraints := by
  simp [pLe, mkProblem]

def outLe (view : EngineView) : PropOut pLe ({} : LitTable) :=
  (lePropWith pLe ({} : LitTable) 0 1 hmemLe).run view

def checkLe : IO Unit := do
  checkConflict "le conflict" pLe (view2 (DomC.bounds 5 10) (DomC.bounds 0 4))
    (outLe (view2 (DomC.bounds 5 10) (DomC.bounds 0 4)))
    [posLe 0 4, negLe 1 4]
  checkPrune "le i-upper" pLe (view2 (DomC.bounds 0 10) (DomC.bounds 0 4))
    (outLe (view2 (DomC.bounds 0 10) (DomC.bounds 0 4)))
    (posLe 0 4) [posLe 0 4, negLe 1 4]
  checkPrune "le j-lower" pLe (view2 (DomC.bounds 3 10) (DomC.bounds 0 10))
    (outLe (view2 (DomC.bounds 3 10) (DomC.bounds 0 10)))
    (negLe 1 2) [negLe 1 2, posLe 0 2]
  checkFix "le fixpoint" (outLe (view2 (DomC.bounds 0 2) (DomC.bounds 1 3)))

def pLt : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.ltSlot 0 1]

theorem hmemLt : DomConstraint.ltSlot 0 1 ∈ pLt.constraints := by
  simp [pLt, mkProblem]

def outLt (view : EngineView) : PropOut pLt ({} : LitTable) :=
  (ltPropWith pLt ({} : LitTable) 0 1 hmemLt).run view

def checkLt : IO Unit := do
  checkConflict "lt conflict" pLt (view2 (DomC.bounds 5 10) (DomC.bounds 0 5))
    (outLt (view2 (DomC.bounds 5 10) (DomC.bounds 0 5)))
    [posLe 0 4, negLe 1 5]
  checkPrune "lt i-upper" pLt (view2 (DomC.bounds 0 10) (DomC.bounds 0 4))
    (outLt (view2 (DomC.bounds 0 10) (DomC.bounds 0 4)))
    (posLe 0 3) [posLe 0 3, negLe 1 4]
  checkPrune "lt j-lower" pLt (view2 (DomC.bounds 3 6) (DomC.bounds 2 10))
    (outLt (view2 (DomC.bounds 3 6) (DomC.bounds 2 10)))
    (negLe 1 3) [negLe 1 3, posLe 0 2]
  checkFix "lt fixpoint" (outLt (view2 (DomC.bounds 0 2) (DomC.bounds 3 5)))

def pEq : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.eqSlot 0 1]

theorem hmemEq : DomConstraint.eqSlot 0 1 ∈ pEq.constraints := by
  simp [pEq, mkProblem]

def initEq : Array DomC := convInit pEq.domains

theorem hinitEq : ∀ s ∈ dcSlotsFull (.eqSlot 0 1),
    DomC.ofDom? (pEq.domains.getD s Dom.empty) = some (initEq.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;>
    simp [pEq, mkProblem, initEq, convInit, dom0_10, DomC.ofDom?]

def outEq (view : EngineView) : PropOut pEq ({} : LitTable) :=
  (eqPropWith pEq ({} : LitTable) initEq 0 1 hinitEq hmemEq).run view

def checkEq : IO Unit := do
  checkConflict "eq fixed/fixed unequal" pEq
    (view2 (DomC.bounds 0 0) (DomC.bounds 1 1))
    (outEq (view2 (DomC.bounds 0 0) (DomC.bounds 1 1)))
    [neLit 0 (.int 0), neLit 1 (.int 1)]
  checkFix "eq fixed/fixed equal" (outEq (view2 (DomC.bounds 2 2) (DomC.bounds 2 2)))
  checkPrune "eq fixed/interval" pEq
    (view2 (DomC.bounds 3 3) (DomC.bounds 0 10))
    (outEq (view2 (DomC.bounds 3 3) (DomC.bounds 0 10)))
    (eqLit 1 (.int 3)) [neLit 0 (.int 3), eqLit 1 (.int 3)]
  checkPrune "eq interval/fixed" pEq
    (view2 (DomC.bounds 0 10) (DomC.bounds 4 4))
    (outEq (view2 (DomC.bounds 0 10) (DomC.bounds 4 4)))
    (eqLit 0 (.int 4)) [eqLit 0 (.int 4), neLit 1 (.int 4)]
  checkPrune "eq i-upper" pEq (view2 (DomC.bounds 0 10) (DomC.bounds 0 4))
    (outEq (view2 (DomC.bounds 0 10) (DomC.bounds 0 4)))
    (posLe 0 4) [posLe 0 4, negLe 1 4]
  checkPrune "eq j-lower" pEq (view2 (DomC.bounds 3 10) (DomC.bounds 0 10))
    (outEq (view2 (DomC.bounds 3 10) (DomC.bounds 0 10)))
    (negLe 1 2) [negLe 1 2, posLe 0 2]
  checkPrune "eq i-lower" pEq (view2 (DomC.bounds 0 5) (DomC.bounds 3 10))
    (outEq (view2 (DomC.bounds 0 5) (DomC.bounds 3 10)))
    (negLe 0 2) [negLe 0 2, posLe 1 2]
  checkPrune "eq j-upper" pEq (view2 (DomC.bounds 3 7) (DomC.bounds 3 10))
    (outEq (view2 (DomC.bounds 3 7) (DomC.bounds 3 10)))
    (posLe 1 7) [posLe 1 7, negLe 0 7]
  checkFix "eq disjoint intervals is a no-op"
    (outEq (view2 (DomC.bounds 0 2) (DomC.bounds 3 5)))
  checkFix "eq value outside init is a no-op"
    (outEq (view2 (DomC.bounds 100 100) (DomC.bounds 0 0)))

def pEqBool : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool] [.eqSlot 0 1]

theorem hmemEqBool : DomConstraint.eqSlot 0 1 ∈ pEqBool.constraints := by
  simp [pEqBool, mkProblem]

def initEqBool : Array DomC := convInit pEqBool.domains

theorem hinitEqBool : ∀ s ∈ dcSlotsFull (.eqSlot 0 1),
    DomC.ofDom? (pEqBool.domains.getD s Dom.empty) = some (initEqBool.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;>
    simp [pEqBool, mkProblem, initEqBool, convInit, domBool, DomC.ofDom?, boolFold]

def outEqBool (view : EngineView) : PropOut pEqBool ({} : LitTable) :=
  (eqPropWith pEqBool ({} : LitTable) initEqBool 0 1 hinitEqBool hmemEqBool).run view

def pEqMixed : CompiledProblem DomConstraint :=
  mkProblem [domBool, dom0_10] [.eqSlot 0 1]

theorem hmemEqMixed : DomConstraint.eqSlot 0 1 ∈ pEqMixed.constraints := by
  simp [pEqMixed, mkProblem]

def initEqMixed : Array DomC := convInit pEqMixed.domains

theorem hinitEqMixed : ∀ s ∈ dcSlotsFull (.eqSlot 0 1),
    DomC.ofDom? (pEqMixed.domains.getD s Dom.empty) = some (initEqMixed.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;>
    simp [pEqMixed, mkProblem, initEqMixed, convInit, dom0_10, domBool, DomC.ofDom?, boolFold]

def outEqMixed (view : EngineView) : PropOut pEqMixed ({} : LitTable) :=
  (eqPropWith pEqMixed ({} : LitTable) initEqMixed 0 1 hinitEqMixed hmemEqMixed).run view

def checkEqBool : IO Unit := do
  checkPrune "eq bool fixed/other" pEqBool
    (view2 (DomC.bool 2) (DomC.bool 3))
    (outEqBool (view2 (DomC.bool 2) (DomC.bool 3)))
    (eqLit 1 (.bool true)) [neLit 0 (.bool true), eqLit 1 (.bool true)]
  checkFix "eq bool fixed/fixed equal"
    (outEqBool (view2 (DomC.bool 2) (DomC.bool 2)))
  checkConflict "eq bool/int clash" pEqMixed
    (view2 (DomC.bool 2) (DomC.bounds 1 1))
    (outEqMixed (view2 (DomC.bool 2) (DomC.bounds 1 1)))
    [neLit 0 (.bool true), neLit 1 (.int 1)]

/-! ## 3. `bool2int` -/

def pB2I : CompiledProblem DomConstraint :=
  mkProblem [domBool, dom0_10] [.bool2intSlot 0 1]

theorem hmemB2I : DomConstraint.bool2intSlot 0 1 ∈ pB2I.constraints := by
  simp [pB2I, mkProblem]

def outB2I (view : EngineView) : PropOut pB2I ({} : LitTable) :=
  (bool2intPropWith pB2I ({} : LitTable) 0 1 hmemB2I).run view

def checkBool2Int : IO Unit := do
  checkPrune "bool2int i=true prune k=1" pB2I
    (view2 (DomC.bool 2) (DomC.bounds 0 10))
    (outB2I (view2 (DomC.bool 2) (DomC.bounds 0 10)))
    (eqLit 1 (.int 1)) [neLit 0 (.bool true), eqLit 1 (.int 1)]
  checkConflict "bool2int i=true conflict k≠1" pB2I
    (view2 (DomC.bool 2) (DomC.bounds 2 10))
    (outB2I (view2 (DomC.bool 2) (DomC.bounds 2 10)))
    [neLit 0 (.bool true), eqLit 1 (.int 1)]
  checkPrune "bool2int i=false prune k=0" pB2I
    (view2 (DomC.bool 1) (DomC.bounds 0 10))
    (outB2I (view2 (DomC.bool 1) (DomC.bounds 0 10)))
    (eqLit 1 (.int 0)) [neLit 0 (.bool false), eqLit 1 (.int 0)]
  checkPrune "bool2int k=1 prune i=true" pB2I
    (view2 (DomC.bool 3) (DomC.bounds 1 1))
    (outB2I (view2 (DomC.bool 3) (DomC.bounds 1 1)))
    (eqLit 0 (.bool true)) [neLit 1 (.int 1), eqLit 0 (.bool true)]
  checkPrune "bool2int k=0 prune i=false" pB2I
    (view2 (DomC.bool 3) (DomC.bounds 0 0))
    (outB2I (view2 (DomC.bool 3) (DomC.bounds 0 0)))
    (eqLit 0 (.bool false)) [neLit 1 (.int 0), eqLit 0 (.bool false)]
  checkConflict "bool2int k=2 conflict" pB2I
    (view2 (DomC.bool 3) (DomC.bounds 2 2))
    (outB2I (view2 (DomC.bool 3) (DomC.bounds 2 2)))
    [negNe 1 0, negNe 1 1]
  checkConflict "bool2int k∉{0,1} conflict" pB2I
    (view2 (DomC.bool 3) (DomC.bounds 2 10))
    (outB2I (view2 (DomC.bool 3) (DomC.bounds 2 10)))
    [negNe 1 0, negNe 1 1]
  checkFix "bool2int consistent i=true,k=1"
    (outB2I (view2 (DomC.bool 2) (DomC.bounds 1 1)))
  checkFix "bool2int consistent i=false,k=0"
    (outB2I (view2 (DomC.bool 1) (DomC.bounds 0 0)))

/-! ## 4. Reifications -/

def pLeReif : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.leReifSlot 0 1 2]

theorem hmemLeReif : DomConstraint.leReifSlot 0 1 2 ∈ pLeReif.constraints := by
  simp [pLeReif, mkProblem]

def outLeReif (view : EngineView) : PropOut pLeReif ({} : LitTable) :=
  (leReifPropWith pLeReif ({} : LitTable) 0 1 2 hmemLeReif).run view

def checkLeReif : IO Unit := do
  checkConflict "leReif r=true conflict" pLeReif
    (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 2))
    (outLeReif (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 2)))
    ([posLe 0 4, negLe 1 4] ++ [neLit 2 (.bool true)])
  checkPrune "leReif r=true i-upper" pLeReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 2))
    (outLeReif (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 2)))
    (posLe 0 4) ([posLe 0 4, negLe 1 4] ++ [neLit 2 (.bool true)])
  checkPrune "leReif r=true j-lower" pLeReif
    (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 2))
    (outLeReif (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 2)))
    (negLe 1 2) ([negLe 1 2, posLe 0 2] ++ [neLit 2 (.bool true)])
  checkConflict "leReif r=false conflict" pLeReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 2 5) (DomC.bool 1))
    (outLeReif (view3 (DomC.bounds 0 2) (DomC.bounds 2 5) (DomC.bool 1)))
    ([posLe 1 1, negLe 0 2] ++ [neLit 2 (.bool false)])
  checkPrune "leReif r=false j-upper" pLeReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 0 10) (DomC.bool 1))
    (outLeReif (view3 (DomC.bounds 0 2) (DomC.bounds 0 10) (DomC.bool 1)))
    (posLe 1 1) ([posLe 1 1, negLe 0 2] ++ [neLit 2 (.bool false)])
  checkPrune "leReif r=false i-lower" pLeReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 3 8) (DomC.bool 1))
    (outLeReif (view3 (DomC.bounds 0 10) (DomC.bounds 3 8) (DomC.bool 1)))
    (negLe 0 3) ([negLe 0 3, posLe 1 2] ++ [neLit 2 (.bool false)])
  checkPrune "leReif prune r=true" pLeReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3))
    (outLeReif (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3)))
    (posBool 2 true) [posBool 2 true, negLe 0 2, posLe 1 1]
  checkPrune "leReif prune r=false" pLeReif
    (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 3))
    (outLeReif (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 3)))
    (posBool 2 false) [posBool 2 false, posLe 0 4, negLe 1 4]

def pEqReif : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.eqReifSlot 0 1 2]

theorem hmemEqReif : DomConstraint.eqReifSlot 0 1 2 ∈ pEqReif.constraints := by
  simp [pEqReif, mkProblem]

def outEqReif (view : EngineView) : PropOut pEqReif ({} : LitTable) :=
  (eqReifPropWith pEqReif ({} : LitTable) 0 1 2 hmemEqReif).run view

def checkEqReif : IO Unit := do
  checkConflict "eqReif r=true conflict ij" pEqReif
    (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 5 10) (DomC.bounds 0 4) (DomC.bool 2)))
    ([posLe 0 4, negLe 1 4] ++ [neLit 2 (.bool true)])
  checkConflict "eqReif r=true conflict ji" pEqReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 2)))
    ([posLe 1 2, negLe 0 2] ++ [neLit 2 (.bool true)])
  checkPrune "eqReif r=true i-upper" pEqReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 2)))
    (posLe 0 4) ([posLe 0 4, negLe 1 4] ++ [neLit 2 (.bool true)])
  checkPrune "eqReif r=true j-lower" pEqReif
    (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 2)))
    (negLe 1 2) ([negLe 1 2, posLe 0 2] ++ [neLit 2 (.bool true)])
  checkPrune "eqReif r=true i-lower" pEqReif
    (view3 (DomC.bounds 0 5) (DomC.bounds 3 10) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 0 5) (DomC.bounds 3 10) (DomC.bool 2)))
    (negLe 0 2) ([negLe 0 2, posLe 1 2] ++ [neLit 2 (.bool true)])
  checkPrune "eqReif r=true j-upper" pEqReif
    (view3 (DomC.bounds 3 7) (DomC.bounds 3 10) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 3 7) (DomC.bounds 3 10) (DomC.bool 2)))
    (posLe 1 7) ([posLe 1 7, negLe 0 7] ++ [neLit 2 (.bool true)])
  checkConflict "eqReif r=false equal fixed conflict" pEqReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 1))
    (outEqReif (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 1)))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool false)])
  checkPrune "eqReif r=false prune j" pEqReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 0 10) (DomC.bool 1))
    (outEqReif (view3 (DomC.bounds 2 2) (DomC.bounds 0 10) (DomC.bool 1)))
    (neLit 1 (.int 2))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool false)])
  checkPrune "eqReif r=false prune i" pEqReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 2 2) (DomC.bool 1))
    (outEqReif (view3 (DomC.bounds 0 10) (DomC.bounds 2 2) (DomC.bool 1)))
    (neLit 0 (.int 2))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool false)])
  checkPrune "eqReif decide r=true" pEqReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 3))
    (outEqReif (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 3)))
    (posBool 2 true) [posBool 2 true, neLit 0 (.int 2), neLit 1 (.int 2)]
  checkPrune "eqReif decide r=false" pEqReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 3 3) (DomC.bool 3))
    (outEqReif (view3 (DomC.bounds 2 2) (DomC.bounds 3 3) (DomC.bool 3)))
    (posBool 2 false) [posBool 2 false, neLit 0 (.int 2), neLit 1 (.int 3)]
  checkPrune "eqReif disjoint prune r=false" pEqReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3))
    (outEqReif (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3)))
    (posBool 2 false) [posBool 2 false, negLe 0 2, posLe 1 2]
  checkConflict "eqReif inconsistent r=true" pEqReif
    (view3 (DomC.bounds 0 0) (DomC.bounds 1 1) (DomC.bool 2))
    (outEqReif (view3 (DomC.bounds 0 0) (DomC.bounds 1 1) (DomC.bool 2)))
    ([posLe 1 0, negLe 0 0] ++ [neLit 2 (.bool true)])

def pNeReif : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.neReifSlot 0 1 2]

theorem hmemNeReif : DomConstraint.neReifSlot 0 1 2 ∈ pNeReif.constraints := by
  simp [pNeReif, mkProblem]

def outNeReif (view : EngineView) : PropOut pNeReif ({} : LitTable) :=
  (neReifPropWith pNeReif ({} : LitTable) 0 1 2 hmemNeReif).run view

def checkNeReif : IO Unit := do
  checkConflict "neReif r=true equal fixed conflict" pNeReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 2))
    (outNeReif (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 2)))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool true)])
  checkPrune "neReif r=true prune j" pNeReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 0 10) (DomC.bool 2))
    (outNeReif (view3 (DomC.bounds 2 2) (DomC.bounds 0 10) (DomC.bool 2)))
    (neLit 1 (.int 2))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool true)])
  checkPrune "neReif r=true prune i" pNeReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 2 2) (DomC.bool 2))
    (outNeReif (view3 (DomC.bounds 0 10) (DomC.bounds 2 2) (DomC.bool 2)))
    (neLit 0 (.int 2))
    ([neLit 0 (.int 2), neLit 1 (.int 2)] ++ [neLit 2 (.bool true)])
  checkConflict "neReif r=false disjoint conflict" pNeReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 1))
    (outNeReif (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 1)))
    ([posLe 1 2, negLe 0 2] ++ [neLit 2 (.bool false)])
  checkPrune "neReif r=false i-upper" pNeReif
    (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 1))
    (outNeReif (view3 (DomC.bounds 0 10) (DomC.bounds 0 4) (DomC.bool 1)))
    (posLe 0 4) ([posLe 0 4, negLe 1 4] ++ [neLit 2 (.bool false)])
  checkPrune "neReif r=false j-lower" pNeReif
    (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 1))
    (outNeReif (view3 (DomC.bounds 3 10) (DomC.bounds 0 10) (DomC.bool 1)))
    (negLe 1 2) ([negLe 1 2, posLe 0 2] ++ [neLit 2 (.bool false)])
  checkPrune "neReif decide r=false" pNeReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 3))
    (outNeReif (view3 (DomC.bounds 2 2) (DomC.bounds 2 2) (DomC.bool 3)))
    (posBool 2 false) [posBool 2 false, neLit 0 (.int 2), neLit 1 (.int 2)]
  checkPrune "neReif decide r=true" pNeReif
    (view3 (DomC.bounds 2 2) (DomC.bounds 3 3) (DomC.bool 3))
    (outNeReif (view3 (DomC.bounds 2 2) (DomC.bounds 3 3) (DomC.bool 3)))
    (posBool 2 true) [posBool 2 true, neLit 0 (.int 2), neLit 1 (.int 3)]
  checkPrune "neReif disjoint prune r=true" pNeReif
    (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3))
    (outNeReif (view3 (DomC.bounds 0 2) (DomC.bounds 3 5) (DomC.bool 3)))
    (posBool 2 true) [posBool 2 true, negLe 0 2, posLe 1 2]

/-! ## 6. Malformed inputs and missing bounds -/

def pBadSlot : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.leSlot 5 6]

theorem hmemBadSlot : DomConstraint.leSlot 5 6 ∈ pBadSlot.constraints := by
  simp [pBadSlot, mkProblem]

def outBadSlot : PropOut pBadSlot ({} : LitTable) :=
  (lePropWith pBadSlot ({} : LitTable) 5 6 hmemBadSlot).run
    (view2 (DomC.bounds 0 10) (DomC.bounds 0 10))

def checkMalformed : IO Unit := do
  -- Missing bounds (empty interval representation).
  checkFix "le missing bounds" (outLe (view2 (DomC.bounds 1 0) (DomC.bounds 0 10)))
  checkFix "lt missing bounds" (outLt (view2 (DomC.bounds 0 10) (DomC.bounds 1 0)))
  checkFix "eq missing bounds" (outEq (view2 (DomC.bounds 1 0) (DomC.bounds 0 10)))
  checkFix "bool2int missing bounds"
    (outB2I (view2 (DomC.bool 3) (DomC.bounds 1 0)))
  checkFix "leReif missing bounds"
    (outLeReif (view3 (DomC.bounds 1 0) (DomC.bounds 0 10) (DomC.bool 2)))
  -- Non-compact / empty bitset gives no bounds.
  checkFix "le non-compact bitset"
    (outLe (view2 (DomC.bitset 0 #[0]) (DomC.bounds 0 10)))
  checkFix "eq non-compact bitset"
    (outEq (view2 (DomC.bitset 0 #[0]) (DomC.bounds 0 10)))
  -- Reification slot with a malformed (integer) kind: no claim.
  checkFix "leReif malformed r kind"
    (outLeReif (view3 (DomC.bounds 0 10) (DomC.bounds 0 10) (DomC.bounds 0 0)))
  -- Out-of-range slots read as empty domains: no claim.
  checkFix "le out-of-range slot" outBadSlot

/-! ## 7. Local differential: dedicated builders vs `Search.propsOf` -/

/-- Test-local adapters: dedicated order builders, generic checker for the
rest.  This mirrors `Search.propsOf` for the constraint families owned by
`Order.lean`. -/
def propsOfTest (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .eqSlot i j =>
        eqPropWith p T init i j
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leSlot i j =>
        lePropWith p T i j (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltSlot i j =>
        ltPropWith p T i j (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstHi i c =>
        leConstHiPropWith p T i c (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leConstLo i c =>
        leConstLoPropWith p T i c (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstHi i c =>
        ltConstHiPropWith p T i c (by simpa [hx] using List.mem_toArray.mp x.2)
    | .ltConstLo i c =>
        ltConstLoPropWith p T i c (by simpa [hx] using List.mem_toArray.mp x.2)
    | .bool2intSlot i k =>
        bool2intPropWith p T i k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .eqReifSlot i j r =>
        eqReifPropWith p T i j r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .leReifSlot i j r =>
        leReifPropWith p T i j r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .neReifSlot i j r =>
        neReifPropWith p T i j r (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- Apply one propagator batch of prunings to the domain array. -/
def applyPrunes (doms : Array DomC) (ps : Array (PLit × EClause p T)) : Array DomC :=
  ps.foldl (fun ds q =>
    let s := atomSlot q.1.lit.atom
    ds.set! s ((ds.getD s DomC.empty).applyLit q.1.lit)) doms

/-- One sweep over all propagators, applying prunings in place.
Returns `none` on conflict, otherwise the new domains, the number of
prunes applied and whether any domain changed. -/
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

/-- Sweep to a local fixpoint with the given fuel (one unit per sweep). -/
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

/-- Differential verdict: the conflict status at the local fixpoint.  The
generic checker is a sound but deliberately weak reference (it never
prunes), so propagation strength is reported separately below rather than
asserted equal. -/
def sameDiff (a b : DiffResult) : Bool :=
  a.conflict == b.conflict

/-- Run both propagator tables from the initial box to a local fixpoint
and print the fuel/prune counts. -/
def checkDifferential (label : String) (p : CompiledProblem DomConstraint)
    (hready : initReady p (convInit p.domains) = true) : IO Unit := do
  let T : LitTable := {}
  let init := convInit p.domains
  let hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) :=
    initReady_spec hready
  let dedicated := propsOfTest p T init hinit
  let generic := propsOf p T init hinit
  let view : EngineView := { doms := init, level := 0 }
  let rd := runLoop dedicated.toList view 64
  let rg := runLoop generic.toList view 64
  check s!"{label}: differential verdict {repr rd} vs {repr rg}" (sameDiff rd rg)
  IO.println s!"  differential {label}: dedicated fuel={rd.fuel} prunes={rd.prunes} \
conflict={rd.conflict} | generic fuel={rg.fuel} prunes={rg.prunes} conflict={rg.conflict}"

def pDiffLe : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom5_10] [.leSlot 0 1]

def pDiffEq : CompiledProblem DomConstraint :=
  mkProblem [dom0_5, dom3_8] [.eqSlot 0 1]

def pDiffB2I : CompiledProblem DomConstraint :=
  mkProblem [domBool, ⟨.holes 0 3 []⟩] [.bool2intSlot 0 1]

def pDiffLeReif : CompiledProblem DomConstraint :=
  mkProblem [dom0_5, dom5_10, domBool] [.leReifSlot 0 1 2]

def pDiffLt : CompiledProblem DomConstraint :=
  mkProblem [dom0_5, dom3_8] [.ltSlot 0 1]

/-- Fixed unsatisfiable instances: the generic checker also produces a
conflict here, so the verdict comparison is non-trivial. -/
def pDiffLeBad : CompiledProblem DomConstraint :=
  mkProblem [⟨.holes 8 8 []⟩, ⟨.holes 7 7 []⟩] [.leSlot 0 1]

def pDiffEqBad : CompiledProblem DomConstraint :=
  mkProblem [⟨.holes 2 2 []⟩, ⟨.holes 3 3 []⟩] [.eqSlot 0 1]

def domBoolTrue : Dom := ⟨.general [.bool true]⟩
def domZero : Dom := ⟨.holes 0 0 []⟩

def pDiffB2IBad : CompiledProblem DomConstraint :=
  mkProblem [domBoolTrue, domZero] [.bool2intSlot 0 1]

theorem hreadyDiffLeBad : initReady pDiffLeBad (convInit pDiffLeBad.domains) = true := by
  simp [initReady, pDiffLeBad, mkProblem, convInit, dcSlotsFull, slotReadyB, DomC.ofDom?]

theorem hreadyDiffEqBad : initReady pDiffEqBad (convInit pDiffEqBad.domains) = true := by
  simp [initReady, pDiffEqBad, mkProblem, convInit, dcSlotsFull, slotReadyB, DomC.ofDom?]

theorem hreadyDiffB2IBad : initReady pDiffB2IBad (convInit pDiffB2IBad.domains) = true := by
  simp [initReady, pDiffB2IBad, mkProblem, convInit, domBoolTrue, domZero, DomC.ofDom?,
    boolFold, dcSlotsFull, slotReadyB]

theorem hreadyDiffLe : initReady pDiffLe (convInit pDiffLe.domains) = true := by
  simp [initReady, pDiffLe, mkProblem, convInit, dom0_10, dom5_10, dcSlotsFull,
    slotReadyB, DomC.ofDom?]

theorem hreadyDiffEq : initReady pDiffEq (convInit pDiffEq.domains) = true := by
  simp [initReady, pDiffEq, mkProblem, convInit, dom0_5, dom3_8, dcSlotsFull,
    slotReadyB, DomC.ofDom?]

theorem hreadyDiffB2I : initReady pDiffB2I (convInit pDiffB2I.domains) = true := by
  simp [initReady, pDiffB2I, mkProblem, convInit, domBool, DomC.ofDom?, boolFold,
    dcSlotsFull, slotReadyB]

theorem hreadyDiffLeReif : initReady pDiffLeReif (convInit pDiffLeReif.domains) = true := by
  simp [initReady, pDiffLeReif, mkProblem, convInit, dom0_5, dom5_10, domBool,
    DomC.ofDom?, boolFold, dcSlotsFull, slotReadyB]

theorem hreadyDiffLt : initReady pDiffLt (convInit pDiffLt.domains) = true := by
  simp [initReady, pDiffLt, mkProblem, convInit, dom0_5, dom3_8, dcSlotsFull,
    slotReadyB, DomC.ofDom?]

def checkDifferentials : IO Unit := do
  checkDifferential "le" pDiffLe hreadyDiffLe
  checkDifferential "lt" pDiffLt hreadyDiffLt
  checkDifferential "eq" pDiffEq hreadyDiffEq
  checkDifferential "bool2int" pDiffB2I hreadyDiffB2I
  checkDifferential "leReif" pDiffLeReif hreadyDiffLeReif
  checkDifferential "le-bad" pDiffLeBad hreadyDiffLeBad
  checkDifferential "eq-bad" pDiffEqBad hreadyDiffEqBad
  checkDifferential "bool2int-bad" pDiffB2IBad hreadyDiffB2IBad

/-! ## Entry point -/

def run : IO UInt32 := do
  checkLeConstHi
  checkLeConstLo
  checkLtConstHi
  checkLtConstLo
  checkLe
  checkLt
  checkEq
  checkEqBool
  checkBool2Int
  checkLeReif
  checkEqReif
  checkNeReif
  checkMalformed
  checkDifferentials
  IO.println "OrderTest: OK"
  return 0

end Tests.Engine.OrderTest

open Tests.Engine.OrderTest in
def main : IO UInt32 := Tests.Engine.OrderTest.run
