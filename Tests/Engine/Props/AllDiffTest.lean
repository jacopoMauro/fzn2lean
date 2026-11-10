/-
Runtime tests for the dedicated `all_different` propagator (P1.1).

Run with:
  lake env lean --run Tests/Engine/Props/AllDiffTest.lean

The checks observe the emitted `PropOut` for fixed-value conflicts/prunings,
the repeated-slot refutation, Boolean slots, and full Core search on small
`all_different` problems.
-/
import LeanFzn.Engine.Search
import LeanFzn.Engine.Props.AllDiff

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Props.AllDiffTest

def fail (msg : String) : IO Unit := do
  IO.eprintln s!"AllDiffTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

def mkProblem (ds : List Dom) (cs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := cs
    objective := ()
    source := default
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray
    toStore := fun _ _ => none }

def convInit (ds : List Dom) : Array DomC :=
  ds.toArray.map fun d => (DomC.ofDom? d).getD DomC.empty

def isFix {p : CompiledProblem DomConstraint} {T : LitTable} : PropOut p T → Bool
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

def clauseEval (c : Clause) (b : List Value) : Bool :=
  c.any fun l => l.eval b == some true

def litEvalView (view : EngineView) (l : Literal) : Option Bool :=
  (view.doms.getD l.atom.slot DomC.empty).evalLit l

def checkAllFalse (label : String) (view : EngineView) (ls : List Literal) : IO Unit :=
  for l in ls do
    check s!"{label}: {repr l} is false" (litEvalView view l == some false)

def checkLitNone (label : String) (view : EngineView) (l : Literal) : IO Unit :=
  check s!"{label}: {repr l} is unassigned" (litEvalView view l == none)

def checkClauseEntailedRuntime (label : String)
    (p : CompiledProblem DomConstraint) (c : Clause) : IO Unit :=
  for b in allAssigns p.domains do
    if accepts p b then
      check s!"{label}: clause satisfied by {repr b}" (clauseEval c b)

/-! ## Domains -/

def dom00 : Dom := ⟨.holes 0 0 []⟩
def dom01 : Dom := ⟨.holes 0 1 []⟩
def dom012 : Dom := ⟨.holes 0 2 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩

/-! ## 1. Two fixed slots with the same value -/

def pConflict : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01] [.allDiff [0, 1]]

def initConflict : Array DomC := convInit pConflict.domains

theorem hinitConflict : ∀ s ∈ [0, 1],
    DomC.ofDom? (pConflict.domains.getD s Dom.empty) =
      some (initConflict.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa using hs
  rcases hs' with rfl | rfl <;>
    simp [pConflict, mkProblem, initConflict, convInit, dom01, DomC.ofDom?]

theorem hmemConflict : DomConstraint.allDiff [0, 1] ∈ pConflict.constraints := by
  simp [pConflict, mkProblem]

def conflictOut (view : EngineView) : PropOut pConflict ({} : LitTable) :=
  (allDiffPropWith pConflict ({} : LitTable) initConflict [0, 1]
    hinitConflict hmemConflict).run view

def conflictView : EngineView :=
  { doms := #[DomC.bounds 0 0, DomC.bounds 0 0], level := 0 }

def checkConflict : IO Unit := do
  match conflictClause? (conflictOut conflictView) with
  | some c =>
      check "conflict: clause" (c == [posNe 0 0, posNe 1 0])
      checkAllFalse "conflict" conflictView c
      checkClauseEntailedRuntime "conflict" pConflict c
  | none => fail "conflict: expected .conflict"

/-! ## 2. Fixed value pruned from another slot -/

def pPrune : CompiledProblem DomConstraint :=
  mkProblem [dom012, dom012] [.allDiff [0, 1]]

def initPrune : Array DomC := convInit pPrune.domains

theorem hinitPrune : ∀ s ∈ [0, 1],
    DomC.ofDom? (pPrune.domains.getD s Dom.empty) =
      some (initPrune.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa using hs
  rcases hs' with rfl | rfl <;>
    simp [pPrune, mkProblem, initPrune, convInit, dom012, DomC.ofDom?]

theorem hmemPrune : DomConstraint.allDiff [0, 1] ∈ pPrune.constraints := by
  simp [pPrune, mkProblem]

def pruneOut (view : EngineView) : PropOut pPrune ({} : LitTable) :=
  (allDiffPropWith pPrune ({} : LitTable) initPrune [0, 1]
    hinitPrune hmemPrune).run view

def pruneView : EngineView :=
  { doms := #[DomC.bounds 1 1, DomC.boundsHoles 0 2 #[]], level := 0 }

def fixView : EngineView :=
  { doms := #[DomC.bounds 0 0, DomC.bounds 1 1], level := 0 }

def checkPrune : IO Unit := do
  match pruneLits? (pruneOut pruneView), pruneClauses? (pruneOut pruneView) with
  | some lits, some [reason] =>
      check "prune: literal" (lits == [posNe 1 1])
      check "prune: reason" (reason == [posNe 0 1, posNe 1 1])
      checkAllFalse "prune: source" pruneView [posNe 0 1]
      checkLitNone "prune: target" pruneView (posNe 1 1)
      checkClauseEntailedRuntime "prune reason" pPrune reason
  | _, _ => fail "prune: expected one prune"
  check "fix: distinct fixed values" (isFix (pruneOut fixView))

/-! ## 3. Repeated slot identifier -/

def pDup : CompiledProblem DomConstraint :=
  mkProblem [dom01] [.allDiff [0, 0]]

def initDup : Array DomC := convInit pDup.domains

theorem hinitDup : ∀ s ∈ [0, 0],
    DomC.ofDom? (pDup.domains.getD s Dom.empty) =
      some (initDup.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 := by simpa using hs
  subst s
  simp [pDup, mkProblem, initDup, convInit, dom01, DomC.ofDom?]

theorem hmemDup : DomConstraint.allDiff [0, 0] ∈ pDup.constraints := by
  simp [pDup, mkProblem]

def dupOut (view : EngineView) : PropOut pDup ({} : LitTable) :=
  (allDiffPropWith pDup ({} : LitTable) initDup [0, 0]
    hinitDup hmemDup).run view

def checkDup : IO Unit := do
  match conflictClause? (dupOut { doms := #[DomC.bounds 0 0], level := 0 }) with
  | some c =>
      check "dup: empty clause" (c == [])
      checkClauseEntailedRuntime "dup" pDup c
  | none => fail "dup: expected .conflict"

/-! ## 4. Boolean slots -/

def pBool : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool] [.allDiff [0, 1]]

def initBool : Array DomC := convInit pBool.domains

theorem hinitBool : ∀ s ∈ [0, 1],
    DomC.ofDom? (pBool.domains.getD s Dom.empty) =
      some (initBool.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa using hs
  rcases hs' with rfl | rfl <;>
    simp [pBool, mkProblem, initBool, convInit, domBool, DomC.ofDom?, boolFold]

theorem hmemBool : DomConstraint.allDiff [0, 1] ∈ pBool.constraints := by
  simp [pBool, mkProblem]

def boolOut (view : EngineView) : PropOut pBool ({} : LitTable) :=
  (allDiffPropWith pBool ({} : LitTable) initBool [0, 1]
    hinitBool hmemBool).run view

def checkBool : IO Unit := do
  let view : EngineView := { doms := #[DomC.bool 1, DomC.bool 1], level := 0 }
  match conflictClause? (boolOut view) with
  | some c =>
      check "bool conflict: clause" (c == [posBool 0 true, posBool 1 true])
      checkAllFalse "bool conflict" view c
      checkClauseEntailedRuntime "bool conflict" pBool c
  | none => fail "bool conflict: expected .conflict"

/-! ## 5. Hall-interval conflict (pigeonhole) -/

def pHall : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, dom01] [.allDiff [0, 1, 2]]

def initHall : Array DomC := convInit pHall.domains

theorem hinitHall : ∀ s ∈ [0, 1, 2],
    DomC.ofDom? (pHall.domains.getD s Dom.empty) =
      some (initHall.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by simpa using hs
  rcases hs' with rfl | rfl | rfl <;>
    simp [pHall, mkProblem, initHall, convInit, dom01, DomC.ofDom?]

theorem hmemHall : DomConstraint.allDiff [0, 1, 2] ∈ pHall.constraints := by
  simp [pHall, mkProblem]

def hallOut (view : EngineView) : PropOut pHall ({} : LitTable) :=
  (allDiffPropWith pHall ({} : LitTable) initHall [0, 1, 2]
    hinitHall hmemHall).run view

def hallView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, DomC.bounds 0 1], level := 0 }

def checkHallConflict : IO Unit := do
  match conflictClause? (hallOut hallView) with
  | some c =>
      check "hall conflict: clause"
        (c == [posLe 0 (-1), negLe 0 1,
               posLe 1 (-1), negLe 1 1,
               posLe 2 (-1), negLe 2 1])
      checkAllFalse "hall conflict" hallView c
      checkClauseEntailedRuntime "hall conflict" pHall c
  | none => fail "hall conflict: expected .conflict"

/-! ## 6. Exact-fill lower-bound pruning -/

def pLower : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, dom012] [.allDiff [0, 1, 2]]

def initLower : Array DomC := convInit pLower.domains

theorem hinitLower : ∀ s ∈ [0, 1, 2],
    DomC.ofDom? (pLower.domains.getD s Dom.empty) =
      some (initLower.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by simpa using hs
  rcases hs' with rfl | rfl | rfl <;>
    simp [pLower, mkProblem, initLower, convInit, dom01, dom012, DomC.ofDom?]

theorem hmemLower : DomConstraint.allDiff [0, 1, 2] ∈ pLower.constraints := by
  simp [pLower, mkProblem]

def lowerOut (view : EngineView) : PropOut pLower ({} : LitTable) :=
  (allDiffPropWith pLower ({} : LitTable) initLower [0, 1, 2]
    hinitLower hmemLower).run view

def lowerView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, DomC.bounds 0 2], level := 0 }

def checkExactLower : IO Unit := do
  match pruneLits? (lowerOut lowerView), pruneClauses? (lowerOut lowerView) with
  | some lits, some [reason] =>
      check "exact lower: only one prune" (lits == [negLe 2 1])
      check "exact lower: reason"
        (reason == [posLe 2 (-1), negLe 2 1,
                    posLe 0 (-1), negLe 0 1,
                    posLe 1 (-1), negLe 1 1])
      checkAllFalse "exact lower: context" lowerView
        [posLe 2 (-1), posLe 0 (-1), negLe 0 1, posLe 1 (-1), negLe 1 1]
      checkLitNone "exact lower: target" lowerView (negLe 2 1)
      checkClauseEntailedRuntime "exact lower reason" pLower reason
  | _, _ => fail "exact lower: expected one prune"

/-! ## 7. Exact-fill upper-bound pruning -/

def domNeg11 : Dom := ⟨.holes (-1) 1 []⟩

def pUpper : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, domNeg11] [.allDiff [0, 1, 2]]

def initUpper : Array DomC := convInit pUpper.domains

theorem hinitUpper : ∀ s ∈ [0, 1, 2],
    DomC.ofDom? (pUpper.domains.getD s Dom.empty) =
      some (initUpper.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by simpa using hs
  rcases hs' with rfl | rfl | rfl <;>
    simp [pUpper, mkProblem, initUpper, convInit, dom01, domNeg11, DomC.ofDom?]

theorem hmemUpper : DomConstraint.allDiff [0, 1, 2] ∈ pUpper.constraints := by
  simp [pUpper, mkProblem]

def upperOut (view : EngineView) : PropOut pUpper ({} : LitTable) :=
  (allDiffPropWith pUpper ({} : LitTable) initUpper [0, 1, 2]
    hinitUpper hmemUpper).run view

def upperView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, DomC.bounds (-1) 1], level := 0 }

def checkExactUpper : IO Unit := do
  match pruneLits? (upperOut upperView), pruneClauses? (upperOut upperView) with
  | some lits, some [reason] =>
      check "exact upper: only one prune" (lits == [posLe 2 (-1)])
      check "exact upper: reason"
        (reason == [posLe 2 (-1), negLe 2 1,
                    posLe 0 (-1), negLe 0 1,
                    posLe 1 (-1), negLe 1 1])
      checkAllFalse "exact upper: context" upperView
        [negLe 2 1, posLe 0 (-1), negLe 0 1, posLe 1 (-1), negLe 1 1]
      checkLitNone "exact upper: target" upperView (posLe 2 (-1))
      checkClauseEntailedRuntime "exact upper reason" pUpper reason
  | _, _ => fail "exact upper: expected one prune"

/-! ## 8. Boolean domains are excluded from Hall reasoning -/

def pBoolHall : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool, domBool] [.allDiff [0, 1, 2]]

def initBoolHall : Array DomC := convInit pBoolHall.domains

theorem hinitBoolHall : ∀ s ∈ [0, 1, 2],
    DomC.ofDom? (pBoolHall.domains.getD s Dom.empty) =
      some (initBoolHall.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by simpa using hs
  rcases hs' with rfl | rfl | rfl <;>
    simp [pBoolHall, mkProblem, initBoolHall, convInit, domBool, DomC.ofDom?, boolFold]

theorem hmemBoolHall : DomConstraint.allDiff [0, 1, 2] ∈ pBoolHall.constraints := by
  simp [pBoolHall, mkProblem]

def boolHallOut (view : EngineView) : PropOut pBoolHall ({} : LitTable) :=
  (allDiffPropWith pBoolHall ({} : LitTable) initBoolHall [0, 1, 2]
    hinitBoolHall hmemBoolHall).run view

def boolHallView : EngineView :=
  { doms := #[DomC.bool 3, DomC.bool 3, DomC.bool 3], level := 0 }

def checkBoolHallExcluded : IO Unit := do
  check "bool: Hall skipped" (isFix (boolHallOut boolHallView))

/-! ## 5. Full Core search -/

def pSat : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, dom012] [.allDiff [0, 1, 2]]

def pUnsat : CompiledProblem DomConstraint :=
  mkProblem [dom00, dom00] [.allDiff [0, 1]]

def pDupSearch : CompiledProblem DomConstraint :=
  mkProblem [dom012] [.allDiff [0, 0]]

def pPigeonholeSearch : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, dom01] [.allDiff [0, 1, 2]]

def pHallSatSearch : CompiledProblem DomConstraint :=
  mkProblem [dom01, dom01, dom012] [.allDiff [0, 1, 2]]

def pBoolPigeonholeSearch : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool, domBool] [.allDiff [0, 1, 2]]

def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

def verdictName : CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

def checkSearch : IO Unit := do
  match coreSolveFull pSat {} coreFuel with
  | (.sat a, _) =>
      check "sat: in allAssigns" ((allAssigns pSat.domains).contains a)
      check "sat: accepted" (accepts pSat a)
  | (r, _) => fail s!"sat: unexpected verdict {verdictName r}"
  match coreSolveFull pUnsat {} coreFuel with
  | (.unsat, _) =>
      check "unsat: no accepted assignment" (noAccepted pUnsat)
  | (r, _) => fail s!"unsat: unexpected verdict {verdictName r}"
  match coreSolveFull pDupSearch {} coreFuel with
  | (.unsat, _) =>
      check "dup search: no accepted assignment" (noAccepted pDupSearch)
  | (r, _) => fail s!"dup search: unexpected verdict {verdictName r}"
  match coreSolveFull pPigeonholeSearch {} coreFuel with
  | (.unsat, _) =>
      check "pigeonhole search: no accepted assignment" (noAccepted pPigeonholeSearch)
  | (r, _) => fail s!"pigeonhole search: unexpected verdict {verdictName r}"
  match coreSolveFull pHallSatSearch {} coreFuel with
  | (.sat a, _) =>
      check "hall sat: accepted" (accepts pHallSatSearch a)
  | (r, _) => fail s!"hall sat: unexpected verdict {verdictName r}"
  match coreSolveFull pBoolPigeonholeSearch {} coreFuel with
  | (.unsat, _) =>
      check "bool pigeonhole search: no accepted assignment"
        (noAccepted pBoolPigeonholeSearch)
  | (r, _) => fail s!"bool pigeonhole search: unexpected verdict {verdictName r}"

def run : IO UInt32 := do
  checkConflict
  checkPrune
  checkDup
  checkBool
  checkHallConflict
  checkExactLower
  checkExactUpper
  checkBoolHallExcluded
  checkSearch
  IO.println "AllDiffTest: OK"
  return 0

end Tests.Engine.Props.AllDiffTest

open Tests.Engine.Props.AllDiffTest in
def main : IO UInt32 := Tests.Engine.Props.AllDiffTest.run
