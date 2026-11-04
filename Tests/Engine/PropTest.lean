/-
Runtime tests for the N6 propagator interface: the generic checker
(`propCheckV2With`), the Boolean-clause propagator and the `int_ne`
propagator.

Run with:
  lake env lean --run Tests/Engine/PropTest.lean

Every check below is a runtime evaluation.  The contractual statements are
the `_entailed`, `_lits_false` and `_prune` theorems in
`LeanFzn/Engine/Prop.lean`, `LeanFzn/Engine/Props/Bool.lean` and
`LeanFzn/Engine/Props/Ne.lean`.
-/
import LeanFzn.Engine.Prop
import LeanFzn.Engine.Props.Bool
import LeanFzn.Engine.Props.Ne

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.PropTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"PropTest FAIL: {msg}"
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

/-- Initial converted domains used to discharge the kind-homogeneity guard. -/
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

/-! ## Runtime clause and literal checks -/

/-- Bool-valued clause evaluator over `Literal.eval`. -/
def clauseEval (c : Clause) (b : List Value) : Bool :=
  c.any fun l => l.eval b == some true

/-- Evaluate a literal on an engine view. -/
def litEvalView (view : EngineView) (l : Literal) : Option Bool :=
  (view.doms.getD l.atom.slot DomC.empty).evalLit l

def checkAllFalse (label : String) (view : EngineView) (ls : List Literal) : IO Unit :=
  for l in ls do
    check s!"{label}: {repr l} is false" (litEvalView view l == some false)

def checkLitNone (label : String) (view : EngineView) (l : Literal) : IO Unit :=
  check s!"{label}: {repr l} is unassigned" (litEvalView view l == none)

/-- Runtime entailment check: every accepted assignment satisfies the clause. -/
def checkClauseEntailedRuntime (label : String)
    (p : CompiledProblem DomConstraint) (c : Clause) : IO Unit :=
  for b in allAssigns p.domains do
    if accepts p b then
      check s!"{label}: clause satisfied by {repr b}" (clauseEval c b)

/-! ## Concrete domains -/

def dom01 : Dom := ⟨.holes 0 1 []⟩
def dom123 : Dom := ⟨.holes 1 3 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩

/-! ## 1-4. The generic checker -/

def pGen : CompiledProblem DomConstraint :=
  mkProblem [dom01] [.constEq 0 (.int 0)]

def initGen : Array DomC := convInit pGen.domains

theorem hinitGen : ∀ s ∈ dcSlotsFull (.constEq 0 (.int 0)),
    DomC.ofDom? (pGen.domains.getD s Dom.empty) = some (initGen.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 := by simpa [dcSlotsFull] using hs
  subst s
  simp [pGen, mkProblem, initGen, convInit, dom01, DomC.ofDom?]

theorem hmemGen : DomConstraint.constEq 0 (.int 0) ∈ pGen.constraints := by
  simp [pGen, mkProblem]

def genOut (d : DomC) : PropOut pGen ({} : LitTable) :=
  (propCheckV2With pGen ({} : LitTable) (.constEq 0 (.int 0)) initGen
    hinitGen hmemGen).run { doms := #[d], level := 0 }

def checkGeneric : IO Unit := do
  -- 1. satisfiable box: the constraint holds on the forced assignment.
  check "generic sat: expected fix" (isFix (genOut (.bounds 0 0)))
  -- 2. conflicting box: the emitted clause is the singleton negation.
  let view : EngineView := { doms := #[DomC.bounds 1 1], level := 0 }
  let out := genOut (.bounds 1 1)
  match conflictClause? out with
  | some c =>
      check "generic conflict: clause [posNe 0 1]" (c == [posNe 0 1])
      checkAllFalse "generic conflict" view c
      checkClauseEntailedRuntime "generic conflict" pGen c
  | none => fail "generic conflict: expected .conflict"
  -- 4. guard regression: an inconsistent view (fixed value outside the
  -- initial converted domain) must perform no propagation.
  check "generic guard: expected fix" (isFix (genOut (.bounds 2 2)))

/-! ## 3. Generic Boolean conflict -/

def pGenBool : CompiledProblem DomConstraint :=
  mkProblem [domBool] [.constEq 0 (.bool true)]

def initGenBool : Array DomC := convInit pGenBool.domains

theorem hinitGenBool : ∀ s ∈ dcSlotsFull (.constEq 0 (.bool true)),
    DomC.ofDom? (pGenBool.domains.getD s Dom.empty) =
      some (initGenBool.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 := by simpa [dcSlotsFull] using hs
  subst s
  simp [pGenBool, mkProblem, initGenBool, convInit, domBool, DomC.ofDom?, boolFold]

theorem hmemGenBool : DomConstraint.constEq 0 (.bool true) ∈ pGenBool.constraints := by
  simp [pGenBool, mkProblem]

def genBoolOut (d : DomC) : PropOut pGenBool ({} : LitTable) :=
  (propCheckV2With pGenBool ({} : LitTable) (.constEq 0 (.bool true)) initGenBool
    hinitGenBool hmemGenBool).run { doms := #[d], level := 0 }

def checkGenericBool : IO Unit := do
  check "generic bool sat: expected fix" (isFix (genBoolOut (.bool 2)))
  let view : EngineView := { doms := #[DomC.bool 1], level := 0 }
  let out := genBoolOut (.bool 1)
  match conflictClause? out with
  | some c =>
      check "generic bool conflict: clause [posBool 0 true]" (c == [posBool 0 true])
      checkAllFalse "generic bool conflict" view c
      checkClauseEntailedRuntime "generic bool conflict" pGenBool c
  | none => fail "generic bool conflict: expected .conflict"

/-! ## 5. The Boolean-clause propagator -/

def pBoolClause : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool, domBool] [.boolClauseSlot [0, 1] [2]]

def initBoolClause : Array DomC := convInit pBoolClause.domains

theorem hinitBoolClause : ∀ s ∈ dcSlotsFull (.boolClauseSlot [0, 1] [2]),
    DomC.ofDom? (pBoolClause.domains.getD s Dom.empty) =
      some (initBoolClause.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl | rfl <;>
    simp [pBoolClause, mkProblem, initBoolClause, convInit, domBool,
      DomC.ofDom?, boolFold]

theorem hmemBoolClause :
    DomConstraint.boolClauseSlot [0, 1] [2] ∈ pBoolClause.constraints := by
  simp [pBoolClause, mkProblem]

def boolClauseOut (view : EngineView) : PropOut pBoolClause ({} : LitTable) :=
  (boolClausePropWith pBoolClause ({} : LitTable) [0, 1] [2] hmemBoolClause).run view

def boolPruneView : EngineView :=
  { doms := #[DomC.bool 1, DomC.bool 1, DomC.bool 3], level := 0 }

def boolConflictView : EngineView :=
  { doms := #[DomC.bool 1, DomC.bool 1, DomC.bool 2], level := 0 }

def checkBoolClause : IO Unit := do
  -- Two false literals and one unassigned: prune with the full clause.
  let out := boolClauseOut boolPruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "bool prune: unit literal" (lits == [posBool 2 false])
      check "bool prune: full reason"
        (reason == [posBool 0 true, posBool 1 true, posBool 2 false])
      checkLitNone "bool prune unit" boolPruneView (posBool 2 false)
      checkAllFalse "bool prune others" boolPruneView
        [posBool 0 true, posBool 1 true]
      checkClauseEntailedRuntime "bool prune reason" pBoolClause reason
  | _, _ => fail "bool prune: expected one unit prune"
  -- All three literals false: conflict with the full clause.
  let out := boolClauseOut boolConflictView
  match conflictClause? out with
  | some c =>
      check "bool conflict: full clause"
        (c == [posBool 0 true, posBool 1 true, posBool 2 false])
      checkAllFalse "bool conflict" boolConflictView c
      checkClauseEntailedRuntime "bool conflict" pBoolClause c
  | none => fail "bool conflict: expected .conflict"

/-! ## 6. The `int_ne` propagator -/

def pNe : CompiledProblem DomConstraint :=
  mkProblem [dom123, dom123] [.neSlot 0 1]

def initNe : Array DomC := convInit pNe.domains

theorem hinitNe : ∀ s ∈ dcSlotsFull (.neSlot 0 1),
    DomC.ofDom? (pNe.domains.getD s Dom.empty) = some (initNe.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;>
    simp [pNe, mkProblem, initNe, convInit, dom123, DomC.ofDom?]

theorem hmemNe : DomConstraint.neSlot 0 1 ∈ pNe.constraints := by
  simp [pNe, mkProblem]

def neOut (view : EngineView) : PropOut pNe ({} : LitTable) :=
  (nePropWith pNe ({} : LitTable) initNe 0 1 hinitNe hmemNe).run view

def nePruneView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.boundsHoles 1 3 #[]], level := 0 }

def neConflictView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2], level := 0 }

def neFixView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 3 3], level := 0 }

def checkNe : IO Unit := do
  -- x = 2, y in {1,2,3}: prune y != 2 with the two-literal reason.
  let out := neOut nePruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "ne prune: literal" (lits == [posNe 1 2])
      check "ne prune: reason" (reason == [posNe 0 2, posNe 1 2])
      checkAllFalse "ne prune: fixed literal" nePruneView [posNe 0 2]
      checkLitNone "ne prune: pruned literal" nePruneView (posNe 1 2)
      checkClauseEntailedRuntime "ne prune reason" pNe reason
  | _, _ => fail "ne prune: expected one prune"
  -- x = y = 2: conflict.
  let out := neOut neConflictView
  match conflictClause? out with
  | some c =>
      check "ne conflict: clause" (c == [posNe 0 2, posNe 1 2])
      checkAllFalse "ne conflict" neConflictView c
      checkClauseEntailedRuntime "ne conflict" pNe c
  | none => fail "ne conflict: expected .conflict"
  -- x = 2, y = 3: no propagation.
  check "ne fix: expected fix" (isFix (neOut neFixView))

/-! ## 6b. The `int_ne` propagator on Booleans -/

def pNeBool : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool] [.neSlot 0 1]

def initNeBool : Array DomC := convInit pNeBool.domains

theorem hinitNeBool : ∀ s ∈ dcSlotsFull (.neSlot 0 1),
    DomC.ofDom? (pNeBool.domains.getD s Dom.empty) =
      some (initNeBool.getD s DomC.empty) := by
  intro s hs
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;>
    simp [pNeBool, mkProblem, initNeBool, convInit, domBool, DomC.ofDom?, boolFold]

theorem hmemNeBool : DomConstraint.neSlot 0 1 ∈ pNeBool.constraints := by
  simp [pNeBool, mkProblem]

def neBoolOut (view : EngineView) : PropOut pNeBool ({} : LitTable) :=
  (nePropWith pNeBool ({} : LitTable) initNeBool 0 1 hinitNeBool hmemNeBool).run view

def neBoolPruneView : EngineView :=
  { doms := #[DomC.bool 1, DomC.bool 3], level := 0 }

def neBoolConflictView : EngineView :=
  { doms := #[DomC.bool 1, DomC.bool 1], level := 0 }

def checkNeBool : IO Unit := do
  -- x = false, y in {false,true}: prune y != false (i.e. y = true).
  let out := neBoolOut neBoolPruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "ne bool prune: literal" (lits == [posBool 1 true])
      check "ne bool prune: reason" (reason == [posBool 0 true, posBool 1 true])
      checkAllFalse "ne bool prune: fixed literal" neBoolPruneView [posBool 0 true]
      checkLitNone "ne bool prune: pruned literal" neBoolPruneView (posBool 1 true)
      checkClauseEntailedRuntime "ne bool prune reason" pNeBool reason
  | _, _ => fail "ne bool prune: expected one prune"
  -- x = y = false: conflict.
  let out := neBoolOut neBoolConflictView
  match conflictClause? out with
  | some c =>
      check "ne bool conflict: clause" (c == [posBool 0 true, posBool 1 true])
      checkAllFalse "ne bool conflict" neBoolConflictView c
      checkClauseEntailedRuntime "ne bool conflict" pNeBool c
  | none => fail "ne bool conflict: expected .conflict"

/-! ## 7. Compile-time API check with a real `hinit` proof -/

example : PropV2 pGen ({} : LitTable) :=
  propCheckV2With pGen ({} : LitTable) (.constEq 0 (.int 0)) initGen
    (by
      intro s hs
      have hs' : s = 0 := by simpa [dcSlotsFull] using hs
      subst s
      simp [pGen, mkProblem, initGen, convInit, dom01, DomC.ofDom?])
    (by simp [pGen, mkProblem])

def run : IO UInt32 := do
  checkGeneric
  checkGenericBool
  checkBoolClause
  checkNe
  checkNeBool
  IO.println "PropTest: OK"
  return 0

end Tests.Engine.PropTest

open Tests.Engine.PropTest in
def main : IO UInt32 := Tests.Engine.PropTest.run
