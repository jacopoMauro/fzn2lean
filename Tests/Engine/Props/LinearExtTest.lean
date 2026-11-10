/-
Runtime tests for the dedicated bounded linear equality, disequality and
reified linear propagators in `LeanFzn/Engine/Props/LinearExt.lean`.

Run with:
  lake env lean --run Tests/Engine/Props/LinearExtTest.lean

The checks cover `int_lin_eq` conflict and both-direction bound prunes on
`2x + 3y = 10`, `int_lin_ne` conflict/all-but-one-fixed prunes and the
satisfiable `.fix` case, `r = true`/`r = false` propagation and
`r`-pruning for the three reified forms, runtime entailment over all
accepted assignments, malformed arity/missing bounds/non-compact views,
and a local differential table (`propsOfTest` versus the generic
`propCheckV2With` table) on the fixtures and on two benchmark instances
that use `int_lin_eq`/`int_lin_ne`.
-/
import LeanFzn.Parser.Parser
import LeanFzn.Checker.Check
import LeanFzn.Compiler.Normalize
import LeanFzn.Engine.Props.LinearExt
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Engine

namespace Tests.Engine.Props.LinearExtTest

/-- Abort with a diagnostic on the first failing check. -/
def fail {α : Type} (msg : String) : IO α := do
  IO.eprintln s!"LinearExtTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-! ## Problem and output helpers -/

/-- A compiled problem carrying just the supplied domains and constraints. -/
def mkProblem (ds : List Dom) (cs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := cs
    objective := ()
    source := default
    domainsArray := ds.toArray
    domainsArray_toList := List.toList_toArray
    toStore := fun _ _ => none }

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

/-- Output kind, used by the differential table. -/
def outKind {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → String
  | .fix => "fix"
  | .prune _ => "prune"
  | .conflict _ => "conflict"

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

def others (reason : Clause) (l : Literal) : Clause :=
  reason.filter fun x => x != l

/-- Runtime entailment check: every accepted assignment satisfies the clause. -/
def checkClauseEntailedRuntime (label : String)
    (p : CompiledProblem DomConstraint) (c : Clause) : IO Unit :=
  for b in allAssigns p.domains do
    if accepts p b then
      check s!"{label}: clause satisfied by {repr b}" (clauseEval c b)

def acceptedAssignments (p : CompiledProblem DomConstraint) : List (List Value) :=
  (allAssigns p.domains).filter fun b => accepts p b

/-! ## Concrete domains -/

def dom0_10 : Dom := ⟨.holes 0 10 []⟩
def dom1_10 : Dom := ⟨.holes 1 10 []⟩
def dom0_5 : Dom := ⟨.holes 0 5 []⟩
def dom3_4 : Dom := ⟨.holes 3 4 []⟩
def dom2_2 : Dom := ⟨.holes 2 2 []⟩
def dom3_3 : Dom := ⟨.holes 3 3 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩

def boolTrue : DomC := DomC.bool 2
def boolFalse : DomC := DomC.bool 1
def boolUnfixed : DomC := DomC.bool 3

/-! ## The shared `2x + 3y = 10` constraint -/

def pEq : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.linEq [2, 3] [0, 1] 10]

theorem hmemEq : DomConstraint.linEq [2, 3] [0, 1] 10 ∈ pEq.constraints := by
  simp [pEq, mkProblem]

theorem pEqHsize : ([2, 3].toArray.size = [0, 1].toArray.size) := by decide

theorem pEqSlots : slotsIntB pEq [0, 1] = true := by rfl

def eqOut (view : EngineView) : PropOut pEq ({} : LitTable) :=
  (linEqPropWith pEq ({} : LitTable) [2, 3] [0, 1] 10 hmemEq).run view

/-! ### 1. `linEq`: conflict, upper-bound prunes, lower-bound prune, fix -/

def eqConflictView : EngineView :=
  { doms := #[DomC.bounds 4 10, DomC.bounds 1 10], level := 0 }

def eqBothView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 3 4], level := 0 }

def eqLoView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 0 2], level := 0 }

def eqFixView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2], level := 0 }

def checkEqConflict : IO Unit := do
  match conflictClause? (eqOut eqConflictView) with
  | some c =>
      check "eq conflict: clause" (c == [posLe 0 3, posLe 1 0])
      checkAllFalse "eq conflict" eqConflictView c
      checkClauseEntailedRuntime "eq conflict" pEq c
  | none => fail "eq conflict: expected .conflict"

def checkEqBothPrunes : IO Unit := do
  match pruneLits? (eqOut eqBothView), pruneClauses? (eqOut eqBothView) with
  | some lits, some [r0, r1] =>
      check "eq both: literals" (lits == [posLe 0 0, posLe 1 3])
      check "eq both: first reason" (r0 == [posLe 1 2, posLe 0 0])
      check "eq both: second reason" (r1 == [posLe 0 (-1), posLe 1 3])
      checkLitNone "eq both unit" eqBothView (posLe 0 0)
      checkLitNone "eq both unit" eqBothView (posLe 1 3)
      checkAllFalse "eq both other" eqBothView [posLe 1 2]
      checkAllFalse "eq both other" eqBothView [posLe 0 (-1)]
      checkClauseEntailedRuntime "eq both reason" pEq r0
      checkClauseEntailedRuntime "eq both reason" pEq r1
  | _, _ => fail "eq both: expected two prunes"

def checkEqLoPrune : IO Unit := do
  match pruneLits? (eqOut eqLoView), pruneClauses? (eqOut eqLoView) with
  | some lits, some [reason] =>
      check "eq lo: literal" (lits == [negLe 0 1])
      check "eq lo: reason" (reason == [negLe 1 2, negLe 0 1])
      checkLitNone "eq lo unit" eqLoView (negLe 0 1)
      checkAllFalse "eq lo other" eqLoView [negLe 1 2]
      checkClauseEntailedRuntime "eq lo reason" pEq reason
  | _, _ => fail "eq lo: expected one prune"

def checkEqFix : IO Unit := do
  check "eq fixed solution: expected fix" (isFix (eqOut eqFixView))

/-! ### 2. `linNe`: conflict, all-but-one prune, satisfiable fix -/

def pNe : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.linNe [2, 3] [0, 1] 10]

theorem hmemNe : DomConstraint.linNe [2, 3] [0, 1] 10 ∈ pNe.constraints := by
  simp [pNe, mkProblem]

theorem pNeSlots : slotsIntB pNe [0, 1] = true := by rfl

def neOut (view : EngineView) : PropOut pNe ({} : LitTable) :=
  (linNePropWith pNe ({} : LitTable) [2, 3] [0, 1] 10 hmemNe).run view

def neConflictView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2], level := 0 }

def nePruneView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 0 10], level := 0 }

def neSatFixView : EngineView :=
  { doms := #[DomC.bounds 3 3, DomC.bounds 3 3], level := 0 }

def checkNeConflict : IO Unit := do
  match conflictClause? (neOut neConflictView) with
  | some c =>
      check "ne conflict: clause" (c == [posNe 0 2, posNe 1 2])
      checkAllFalse "ne conflict" neConflictView c
      checkClauseEntailedRuntime "ne conflict" pNe c
  | none => fail "ne conflict: expected .conflict"

def checkNePrune : IO Unit := do
  match pruneLits? (neOut nePruneView), pruneClauses? (neOut nePruneView) with
  | some lits, some [reason] =>
      check "ne prune: literal" (lits == [posNe 1 2])
      check "ne prune: reason" (reason == [posNe 0 2, posNe 1 2])
      checkLitNone "ne prune unit" nePruneView (posNe 1 2)
      checkAllFalse "ne prune other" nePruneView [posNe 0 2]
      checkClauseEntailedRuntime "ne prune reason" pNe reason
  | _, _ => fail "ne prune: expected one prune"

def checkNeFix : IO Unit := do
  check "ne satisfiable fixed: expected fix" (isFix (neOut neSatFixView))

/-! ### 3a. `linLeReif` -/

def pLeR : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.linLeReif [2, 3] [0, 1] 10 2]

theorem hmemLeR : DomConstraint.linLeReif [2, 3] [0, 1] 10 2 ∈ pLeR.constraints := by
  simp [pLeR, mkProblem]

theorem pLeRSlots : slotsIntB pLeR [0, 1] = true := by rfl

def leROut (view : EngineView) : PropOut pLeR ({} : LitTable) :=
  (linLeReifPropWith pLeR ({} : LitTable) [2, 3] [0, 1] 10 2 hmemLeR).run view

def leTrueView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 0 5, boolTrue], level := 0 }

def leFalseView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 0 5, boolFalse], level := 0 }

def lePruneTrueView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, boolUnfixed], level := 0 }

def lePruneFalseView : EngineView :=
  { doms := #[DomC.bounds 5 6, DomC.bounds 2 3, boolUnfixed], level := 0 }

def leSkipTrueView : EngineView :=
  { doms := #[DomC.bounds 0 0, DomC.bounds 0 0, boolTrue], level := 0 }

def leSkipFalseView : EngineView :=
  { doms := #[DomC.bounds 5 5, DomC.bounds 1 1, boolFalse], level := 0 }

def checkLeReif : IO Unit := do
  check "le reif decided r=true: fix" (isFix (leROut leSkipTrueView))
  check "le reif decided r=false: fix" (isFix (leROut leSkipFalseView))
  match pruneLits? (leROut leTrueView), pruneClauses? (leROut leTrueView) with
  | some lits, some [reason] =>
      check "le reif r=true: literal" (lits == [posLe 1 3])
      check "le reif r=true: reason"
        (reason == [posLe 0 (-1), posLe 1 3, posBool 2 false])
      checkLitNone "le reif r=true unit" leTrueView (posLe 1 3)
      checkAllFalse "le reif r=true other" leTrueView [posLe 0 (-1)]
      checkClauseEntailedRuntime "le reif r=true reason" pLeR reason
  | _, _ => fail "le reif r=true: expected one prune"
  match pruneLits? (leROut leFalseView), pruneClauses? (leROut leFalseView) with
  | some lits, some [reason] =>
      check "le reif r=false: literal" (lits == [negLe 1 0])
      check "le reif r=false: reason"
        (reason == [negLe 0 5, negLe 1 0, posBool 2 true])
      checkLitNone "le reif r=false unit" leFalseView (negLe 1 0)
      checkAllFalse "le reif r=false other" leFalseView [negLe 0 5]
      checkClauseEntailedRuntime "le reif r=false reason" pLeR reason
  | _, _ => fail "le reif r=false: expected one prune"
  match pruneLits? (leROut lePruneTrueView), pruneClauses? (leROut lePruneTrueView) with
  | some lits, some [reason] =>
      check "le reif prune r=true: literal" (lits == [posBool 2 true])
      check "le reif prune r=true: reason"
        (reason == [negLe 0 1, negLe 1 1, posBool 2 true])
      checkLitNone "le reif prune r=true unit" lePruneTrueView (posBool 2 true)
      checkAllFalse "le reif prune r=true other" lePruneTrueView
        [negLe 0 1, negLe 1 1]
      checkClauseEntailedRuntime "le reif prune r=true reason" pLeR reason
  | _, _ => fail "le reif prune r=true: expected one prune"
  match pruneLits? (leROut lePruneFalseView), pruneClauses? (leROut lePruneFalseView) with
  | some lits, some [reason] =>
      check "le reif prune r=false: literal" (lits == [posBool 2 false])
      check "le reif prune r=false: reason"
        (reason == [posLe 0 4, posLe 1 1, posBool 2 false])
      checkLitNone "le reif prune r=false unit" lePruneFalseView (posBool 2 false)
      checkAllFalse "le reif prune r=false other" lePruneFalseView
        [posLe 0 4, posLe 1 1]
      checkClauseEntailedRuntime "le reif prune r=false reason" pLeR reason
  | _, _ => fail "le reif prune r=false: expected one prune"

/-! ### 3b. `linEqReif` -/

def pEqR : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.linEqReif [2, 3] [0, 1] 10 2]

theorem hmemEqR : DomConstraint.linEqReif [2, 3] [0, 1] 10 2 ∈ pEqR.constraints := by
  simp [pEqR, mkProblem]

theorem pEqRSlots : slotsIntB pEqR [0, 1] = true := by rfl

def eqROut (view : EngineView) : PropOut pEqR ({} : LitTable) :=
  (linEqReifPropWith pEqR ({} : LitTable) [2, 3] [0, 1] 10 2 hmemEqR).run view

def eqRTrueView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 3 4, boolTrue], level := 0 }

def eqRFalseView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 0 10, boolFalse], level := 0 }

def eqRPruneTrueView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2, boolUnfixed], level := 0 }

def eqRPruneFalseView : EngineView :=
  { doms := #[DomC.bounds 5 6, DomC.bounds 2 3, boolUnfixed], level := 0 }

def checkEqReif : IO Unit := do
  match pruneLits? (eqROut eqRTrueView), pruneClauses? (eqROut eqRTrueView) with
  | some lits, some [r0, r1] =>
      check "eq reif r=true: literals" (lits == [posLe 0 0, posLe 1 3])
      check "eq reif r=true: first reason"
        (r0 == [posLe 1 2, posLe 0 0, posBool 2 false])
      check "eq reif r=true: second reason"
        (r1 == [posLe 0 (-1), posLe 1 3, posBool 2 false])
      checkClauseEntailedRuntime "eq reif r=true reason" pEqR r0
      checkClauseEntailedRuntime "eq reif r=true reason" pEqR r1
  | _, _ => fail "eq reif r=true: expected two prunes"
  match pruneLits? (eqROut eqRFalseView), pruneClauses? (eqROut eqRFalseView) with
  | some lits, some [reason] =>
      check "eq reif r=false: literal" (lits == [posNe 1 2])
      check "eq reif r=false: reason"
        (reason == [posNe 0 2, posNe 1 2, posBool 2 true])
      checkLitNone "eq reif r=false unit" eqRFalseView (posNe 1 2)
      checkAllFalse "eq reif r=false other" eqRFalseView [posNe 0 2]
      checkClauseEntailedRuntime "eq reif r=false reason" pEqR reason
  | _, _ => fail "eq reif r=false: expected one prune"
  match pruneLits? (eqROut eqRPruneTrueView), pruneClauses? (eqROut eqRPruneTrueView) with
  | some lits, some [reason] =>
      check "eq reif prune r=true: literal" (lits == [posBool 2 true])
      check "eq reif prune r=true: reason"
        (reason == [posLe 0 1, posLe 1 1, negLe 0 2, negLe 1 2, posBool 2 true])
      checkLitNone "eq reif prune r=true unit" eqRPruneTrueView (posBool 2 true)
      checkAllFalse "eq reif prune r=true other" eqRPruneTrueView
        [posLe 0 1, posLe 1 1, negLe 0 2, negLe 1 2]
      checkClauseEntailedRuntime "eq reif prune r=true reason" pEqR reason
  | _, _ => fail "eq reif prune r=true: expected one prune"
  match pruneLits? (eqROut eqRPruneFalseView), pruneClauses? (eqROut eqRPruneFalseView) with
  | some lits, some [reason] =>
      check "eq reif prune r=false: literal" (lits == [posBool 2 false])
      check "eq reif prune r=false: reason"
        (reason == [posLe 0 4, posLe 1 1, posBool 2 false])
      checkLitNone "eq reif prune r=false unit" eqRPruneFalseView (posBool 2 false)
      checkAllFalse "eq reif prune r=false other" eqRPruneFalseView
        [posLe 0 4, posLe 1 1]
      checkClauseEntailedRuntime "eq reif prune r=false reason" pEqR reason
  | _, _ => fail "eq reif prune r=false: expected one prune"

/-! ### 3c. `linNeReif` -/

def pNeR : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, domBool] [.linNeReif [2, 3] [0, 1] 10 2]

theorem hmemNeR : DomConstraint.linNeReif [2, 3] [0, 1] 10 2 ∈ pNeR.constraints := by
  simp [pNeR, mkProblem]

theorem pNeRSlots : slotsIntB pNeR [0, 1] = true := by rfl

def neROut (view : EngineView) : PropOut pNeR ({} : LitTable) :=
  (linNeReifPropWith pNeR ({} : LitTable) [2, 3] [0, 1] 10 2 hmemNeR).run view

def neRTrueView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 0 10, boolTrue], level := 0 }

def neRFalseView : EngineView :=
  { doms := #[DomC.bounds 0 5, DomC.bounds 3 4, boolFalse], level := 0 }

def neRPruneTrueView : EngineView :=
  { doms := #[DomC.bounds 5 6, DomC.bounds 2 3, boolUnfixed], level := 0 }

def neRPruneFalseView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2, boolUnfixed], level := 0 }

def checkNeReif : IO Unit := do
  match pruneLits? (neROut neRTrueView), pruneClauses? (neROut neRTrueView) with
  | some lits, some [reason] =>
      check "ne reif r=true: literal" (lits == [posNe 1 2])
      check "ne reif r=true: reason"
        (reason == [posNe 0 2, posNe 1 2, posBool 2 false])
      checkLitNone "ne reif r=true unit" neRTrueView (posNe 1 2)
      checkAllFalse "ne reif r=true other" neRTrueView [posNe 0 2]
      checkClauseEntailedRuntime "ne reif r=true reason" pNeR reason
  | _, _ => fail "ne reif r=true: expected one prune"
  match pruneLits? (neROut neRFalseView), pruneClauses? (neROut neRFalseView) with
  | some lits, some [r0, r1] =>
      check "ne reif r=false: literals" (lits == [posLe 0 0, posLe 1 3])
      check "ne reif r=false: first reason"
        (r0 == [posLe 1 2, posLe 0 0, posBool 2 true])
      check "ne reif r=false: second reason"
        (r1 == [posLe 0 (-1), posLe 1 3, posBool 2 true])
      checkClauseEntailedRuntime "ne reif r=false reason" pNeR r0
      checkClauseEntailedRuntime "ne reif r=false reason" pNeR r1
  | _, _ => fail "ne reif r=false: expected two prunes"
  match pruneLits? (neROut neRPruneTrueView), pruneClauses? (neROut neRPruneTrueView) with
  | some lits, some [reason] =>
      check "ne reif prune r=true: literal" (lits == [posBool 2 true])
      check "ne reif prune r=true: reason"
        (reason == [posLe 0 4, posLe 1 1, posBool 2 true])
      checkLitNone "ne reif prune r=true unit" neRPruneTrueView (posBool 2 true)
      checkAllFalse "ne reif prune r=true other" neRPruneTrueView [posLe 0 4, posLe 1 1]
      checkClauseEntailedRuntime "ne reif prune r=true reason" pNeR reason
  | _, _ => fail "ne reif prune r=true: expected one prune"
  match pruneLits? (neROut neRPruneFalseView), pruneClauses? (neROut neRPruneFalseView) with
  | some lits, some [reason] =>
      check "ne reif prune r=false: literal" (lits == [posBool 2 false])
      check "ne reif prune r=false: reason"
        (reason == [posLe 0 1, posLe 1 1, negLe 0 2, negLe 1 2, posBool 2 false])
      checkLitNone "ne reif prune r=false unit" neRPruneFalseView (posBool 2 false)
      checkAllFalse "ne reif prune r=false other" neRPruneFalseView
        [posLe 0 1, posLe 1 1, negLe 0 2, negLe 1 2]
      checkClauseEntailedRuntime "ne reif prune r=false reason" pNeR reason
  | _, _ => fail "ne reif prune r=false: expected one prune"

/-! ### 4. Malformed arity, missing bounds and non-integer (non-compact) views -/

def pMalformed : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.linEq [1] [0, 1] 10]

theorem hmemMalformed : DomConstraint.linEq [1] [0, 1] 10 ∈ pMalformed.constraints := by
  simp [pMalformed, mkProblem]

def malformedView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }

def malformedOut : PropOut pMalformed ({} : LitTable) :=
  (linEqPropWith pMalformed ({} : LitTable) [1] [0, 1] 10 hmemMalformed).run malformedView

def pBoolEqR : CompiledProblem DomConstraint :=
  mkProblem [domBool, dom0_10, domBool] [.linEqReif [1, 1] [0, 1] 1 2]

theorem hmemBoolEqR : DomConstraint.linEqReif [1, 1] [0, 1] 1 2 ∈ pBoolEqR.constraints := by
  simp [pBoolEqR, mkProblem]

def missingBoundsView : EngineView :=
  { doms := #[DomC.empty, DomC.bounds 0 10], level := 0 }

def nonIntegerView : EngineView :=
  { doms := #[DomC.bool 3, DomC.bounds 0 10], level := 0 }

def checkMalformed : IO Unit := do
  check "malformed arity: expected fix" (isFix malformedOut)
  check "missing bounds: expected fix" (isFix (eqOut missingBoundsView))
  -- `linNe` requires integer-kind view slots; a Boolean compact domain is
  -- rejected by the view-kind guard.
  let outNe := (linNePropWith pNe ({} : LitTable) [2, 3] [0, 1] 10 hmemNe).run
    nonIntegerView
  check "Boolean integer slot (linNe): expected fix" (isFix outNe)
  -- The reified builders additionally require `slotsIntB` (a Boolean slot
  -- can make `dotProduct` undefined).
  let outR := (linEqReifPropWith pBoolEqR ({} : LitTable) [1, 1] [0, 1] 1 2 hmemBoolEqR).run
    { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, boolUnfixed], level := 0 }
  check "Boolean slot in a reified linear constraint: expected fix" (isFix outR)

/-! ## 5. Local differential table -/

/-- A `propsOf`-shaped table that uses the dedicated `LinearExt` builders for
the whole linear family and the generic checker for every other family. -/
def propsOfTest (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .linEq cs is b =>
        linEqPropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNe cs is b =>
        linNePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linEqReif cs is b r =>
        linEqReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLeReif cs is b r =>
        linLeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linNeReif cs is b r =>
        linNeReifPropWith p T cs is b r
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .linLe cs is b =>
        linLePropWith p T cs is b
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- The test table satisfies the pruning contract. -/
theorem propsOfTest_pruneSound (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    PropsSound p T (propsOfTest p T init hinit) := by
  intro id pr hid
  have hpr : pr ∈ propsOfTest p T init hinit := by
    rw [Array.mem_iff_getElem?]
    exact ⟨id, hid⟩
  unfold propsOfTest at hpr
  rw [Array.mem_map] at hpr
  obtain ⟨x, _, hxpr⟩ := hpr
  rw [← hxpr]
  split
  case h_1 cs is b heq =>
    exact linEqPropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_2 cs is b heq =>
    exact linNePropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_3 cs is b r heq =>
    exact linEqReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_4 cs is b r heq =>
    exact linLeReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_5 cs is b r heq =>
    exact linNeReifPropWith_pruneSound cs is b r (heq ▸ List.mem_toArray.mp x.2)
  case h_6 cs is b heq =>
    exact linLePropWith_pruneSound cs is b (heq ▸ List.mem_toArray.mp x.2)
  case h_7 =>
    exact propCheckV2With_pruneSound p T x.val init
      (hinit x.val (List.mem_toArray.mp x.2)) (List.mem_toArray.mp x.2)

/-- The fully generic table: every constraint goes through `propCheckV2With`. -/
def propsOfGeneric (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    propCheckV2With p T x.1 init
      (hinit x.1 (List.mem_toArray.mp x.2))
      (List.mem_toArray.mp x.2)

/-- Run the per-constraint differential on a fully fixed view.  The generic
checker only fires when every slot is fixed, so agreement is asserted on the
fixed views; on loose views the dedicated builders are additionally stronger
(prunes instead of `.fix`), which the fixtures above already exercise. -/
def checkPropTableAgreement (label : String) (p : CompiledProblem DomConstraint)
    (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (view : EngineView) : IO Unit := do
  let testProps := propsOfTest p ({} : LitTable) init hinit
  let genProps := propsOfGeneric p ({} : LitTable) init hinit
  check s!"{label}: same table size" (testProps.size == genProps.size)
  for i in List.range testProps.size do
    match testProps[i]?, genProps[i]? with
    | some tp, some gp =>
        let t := tp.run view
        let g := gp.run view
        check s!"{label}: prop {i} verdict ({outKind t} vs {outKind g})"
          ((isFix t && isFix g) || (!isFix t && !isFix g))
    | _, _ => fail s!"{label}: missing propagator {i}"

/-- The compact domain produced by converting the interval `0..10`. -/
def conv (lo hi : Int) : DomC :=
  (DomC.ofDom? ⟨.holes lo hi []⟩).getD DomC.empty

def initEq : Array DomC := #[conv 0 10, conv 0 10]

theorem hinitEq : ∀ dc ∈ pEq.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pEq.domains.getD s Dom.empty) = some (initEq.getD s DomC.empty) := by
  intro dc hdc s hs
  simp [pEq, mkProblem] at hdc
  subst hdc
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;> decide

def initNe : Array DomC := #[conv 0 10, conv 0 10]

theorem hinitNe : ∀ dc ∈ pNe.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pNe.domains.getD s Dom.empty) = some (initNe.getD s DomC.empty) := by
  intro dc hdc s hs
  simp [pNe, mkProblem] at hdc
  subst hdc
  have hs' : s = 0 ∨ s = 1 := by simpa [dcSlotsFull] using hs
  rcases hs' with rfl | rfl <;> decide

def initLeR : Array DomC :=
  #[conv 0 10, conv 0 10, DomC.bool 3]

theorem hinitLeR : ∀ dc ∈ pLeR.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pLeR.domains.getD s Dom.empty) = some (initLeR.getD s DomC.empty) := by
  intro dc hdc s hs
  simp [pLeR, mkProblem] at hdc
  subst hdc
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by
    simpa [dcSlotsFull, List.mem_append, List.mem_singleton] using hs
  rcases hs' with rfl | rfl | rfl <;> decide

def initEqR : Array DomC :=
  #[conv 0 10, conv 0 10, DomC.bool 3]

theorem hinitEqR : ∀ dc ∈ pEqR.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pEqR.domains.getD s Dom.empty) = some (initEqR.getD s DomC.empty) := by
  intro dc hdc s hs
  simp [pEqR, mkProblem] at hdc
  subst hdc
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by
    simpa [dcSlotsFull, List.mem_append, List.mem_singleton] using hs
  rcases hs' with rfl | rfl | rfl <;> decide

def initNeR : Array DomC :=
  #[conv 0 10, conv 0 10, DomC.bool 3]

theorem hinitNeR : ∀ dc ∈ pNeR.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pNeR.domains.getD s Dom.empty) = some (initNeR.getD s DomC.empty) := by
  intro dc hdc s hs
  simp [pNeR, mkProblem] at hdc
  subst hdc
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 := by
    simpa [dcSlotsFull, List.mem_append, List.mem_singleton] using hs
  rcases hs' with rfl | rfl | rfl <;> decide

def eqSatFixedView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2], level := 0 }

def eqUnsatFixedView : EngineView :=
  { doms := #[DomC.bounds 4 4, DomC.bounds 1 1], level := 0 }

def neSatFixedView : EngineView :=
  { doms := #[DomC.bounds 3 3, DomC.bounds 3 3], level := 0 }

def leTrueSatFixedView : EngineView :=
  { doms := #[DomC.bounds 0 0, DomC.bounds 0 0, boolTrue], level := 0 }

def leTrueUnsatFixedView : EngineView :=
  { doms := #[DomC.bounds 5 5, DomC.bounds 5 5, boolTrue], level := 0 }

def eqRTrueSatFixedView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2, boolTrue], level := 0 }

def neRTrueUnsatFixedView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 2 2, boolTrue], level := 0 }

def checkDifferentialFixtures : IO Unit := do
  checkPropTableAgreement "diff eq sat" pEq initEq hinitEq eqSatFixedView
  checkPropTableAgreement "diff eq unsat" pEq initEq hinitEq eqUnsatFixedView
  checkPropTableAgreement "diff ne sat" pNe initNe hinitNe neSatFixedView
  checkPropTableAgreement "diff ne unsat" pNe initNe hinitNe neConflictView
  checkPropTableAgreement "diff le-reif sat" pLeR initLeR hinitLeR leTrueSatFixedView
  checkPropTableAgreement "diff le-reif unsat" pLeR initLeR hinitLeR leTrueUnsatFixedView
  checkPropTableAgreement "diff eq-reif sat" pEqR initEqR hinitEqR eqRTrueSatFixedView
  checkPropTableAgreement "diff ne-reif unsat" pNeR initNeR hinitNeR neRTrueUnsatFixedView

/-! ### Benchmark instances (`int_lin_eq` / `int_lin_ne`) -/

/-- A test-local copy of `Search.initState` whose propagator table is
`propsOfTest` instead of `Search.propsOf`. -/
def initStateTest (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  if !gateOkFast (propagationProblem p) then none
  else
    match convertDomains p.domains with
    | none => none
    | some doms =>
        if hready : initReady p doms = true then
          let hinitAll := initReady_spec hready
          let props := propsOfTest p T doms hinitAll
          some (initStateCore p T doms props)
        else none

/-- The test-local entry carries the conversion equation. -/
theorem initStateTest_initConv
    {p : CompiledProblem DomConstraint} {T : LitTable} {st : EngineState p T}
    (h : initStateTest p T = some st) : InitConv p st.doms := by
  unfold initStateTest at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_doms]
            exact ⟨(convertDomains_spec hc).2⟩
          · simp [hr] at h
  | false => simp [hg] at h

/-- The test-local entry satisfies `RootInv`. -/
theorem initStateTest_rootInv
    {p : CompiledProblem DomConstraint} {T : LitTable} {st : EngineState p T}
    (h : initStateTest p T = some st) (hT : T.Inv) :
    RootInv p T st.doms st := by
  unfold initStateTest at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_doms]
            exact initStateCore_rootInv p T doms _ hT
              (initInv_of_convertDomains hc) ⟨(convertDomains_spec hc).2⟩
          · simp [hr] at h
  | false => simp [hg] at h

/-- The test-local entry's propagator table satisfies `PropsSound`. -/
theorem initStateTest_propsSound
    {p : CompiledProblem DomConstraint} {T : LitTable} {st : EngineState p T}
    (h : initStateTest p T = some st) :
    PropsSound p T st.props := by
  unfold initStateTest at h
  cases hg : gateOkFast (propagationProblem p) with
  | true =>
      simp only [hg, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hc : convertDomains p.domains with
      | none => simp [hc] at h
      | some doms =>
          simp only [hc] at h
          by_cases hr : initReady p doms = true
          · simp [hr] at h
            subst h
            rw [initStateCore_props]
            exact propsOfTest_pruneSound p T doms _
          · simp [hr] at h
  | false => simp [hg] at h

/-- The test-local entry satisfies the history invariants, by the same
argument as `Search.initState_histInv`. -/
theorem initStateTest_histInv
    {p : CompiledProblem DomConstraint} {T : LitTable} {st : EngineState p T}
    (h : initStateTest p T = some st) : HistInv st.doms st := by
  unfold initStateTest at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [initStateCore_doms]
        exact initStateCore_histInv p T _ _
      · simp at h

/-- The `coreSolveFull` body with `initStateTest`. -/
def coreSolveTest (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult × EngineStats :=
  let T : LitTable := {}
  match hinit : initStateTest p T with
  | none => (.gaveUp, { gaveUp := 1 })
  | some st0 =>
      coreSolveFrom p T o st0
        (initStateTest_rootInv hinit LitTable.inv_empty)
        (initStateTest_propsSound hinit)
        (annotPrioArray p) (LeanFzn.Engine.configOrders p o) fuel

def verdictName : CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

def checkBenchmark (path : String) : IO Unit := do
  let src ←
    try IO.FS.readFile path
    catch _ => fail s!"benchmark: cannot read {path}"
  let model ←
    match Parser.parseModel src with
    | .ok m => pure m
    | .error e => fail s!"benchmark {path}: parse error {e}"
  let p ←
    match compileModelFull model with
    | .ok p => pure p
    | .error e => fail s!"benchmark {path}: compile error {e}"
  let o : SearchConfig := { var := .minc, val := .act }
  let fuel := 1000000
  let (rg, sg) := coreSolveFull p o fuel
  let (rt, st) := coreSolveTest p o fuel
  check s!"benchmark {path}: generic verdict is sat ({verdictName rg})"
    (verdictName rg == "sat")
  check s!"benchmark {path}: test verdict agrees ({verdictName rt})"
    (verdictName rt == verdictName rg)
  IO.println s!"LinearExtTest differential {path}: generic={verdictName rg} \
(decisions={sg.decisions}, propagations={sg.propagations}, conflicts={sg.conflicts}) \
test={verdictName rt} (decisions={st.decisions}, propagations={st.propagations}, \
conflicts={st.conflicts}) fuel={fuel}"

def checkBenchmarks : IO Unit := do
  checkBenchmark "audits/benchmark_fixtures/linear_hole.fzn"
  checkBenchmark "audits/benchmark_fixtures/generated/linear_chain_8.fzn"

/-! ## 6. Compile-time contract smoke checks -/

theorem boundsViewWF2 (d0 d1 : DomC) (h0 : d0.WF) (h1 : d1.WF) :
    ViewWF { doms := #[d0, d1], level := 0 } #[0, 1] := by
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have hi0 : i = 0 ∨ i = 1 := by omega
  rcases hi0 with rfl | rfl
  · simpa using h0
  · simpa using h1

theorem boundsViewWF3First (d0 d1 d2 : DomC) (h0 : d0.WF) (h1 : d1.WF) :
    ViewWF { doms := #[d0, d1, d2], level := 0 } #[0, 1] := by
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have hi0 : i = 0 ∨ i = 1 := by omega
  rcases hi0 with rfl | rfl
  · simpa using h0
  · simpa using h1

theorem intKindView2 (d0 d1 : DomC) (h0 : d0.intKindB = true) (h1 : d1.intKindB = true) :
    viewIntKindB { doms := #[d0, d1], level := 0 } #[0, 1] = true := by
  rw [viewIntKindB, Array.all_eq_true]
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have hi0 : i = 0 ∨ i = 1 := by omega
  rcases hi0 with rfl | rfl
  · simpa using h0
  · simpa using h1

theorem intKindView3 (d0 d1 d2 : DomC)
    (h0 : d0.intKindB = true) (h1 : d1.intKindB = true) :
    viewIntKindB { doms := #[d0, d1, d2], level := 0 } #[0, 1] = true := by
  rw [viewIntKindB, Array.all_eq_true]
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have hi0 : i = 0 ∨ i = 1 := by omega
  rcases hi0 with rfl | rfl
  · simpa using h0
  · simpa using h1

example (ec : EClause pEq ({} : LitTable))
    (h : (linEqPropWith pEq ({} : LitTable) [2, 3] [0, 1] 10 hmemEq).run
      eqConflictView = .conflict ec) :
    Entailed pEq (({} : LitTable).decodeClause ec.lits) :=
  linEqPropWith_conflict_entailed pEq ({} : LitTable) [2, 3] [0, 1] 10
    eqConflictView hmemEq pEqHsize
    (boundsViewWF2 (DomC.bounds 4 10) (DomC.bounds 1 10)
      (by simp [DomC.WF]) (by simp [DomC.WF])) h
example (ps : Array (PLit × EClause pNe ({} : LitTable)))
    (q : PLit × EClause pNe ({} : LitTable))
    (h : (linNePropWith pNe ({} : LitTable) [2, 3] [0, 1] 10 hmemNe).run
      nePruneView = .prune ps)
    (hq : q ∈ ps.toList) :
    Entailed pNe (({} : LitTable).decodeClause q.2.lits) :=
  linNePropWith_prune_reason_entailed pNe ({} : LitTable) [2, 3] [0, 1] 10
    nePruneView hmemNe (by decide)
    (boundsViewWF2 (DomC.bounds 2 2) (DomC.bounds 0 10)
      (by simp [DomC.WF]) (by simp [DomC.WF]))
    (intKindView2 (DomC.bounds 2 2) (DomC.bounds 0 10) rfl rfl) h hq

example (ps : Array (PLit × EClause pLeR ({} : LitTable)))
    (q : PLit × EClause pLeR ({} : LitTable))
    (h : (linLeReifPropWith pLeR ({} : LitTable) [2, 3] [0, 1] 10 2 hmemLeR).run
      lePruneTrueView = .prune ps)
    (hq : q ∈ ps.toList) :
    Entailed pLeR (({} : LitTable).decodeClause q.2.lits) :=
  linLeReifPropWith_prune_reason_entailed pLeR ({} : LitTable) [2, 3] [0, 1] 10 2
    lePruneTrueView hmemLeR (by decide)
    (boundsViewWF3First (DomC.bounds 0 1) (DomC.bounds 0 1) boolUnfixed
      (by simp [DomC.WF]) (by simp [DomC.WF]))
    pLeRSlots
    (intKindView3 (DomC.bounds 0 1) (DomC.bounds 0 1) boolUnfixed rfl rfl) h hq

def run : IO UInt32 := do
  checkEqConflict
  checkEqBothPrunes
  checkEqLoPrune
  checkEqFix
  checkNeConflict
  checkNePrune
  checkNeFix
  checkLeReif
  checkEqReif
  checkNeReif
  checkMalformed
  checkDifferentialFixtures
  checkBenchmarks
  IO.println "LinearExtTest: OK"
  return 0

end Tests.Engine.Props.LinearExtTest

open Tests.Engine.Props.LinearExtTest in
def main : IO UInt32 := Tests.Engine.Props.LinearExtTest.run
