/-
Runtime tests for the dedicated bounded linear inequality (`int_lin_le`)
propagator in `LeanFzn/Engine/Props/Linear.lean`.

Run with:
  lake env lean --run Tests/Engine/LinearTest.lean

The checks cover conflict and prune clauses, the negative-coefficient
branch, Boolean slots with integer-view semantics, runtime entailment over
all accepted assignments, `evalLit` facts, the §A malformed-arity `.fix`
regression, and agreement between `linLeProp` and the membership-explicit
`linLePropWith`.  The contractual statements are the `linLeProp_*` and
`linLePropWith_*` theorems in `LeanFzn/Engine/Props/Linear.lean`.
-/
import LeanFzn.Engine.Props.Linear

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.LinearTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"LinearTest FAIL: {msg}"
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
    check s!"{label}: {repr l} is false" (litEvalView view l == some false)

def checkLitNone (label : String) (view : EngineView) (l : Literal) : IO Unit :=
  check s!"{label}: {repr l} is unassigned" (litEvalView view l == none)

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
def dom4_10 : Dom := ⟨.holes 4 10 []⟩
def dom1_10 : Dom := ⟨.holes 1 10 []⟩
def dom0_1 : Dom := ⟨.holes 0 1 []⟩
def dom3_3 : Dom := ⟨.holes 3 3 []⟩
def dom5_5 : Dom := ⟨.holes 5 5 []⟩
def dom10_10 : Dom := ⟨.holes 10 10 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩

/-! ## 1-4. `2x + 3y ≤ 10` -/

def pLinear : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.linLe [2, 3] [0, 1] 10]

theorem hmemLinear : DomConstraint.linLe [2, 3] [0, 1] 10 ∈ pLinear.constraints := by
  simp [pLinear, mkProblem]

def linOut (view : EngineView) : PropOut pLinear ({} : LitTable) :=
  (linLeProp pLinear ({} : LitTable) [2, 3] [0, 1] 10).run view

def linOutWith (view : EngineView) : PropOut pLinear ({} : LitTable) :=
  (linLePropWith pLinear ({} : LitTable) [2, 3] [0, 1] 10 hmemLinear).run view

/-- `ViewWF` for a two-slot bounds view. -/
theorem boundsViewWF (d0 d1 : DomC) (h0 : d0.WF) (h1 : d1.WF) :
    ViewWF { doms := #[d0, d1], level := 0 } #[0, 1] := by
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have hi0 : i = 0 ∨ i = 1 := by omega
  rcases hi0 with rfl | rfl
  · simpa using h0
  · simpa using h1

def conflictView : EngineView :=
  { doms := #[DomC.bounds 4 10, DomC.bounds 1 10], level := 0 }

def xPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 3 3], level := 0 }

def yPruneView : EngineView :=
  { doms := #[DomC.bounds 5 5, DomC.bounds 0 10], level := 0 }

def fixView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1], level := 0 }

def checkLinearConflict : IO Unit := do
  check "linear conflict: With agrees with linLeProp"
    (sameOutput (linOutWith conflictView) (linOut conflictView))
  let out := linOut conflictView
  match conflictClause? out with
  | some c =>
      check "linear conflict: clause"
        (c == [posLe 0 3, posLe 1 0])
      checkAllFalse "linear conflict" conflictView c
      checkClauseEntailedRuntime "linear conflict" pLinear c
  | none => fail "linear conflict: expected .conflict"

def checkLinearXPrune : IO Unit := do
  check "linear x-prune: With agrees with linLeProp"
    (sameOutput (linOutWith xPruneView) (linOut xPruneView))
  let out := linOut xPruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "linear x-prune: unit literal" (lits == [posLe 0 0])
      check "linear x-prune: reason"
        (reason == [posLe 1 2, posLe 0 0])
      checkAllFalse "linear x-prune other" xPruneView [posLe 1 2]
      checkLitNone "linear x-prune unit" xPruneView (posLe 0 0)
      checkClauseEntailedRuntime "linear x-prune reason" pLinear reason
  | _, _ => fail "linear x-prune: expected one prune"

def checkLinearYPrune : IO Unit := do
  check "linear y-prune: With agrees with linLeProp"
    (sameOutput (linOutWith yPruneView) (linOut yPruneView))
  let out := linOut yPruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "linear y-prune: unit literal" (lits == [posLe 1 0])
      check "linear y-prune: reason"
        (reason == [posLe 0 4, posLe 1 0])
      checkAllFalse "linear y-prune other" yPruneView [posLe 0 4]
      checkLitNone "linear y-prune unit" yPruneView (posLe 1 0)
      checkClauseEntailedRuntime "linear y-prune reason" pLinear reason
  | _, _ => fail "linear y-prune: expected one prune"

def checkLinearFix : IO Unit := do
  check "linear loose box: expected fix" (isFix (linOut fixView))
  check "linear loose box: With agrees with linLeProp"
    (sameOutput (linOutWith fixView) (linOut fixView))

/-! ## 5. Negative coefficient: `-2x + y ≤ 3` -/

def pNeg : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom10_10] [.linLe [-2, 1] [0, 1] 3]

theorem hmemNeg : DomConstraint.linLe [-2, 1] [0, 1] 3 ∈ pNeg.constraints := by
  simp [pNeg, mkProblem]

def negView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 10 10], level := 0 }

def negOut : PropOut pNeg ({} : LitTable) :=
  (linLeProp pNeg ({} : LitTable) [-2, 1] [0, 1] 3).run negView

def negOutWith : PropOut pNeg ({} : LitTable) :=
  (linLePropWith pNeg ({} : LitTable) [-2, 1] [0, 1] 3 hmemNeg).run negView

def checkNegativeCoefficient : IO Unit := do
  check "negative prune: With agrees with linLeProp"
    (sameOutput negOutWith negOut)
  match pruneLits? negOut, pruneClauses? negOut with
  | some lits, some [reason] =>
      -- (3 - 10) / 2 = -4 in Euclidean integer division, so newLo = 4
      -- and the propagated bound is `x > 3`.
      check "negative prune: negLe unit" (lits == [negLe 0 3])
      check "negative prune: reason"
        (reason == [posLe 1 9, negLe 0 3])
      checkAllFalse "negative prune other" negView [posLe 1 9]
      checkLitNone "negative prune unit" negView (negLe 0 3)
      checkClauseEntailedRuntime "negative prune reason" pNeg reason
  | _, _ => fail "negative prune: expected one prune"

/-! ## 6. Boolean slots in an integer linear constraint -/

def pBoolLinear : CompiledProblem DomConstraint :=
  mkProblem [domBool, domBool] [.linLe [1, 1] [0, 1] 1]

theorem hmemBool : DomConstraint.linLe [1, 1] [0, 1] 1 ∈ pBoolLinear.constraints := by
  simp [pBoolLinear, mkProblem]

def boolPruneView : EngineView :=
  { doms := #[DomC.bool 2, DomC.bool 3], level := 0 }

def boolConflictView : EngineView :=
  { doms := #[DomC.bool 2, DomC.bool 2], level := 0 }

def boolOut (view : EngineView) : PropOut pBoolLinear ({} : LitTable) :=
  (linLeProp pBoolLinear ({} : LitTable) [1, 1] [0, 1] 1).run view

def boolOutWith (view : EngineView) : PropOut pBoolLinear ({} : LitTable) :=
  (linLePropWith pBoolLinear ({} : LitTable) [1, 1] [0, 1] 1 hmemBool).run view

def checkBooleanSlots : IO Unit := do
  check "boolean prune/conflict: With agrees with linLeProp"
    (sameOutput (boolOutWith boolPruneView) (boolOut boolPruneView) &&
      sameOutput (boolOutWith boolConflictView) (boolOut boolConflictView))
  -- x = true, y in {false, true}: the integer view prunes `y ≤ 0`,
  -- i.e. the Boolean literal "y is false".
  let out := boolOut boolPruneView
  match pruneLits? out, pruneClauses? out with
  | some lits, some [reason] =>
      check "boolean prune: unit literal" (lits == [posLe 1 0])
      check "boolean prune: reason"
        (reason == [posLe 0 0, posLe 1 0])
      checkAllFalse "boolean prune other" boolPruneView [posLe 0 0]
      checkLitNone "boolean prune unit" boolPruneView (posLe 1 0)
      checkClauseEntailedRuntime "boolean prune reason" pBoolLinear reason
  | _, _ => fail "boolean prune: expected one prune"
  -- Both Boolean values true: conflict from their integer views 1 + 1 > 1.
  let out := boolOut boolConflictView
  match conflictClause? out with
  | some c =>
      check "boolean conflict: clause" (c == [posLe 0 0, posLe 1 0])
      checkAllFalse "boolean conflict" boolConflictView c
      checkClauseEntailedRuntime "boolean conflict" pBoolLinear c
  | none => fail "boolean conflict: expected .conflict"
  -- Residual kind issue (reported for N9): `dotProduct` reads integer
  -- values only, so `accepts` rejects every all-Boolean assignment even
  -- when the integer-view inequality holds.  The runtime entailment
  -- checks above are therefore vacuous for Boolean slots.
  check "boolean kind: satisfying Boolean assignment enumerated"
    ((allAssigns pBoolLinear.domains).contains [.bool true, .bool false])
  check "boolean kind: dotProduct rejects Boolean values"
    (!(accepts pBoolLinear [.bool true, .bool false]))
  check "boolean kind: no accepted Boolean assignments"
    (acceptedAssignments pBoolLinear).isEmpty

/-! ## 7. Malformed arity is a `.fix` no-op (§A) -/

def pMalformed : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.linLe [1] [0, 1] 10]

theorem hmemMalformed : DomConstraint.linLe [1] [0, 1] 10 ∈ pMalformed.constraints := by
  simp [pMalformed, mkProblem]

def malformedView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }

def malformedOut : PropOut pMalformed ({} : LitTable) :=
  (linLeProp pMalformed ({} : LitTable) [1] [0, 1] 10).run malformedView

def malformedWithOut : PropOut pMalformed ({} : LitTable) :=
  (linLePropWith pMalformed ({} : LitTable) [1] [0, 1] 10 hmemMalformed).run malformedView

example : malformedOut = .fix :=
  linLeProp_run_fix_of_size_ne pMalformed ({} : LitTable) [1] [0, 1] 10
    malformedView (by decide)

example : malformedWithOut = .fix :=
  linLePropWith_run_fix_of_size_ne pMalformed ({} : LitTable) [1] [0, 1] 10
    malformedView hmemMalformed (by decide)

def checkMalformedArity : IO Unit := do
  check "malformed arity: expected fix" (isFix malformedOut)
  check "malformed arity: With agrees with linLeProp"
    (sameOutput malformedWithOut malformedOut)

/-! ## 8. Compile-time contract checks through `linLePropWith` -/

example (ec : EClause pLinear ({} : LitTable))
    (h : (linLePropWith pLinear ({} : LitTable) [2, 3] [0, 1] 10 hmemLinear).run
      conflictView = .conflict ec) :
    Entailed pLinear (({} : LitTable).decodeClause ec.lits) :=
  linLePropWith_conflict_entailed pLinear ({} : LitTable) [2, 3] [0, 1] 10
    conflictView hmemLinear (by decide)
    (boundsViewWF (DomC.bounds 4 10) (DomC.bounds 1 10)
      (by simp [DomC.WF]) (by simp [DomC.WF])) h

example (ps : Array (PLit × EClause pLinear ({} : LitTable)))
    (q : PLit × EClause pLinear ({} : LitTable))
    (h : (linLePropWith pLinear ({} : LitTable) [2, 3] [0, 1] 10 hmemLinear).run
      xPruneView = .prune ps)
    (hq : q ∈ ps.toList) :
    Entailed pLinear (({} : LitTable).decodeClause q.2.lits) :=
  linLePropWith_prune_reason_entailed pLinear ({} : LitTable) [2, 3] [0, 1] 10
    xPruneView hmemLinear (by decide)
    (boundsViewWF (DomC.bounds 0 10) (DomC.bounds 3 3)
      (by simp [DomC.WF]) (by simp [DomC.WF])) h hq

example (ps : Array (PLit × EClause pLinear ({} : LitTable)))
    (q : PLit × EClause pLinear ({} : LitTable))
    (h : (linLePropWith pLinear ({} : LitTable) [2, 3] [0, 1] 10 hmemLinear).run
      xPruneView = .prune ps)
    (hq : q ∈ ps.toList) :
    (xPruneView.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ ({} : LitTable).decodeClause q.2.lits, q' ≠ q.1.lit →
        (xPruneView.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false :=
  linLePropWith_prune_lit_none pLinear ({} : LitTable) [2, 3] [0, 1] 10
    xPruneView hmemLinear (by decide)
    (boundsViewWF (DomC.bounds 0 10) (DomC.bounds 3 3)
      (by simp [DomC.WF]) (by simp [DomC.WF])) h hq

def run : IO UInt32 := do
  checkLinearConflict
  checkLinearXPrune
  checkLinearYPrune
  checkLinearFix
  checkNegativeCoefficient
  checkBooleanSlots
  checkMalformedArity
  IO.println "LinearTest: OK"
  return 0

end Tests.Engine.LinearTest

open Tests.Engine.LinearTest in
def main : IO UInt32 := Tests.Engine.LinearTest.run
