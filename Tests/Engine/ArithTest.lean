/-
Runtime tests for the dedicated arithmetic propagators in
`LeanFzn/Engine/Props/Arith.lean`.

Run with:
  lake env lean --run Tests/Engine/ArithTest.lean

The checks cover the stage-1 interval propagators (`plus`, `min`, `max`,
`abs`), the general `minPair`/`maxPair` forms, `minGen`/`maxGen`
(constants, slots and the empty operand list), `times` (signs, zero
factor, reverse division and fixed/fixed conflict), `div`/`mod`
(zero divisor, truncation toward zero, reverse dividend bounds and the
conservative `.fix` fallbacks), missing bounds, runtime entailment over
`allAssigns` filtered by `accepts`, and a test-local differential table
that wires the arithmetic builders through a local `propsOfTest` and
compares every verdict with the generic `propCheckV2With`.

The contractual statements are the `*PropWith_*` theorems in
`LeanFzn/Engine/Props/Arith.lean`.

Note on `div`/`mod` truncation: the source semantics is `Int.tdiv` /
`Int.tmod` (truncation toward zero, remainder sign follows the dividend),
so `(-7).tdiv 2 = -3` and `(-7).tmod 2 = -1`; the `-4` example in the
task text is floor division and would contradict the mandated
`Int.tdiv`.
-/
import LeanFzn.Engine.Props.Arith
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.ArithTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"ArithTest FAIL: {msg}"
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

/-- The interval-with-no-holes source domain. -/
def d (lo hi : Int) : Dom := ⟨.holes lo hi []⟩

/-- The compact domain produced by converting `d lo hi`. -/
def conv (lo hi : Int) : DomC := DomC.boundsHoles lo hi #[]

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

def checkHasAccepted (label : String) (p : CompiledProblem DomConstraint) : IO Unit :=
  check s!"{label}: accepted box is nonempty" (!(acceptedAssignments p).isEmpty)

/-! ## Output expectations -/

def P (l : Literal) (box : List Literal) : Literal × List Literal :=
  (l, box ++ [l])

/-- Check an exact prune batch: literals, reasons, unit status and
runtime entailment of every reason. -/
def expectPrunes (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) {T : LitTable} (out : PropOut p T)
    (expected : List (Literal × List Literal)) : IO Unit := do
  match pruneLits? out, pruneClauses? out with
  | some lits, some reasons =>
      check s!"{label}: unit literals" (lits == expected.map Prod.fst)
      check s!"{label}: reasons" (reasons == expected.map Prod.snd)
      for q in expected do
        checkLitNone (label ++ " unit") view q.1
        checkAllFalse (label ++ " other") view
          (q.2.filter fun l => l != q.1)
        checkClauseEntailedRuntime (label ++ " reason") p q.2
  | _, _ => fail s!"{label}: expected .prune"

/-- Check an exact conflict clause, its falsity on the view and runtime
entailment. -/
def expectConflict (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) {T : LitTable} (out : PropOut p T)
    (expected : Clause) : IO Unit := do
  match conflictClause? out with
  | some c =>
      check s!"{label}: clause" (c == expected)
      checkAllFalse (label ++ " lits") view c
      checkClauseEntailedRuntime (label ++ " clause") p c
  | none => fail s!"{label}: expected .conflict"

def expectFix (label : String) {p : CompiledProblem DomConstraint}
    {T : LitTable} (out : PropOut p T) : IO Unit :=
  check s!"{label}: expected .fix" (isFix out)

/-! ## A test-local `propsOf` with the arithmetic builders -/

/-- The coordinator's future table, reproduced locally: the eleven
arithmetic builders for their constructors, `propCheckV2With` for every
other family. -/
def propsOfTest (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .plusSlot i j k =>
        plusPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .timesSlot i j k =>
        timesPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minSlot i j k =>
        minPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxSlot i j k =>
        maxPropWith p T i j k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .absSlot i k =>
        absPropWith p T i k (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minPair o0 o1 r =>
        minPairPropWith p T o0 o1 r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxPair o0 o1 r =>
        maxPairPropWith p T o0 o1 r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .minGen os r =>
        minGenPropWith p T os r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .maxGen os r =>
        maxGenPropWith p T os r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .divGen o1 o2 r =>
        divPropWith p T o1 o2 r (by simpa [hx] using List.mem_toArray.mp x.2)
    | .modGen o1 o2 r =>
        modPropWith p T o1 o2 r (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- Restrict the global kind-homogeneity hypothesis to one constraint. -/
theorem hinitFor {p : CompiledProblem DomConstraint} {init : Array DomC}
    (h : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    {dc : DomConstraint} (hmem : dc ∈ p.constraints) :
    ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty) :=
  fun s hs => h dc hmem s hs

/-- Run every table entry on one view. -/
def runTable (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (view : EngineView) : List (PropOut p T) :=
  (propsOfTest p T init hinit).toList.map fun prop => prop.run view

/-- The table must agree with the direct builder on every view. -/
def checkTableAgrees (label : String) (p : CompiledProblem DomConstraint)
    (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (view : EngineView) {out : PropOut p T} : IO Unit := do
  match runTable p T init hinit view with
  | [t] => check s!"{label}: propsOfTest agrees" (sameOutput t out)
  | _ => fail s!"{label}: expected exactly one table entry"

/-! ## Differential machinery -/

def outIsConflict {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Bool
  | .conflict _ => true
  | _ => false

/-- Every output the dedicated or generic propagator emits must satisfy
the runtime halves of the contracts: conflict literals false and clauses
entailed; prune units unassigned, other reason literals false and
reasons entailed. -/
def checkOutContract {p : CompiledProblem DomConstraint} {T : LitTable}
    (label : String) (view : EngineView) (out : PropOut p T) : IO Unit :=
  match out with
  | .fix => pure ()
  | .conflict ec => do
      let c := T.decodeClause ec.lits
      checkAllFalse (label ++ " conflict") view c
      checkClauseEntailedRuntime (label ++ " conflict") p c
  | .prune ps => do
      for q in ps.toList do
        checkLitNone (label ++ " unit") view q.1.lit
        let reason := T.decodeClause q.2.lits
        checkAllFalse (label ++ " other") view
          (reason.filter fun l => l != q.1.lit)
        checkClauseEntailedRuntime (label ++ " reason") p reason

def allSlotsFixed (dc : DomConstraint) (view : EngineView) : Bool :=
  (dcSlotsFull dc).toArray.all fun s => (view.doms.getD s DomC.empty).isFixed

/-- The local differential table: on a list of small views, run the
dedicated builder and the generic checker, check both outputs against the
runtime contracts, assert conflict/fix agreement on fully fixed views
(the generic checker only fires there), and count nodes, propagator calls,
dedicated prunes, conflicts and verdict agreements.

`strict = false` is used for the deliberately conservative `minGen` /
`maxGen` slot-list fallback, whose `.fix` may be weaker than the generic
checker on a fixed unsatisfiable view. -/
def diffCheck (label : String) (p : CompiledProblem DomConstraint)
    (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (dc : DomConstraint) (ded gen : PropV2 p T)
    (views : List EngineView) (strict : Bool) : IO Unit := do
  let mut nodes : Nat := 0
  let mut agree : Nat := 0
  let mut conflicts : Nat := 0
  let mut prunes : Nat := 0
  for view in views do
    nodes := nodes + 1
    let d := ded.run view
    let g := gen.run view
    checkOutContract (label ++ " dedicated") view d
    checkOutContract (label ++ " generic") view g
    checkTableAgrees (label ++ " table") p T init hinit view (out := d)
    if allSlotsFixed dc view then
      if strict then
        if outIsConflict d != outIsConflict g then
          fail s!"{label}: fixed-view conflicts differ on {repr view.doms}: \
            dedicated={outIsConflict d} generic={outIsConflict g}"
        if !outIsConflict d then
          check s!"{label}: fixed satisfying view is a fix" (isFix d)
    if outIsConflict d then conflicts := conflicts + 1
    match d with
    | .prune _ => prunes := prunes + 1
    | _ => pure ()
    if outIsConflict d == outIsConflict g then agree := agree + 1
  IO.println s!"differential {label}: nodes={nodes} calls={2 * nodes} \
    conflicts={conflicts} prunes={prunes} verdict-agree={agree}"

/-- Cartesian product of three small domain choices. -/
def cross3 (xs ys zs : List DomC) : List EngineView :=
  xs.flatMap fun x => ys.flatMap fun y => zs.map fun z =>
    { doms := #[x, y, z], level := 0 }

/-- Cartesian product of two small domain choices. -/
def cross2 (xs ys : List DomC) : List EngineView :=
  xs.flatMap fun x => ys.map fun y =>
    { doms := #[x, y], level := 0 }

/-! ## Concrete problems -/

def pPlus : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3] [.plusSlot 0 1 2]
def initPlus : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitPlus : ∀ dc ∈ pPlus.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pPlus.domains.getD s Dom.empty) = some (initPlus.getD s DomC.empty) := by
  decide
theorem hmemPlus : DomConstraint.plusSlot 0 1 2 ∈ pPlus.constraints := by
  simp [pPlus, mkProblem]
def plusOut (view : EngineView) : PropOut pPlus ({} : LitTable) :=
  (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus).run view
def plusGen (view : EngineView) : PropOut pPlus ({} : LitTable) :=
  (propCheckV2With pPlus ({} : LitTable) (.plusSlot 0 1 2) initPlus (hinitFor hinitPlus hmemPlus) hmemPlus).run view

def pMin : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3] [.minSlot 0 1 2]
def initMin : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMin : ∀ dc ∈ pMin.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMin.domains.getD s Dom.empty) = some (initMin.getD s DomC.empty) := by
  decide
theorem hmemMin : DomConstraint.minSlot 0 1 2 ∈ pMin.constraints := by
  simp [pMin, mkProblem]
def minOut (view : EngineView) : PropOut pMin ({} : LitTable) :=
  (minPropWith pMin ({} : LitTable) 0 1 2 hmemMin).run view
def minGenOut (view : EngineView) : PropOut pMin ({} : LitTable) :=
  (propCheckV2With pMin ({} : LitTable) (.minSlot 0 1 2) initMin (hinitFor hinitMin hmemMin) hmemMin).run view

def pMax : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3] [.maxSlot 0 1 2]
def initMax : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMax : ∀ dc ∈ pMax.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMax.domains.getD s Dom.empty) = some (initMax.getD s DomC.empty) := by
  decide
theorem hmemMax : DomConstraint.maxSlot 0 1 2 ∈ pMax.constraints := by
  simp [pMax, mkProblem]
def maxOut (view : EngineView) : PropOut pMax ({} : LitTable) :=
  (maxPropWith pMax ({} : LitTable) 0 1 2 hmemMax).run view
def maxGen (view : EngineView) : PropOut pMax ({} : LitTable) :=
  (propCheckV2With pMax ({} : LitTable) (.maxSlot 0 1 2) initMax (hinitFor hinitMax hmemMax) hmemMax).run view

def pAbs : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3] [.absSlot 0 1]
def initAbs : Array DomC := #[conv (-3) 3, conv (-3) 3]
theorem hinitAbs : ∀ dc ∈ pAbs.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pAbs.domains.getD s Dom.empty) = some (initAbs.getD s DomC.empty) := by
  decide
theorem hmemAbs : DomConstraint.absSlot 0 1 ∈ pAbs.constraints := by
  simp [pAbs, mkProblem]
def absOut (view : EngineView) : PropOut pAbs ({} : LitTable) :=
  (absPropWith pAbs ({} : LitTable) 0 1 hmemAbs).run view
def absGen (view : EngineView) : PropOut pAbs ({} : LitTable) :=
  (propCheckV2With pAbs ({} : LitTable) (.absSlot 0 1) initAbs (hinitFor hinitAbs hmemAbs) hmemAbs).run view

def pTimes : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3] [.timesSlot 0 1 2]
def initTimes : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitTimes : ∀ dc ∈ pTimes.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pTimes.domains.getD s Dom.empty) = some (initTimes.getD s DomC.empty) := by
  decide
theorem hmemTimes : DomConstraint.timesSlot 0 1 2 ∈ pTimes.constraints := by
  simp [pTimes, mkProblem]
def timesOut (view : EngineView) : PropOut pTimes ({} : LitTable) :=
  (timesPropWith pTimes ({} : LitTable) 0 1 2 hmemTimes).run view
def timesGen (view : EngineView) : PropOut pTimes ({} : LitTable) :=
  (propCheckV2With pTimes ({} : LitTable) (.timesSlot 0 1 2) initTimes (hinitFor hinitTimes hmemTimes) hmemTimes).run view

def pDiv : CompiledProblem DomConstraint :=
  mkProblem [d (-4) 4, d (-4) 4, d (-4) 4]
    [.divGen (.slot 0) (.slot 1) (.slot 2)]
def initDiv : Array DomC := #[conv (-4) 4, conv (-4) 4, conv (-4) 4]
theorem hinitDiv : ∀ dc ∈ pDiv.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pDiv.domains.getD s Dom.empty) = some (initDiv.getD s DomC.empty) := by
  decide
theorem hmemDiv : DomConstraint.divGen (.slot 0) (.slot 1) (.slot 2) ∈ pDiv.constraints := by
  simp [pDiv, mkProblem]
def divOut (view : EngineView) : PropOut pDiv ({} : LitTable) :=
  (divPropWith pDiv ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemDiv).run view
def divGenOut (view : EngineView) : PropOut pDiv ({} : LitTable) :=
  (propCheckV2With pDiv ({} : LitTable) (.divGen (.slot 0) (.slot 1) (.slot 2))
    initDiv (hinitFor hinitDiv hmemDiv) hmemDiv).run view

def pMod : CompiledProblem DomConstraint :=
  mkProblem [d (-4) 4, d (-4) 4, d (-4) 4]
    [.modGen (.slot 0) (.slot 1) (.slot 2)]
def initMod : Array DomC := #[conv (-4) 4, conv (-4) 4, conv (-4) 4]
theorem hinitMod : ∀ dc ∈ pMod.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMod.domains.getD s Dom.empty) = some (initMod.getD s DomC.empty) := by
  decide
theorem hmemMod : DomConstraint.modGen (.slot 0) (.slot 1) (.slot 2) ∈ pMod.constraints := by
  simp [pMod, mkProblem]
def modOut (view : EngineView) : PropOut pMod ({} : LitTable) :=
  (modPropWith pMod ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMod).run view
def modGenOut (view : EngineView) : PropOut pMod ({} : LitTable) :=
  (propCheckV2With pMod ({} : LitTable) (.modGen (.slot 0) (.slot 1) (.slot 2))
    initMod (hinitFor hinitMod hmemMod) hmemMod).run view

/-! ## Stage 1: `plus` -/

def plusPruneXView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 3 3, DomC.bounds 5 8], level := 0 }
def plusPruneYView : EngineView :=
  { doms := #[DomC.bounds 3 3, DomC.bounds 0 10, DomC.bounds 5 8], level := 0 }
def plusPruneZView : EngineView :=
  { doms := #[DomC.bounds 2 3, DomC.bounds 4 5, DomC.bounds 0 20], level := 0 }
def plusConflictView : EngineView :=
  { doms := #[DomC.bounds 4 10, DomC.bounds 1 10, DomC.bounds 0 3], level := 0 }
def plusFixView : EngineView :=
  { doms := #[DomC.bounds 0 1, DomC.bounds 0 1, DomC.bounds 0 2], level := 0 }

def boxPlusX : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 3, hiLit 1 3, loLit 2 5, hiLit 2 8]
def boxPlusY : List Literal :=
  [loLit 0 3, hiLit 0 3, loLit 1 0, hiLit 1 10, loLit 2 5, hiLit 2 8]
def boxPlusZ : List Literal :=
  [loLit 0 2, hiLit 0 3, loLit 1 4, hiLit 1 5, loLit 2 0, hiLit 2 20]
def boxPlusConflict : List Literal :=
  [loLit 0 4, hiLit 0 10, loLit 1 1, hiLit 1 10, loLit 2 0, hiLit 2 3]

def checkPlus : IO Unit := do
  expectPrunes "plus x-prune" pPlus plusPruneXView (plusOut plusPruneXView)
    [P (negLe 0 1) boxPlusX, P (posLe 0 5) boxPlusX]
  checkTableAgrees "plus x-prune" pPlus ({} : LitTable) initPlus hinitPlus
    plusPruneXView (out := plusOut plusPruneXView)
  expectPrunes "plus y-prune" pPlus plusPruneYView (plusOut plusPruneYView)
    [P (negLe 1 1) boxPlusY, P (posLe 1 5) boxPlusY]
  expectPrunes "plus z-prune" pPlus plusPruneZView (plusOut plusPruneZView)
    [P (negLe 2 5) boxPlusZ, P (posLe 2 8) boxPlusZ]
  expectConflict "plus conflict" pPlus plusConflictView (plusOut plusConflictView)
    boxPlusConflict
  expectFix "plus fix" (plusOut plusFixView)
  checkHasAccepted "plus" pPlus

/-! ## Stage 1: `min` and `max` slots -/

def minPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 2 5, DomC.bounds 4 4], level := 0 }
def minPruneKView : EngineView :=
  { doms := #[DomC.bounds 2 6, DomC.bounds 3 9, DomC.bounds 0 10], level := 0 }
def minConflictView : EngineView :=
  { doms := #[DomC.bounds 5 10, DomC.bounds 6 10, DomC.bounds 0 4], level := 0 }
def minFixView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }

def boxMinPrune : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 2, hiLit 1 5, loLit 2 4, hiLit 2 4]
def boxMinPruneK : List Literal :=
  [loLit 0 2, hiLit 0 6, loLit 1 3, hiLit 1 9, loLit 2 0, hiLit 2 10]
def boxMinConflict : List Literal :=
  [loLit 0 5, hiLit 0 10, loLit 1 6, hiLit 1 10, loLit 2 0, hiLit 2 4]

def checkMin : IO Unit := do
  expectPrunes "min prune" pMin minPruneView (minOut minPruneView)
    [P (negLe 0 3) boxMinPrune, P (negLe 1 3) boxMinPrune]
  expectPrunes "min k-prune" pMin minPruneKView (minOut minPruneKView)
    [P (negLe 2 1) boxMinPruneK, P (posLe 2 6) boxMinPruneK]
  expectConflict "min conflict" pMin minConflictView (minOut minConflictView)
    boxMinConflict
  expectFix "min fix" (minOut minFixView)
  checkHasAccepted "min" pMin

def maxPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 2 5, DomC.bounds 4 4], level := 0 }
def maxPruneKView : EngineView :=
  { doms := #[DomC.bounds 2 6, DomC.bounds 3 9, DomC.bounds 0 10], level := 0 }
def maxConflictView : EngineView :=
  { doms := #[DomC.bounds 0 2, DomC.bounds 0 3, DomC.bounds 5 10], level := 0 }
def maxFixView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }

def boxMaxPrune : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 2, hiLit 1 5, loLit 2 4, hiLit 2 4]
def boxMaxPruneK : List Literal :=
  [loLit 0 2, hiLit 0 6, loLit 1 3, hiLit 1 9, loLit 2 0, hiLit 2 10]
def boxMaxConflict : List Literal :=
  [loLit 0 0, hiLit 0 2, loLit 1 0, hiLit 1 3, loLit 2 5, hiLit 2 10]

def checkMax : IO Unit := do
  expectPrunes "max prune" pMax maxPruneView (maxOut maxPruneView)
    [P (posLe 0 4) boxMaxPrune, P (posLe 1 4) boxMaxPrune]
  expectPrunes "max k-prune" pMax maxPruneKView (maxOut maxPruneKView)
    [P (negLe 2 2) boxMaxPruneK, P (posLe 2 9) boxMaxPruneK]
  expectConflict "max conflict" pMax maxConflictView (maxOut maxConflictView)
    boxMaxConflict
  expectFix "max fix" (maxOut maxFixView)
  checkHasAccepted "max" pMax

/-! ## Stage 1: `abs` -/

def absPruneXView : EngineView :=
  { doms := #[DomC.bounds (-5) 5, DomC.bounds 2 2], level := 0 }
def absPruneKView : EngineView :=
  { doms := #[DomC.bounds (-5) (-3), DomC.bounds 0 10], level := 0 }
def absConflictView : EngineView :=
  { doms := #[DomC.bounds 0 3, DomC.bounds (-5) (-1)], level := 0 }
def absFixView : EngineView :=
  { doms := #[DomC.bounds 1 3, DomC.bounds 1 3], level := 0 }

def boxAbsX : List Literal :=
  [loLit 0 (-5), hiLit 0 5, loLit 1 2, hiLit 1 2]
def boxAbsK : List Literal :=
  [loLit 0 (-5), hiLit 0 (-3), loLit 1 0, hiLit 1 10]
def boxAbsConflict : List Literal :=
  [loLit 0 0, hiLit 0 3, loLit 1 (-5), hiLit 1 (-1)]

def checkAbs : IO Unit := do
  expectPrunes "abs x-prune" pAbs absPruneXView (absOut absPruneXView)
    [P (negLe 0 (-3)) boxAbsX, P (posLe 0 2) boxAbsX]
  expectPrunes "abs k-prune" pAbs absPruneKView (absOut absPruneKView)
    [P (negLe 1 2) boxAbsK, P (posLe 1 5) boxAbsK]
  expectConflict "abs conflict" pAbs absConflictView (absOut absConflictView)
    boxAbsConflict
  expectFix "abs fix" (absOut absFixView)
  checkHasAccepted "abs" pAbs

/-! ## Stage 1: `minPair` / `maxPair` -/

def pMinPairLit : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3] [.minPair (.lit 5) (.slot 0) (.slot 1)]
def initMinPairLit : Array DomC := #[conv (-3) 3, conv (-3) 3]
theorem hinitMinPairLit : ∀ dc ∈ pMinPairLit.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinPairLit.domains.getD s Dom.empty) = some (initMinPairLit.getD s DomC.empty) := by
  decide
theorem hmemMinPairLit : DomConstraint.minPair (.lit 5) (.slot 0) (.slot 1) ∈ pMinPairLit.constraints := by
  simp [pMinPairLit, mkProblem]
def minPairLitOut (view : EngineView) : PropOut pMinPairLit ({} : LitTable) :=
  (minPairPropWith pMinPairLit ({} : LitTable) (.lit 5) (.slot 0) (.slot 1) hmemMinPairLit).run view
def minPairLitGen (view : EngineView) : PropOut pMinPairLit ({} : LitTable) :=
  (propCheckV2With pMinPairLit ({} : LitTable) (.minPair (.lit 5) (.slot 0) (.slot 1))
    initMinPairLit (hinitFor hinitMinPairLit hmemMinPairLit) hmemMinPairLit).run view

def pMaxPairLit : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3] [.maxPair (.lit 3) (.slot 0) (.slot 1)]
def initMaxPairLit : Array DomC := #[conv (-3) 3, conv (-3) 3]
theorem hinitMaxPairLit : ∀ dc ∈ pMaxPairLit.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxPairLit.domains.getD s Dom.empty) = some (initMaxPairLit.getD s DomC.empty) := by
  decide
theorem hmemMaxPairLit : DomConstraint.maxPair (.lit 3) (.slot 0) (.slot 1) ∈ pMaxPairLit.constraints := by
  simp [pMaxPairLit, mkProblem]
def maxPairLitOut (view : EngineView) : PropOut pMaxPairLit ({} : LitTable) :=
  (maxPairPropWith pMaxPairLit ({} : LitTable) (.lit 3) (.slot 0) (.slot 1) hmemMaxPairLit).run view
def maxPairLitGen (view : EngineView) : PropOut pMaxPairLit ({} : LitTable) :=
  (propCheckV2With pMaxPairLit ({} : LitTable) (.maxPair (.lit 3) (.slot 0) (.slot 1))
    initMaxPairLit (hinitFor hinitMaxPairLit hmemMaxPairLit) hmemMaxPairLit).run view

def pMinPairSlots : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3]
    [.minPair (.slot 0) (.slot 1) (.slot 2)]
def initMinPairSlots : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMinPairSlots : ∀ dc ∈ pMinPairSlots.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinPairSlots.domains.getD s Dom.empty) = some (initMinPairSlots.getD s DomC.empty) := by
  decide
theorem hmemMinPairSlots : DomConstraint.minPair (.slot 0) (.slot 1) (.slot 2) ∈ pMinPairSlots.constraints := by
  simp [pMinPairSlots, mkProblem]
def minPairSlotsOut (view : EngineView) : PropOut pMinPairSlots ({} : LitTable) :=
  (minPairPropWith pMinPairSlots ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMinPairSlots).run view
def minPairSlotsGen (view : EngineView) : PropOut pMinPairSlots ({} : LitTable) :=
  (propCheckV2With pMinPairSlots ({} : LitTable) (.minPair (.slot 0) (.slot 1) (.slot 2))
    initMinPairSlots (hinitFor hinitMinPairSlots hmemMinPairSlots) hmemMinPairSlots).run view

def pMaxPairSlots : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3]
    [.maxPair (.slot 0) (.slot 1) (.slot 2)]
def initMaxPairSlots : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMaxPairSlots : ∀ dc ∈ pMaxPairSlots.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxPairSlots.domains.getD s Dom.empty) = some (initMaxPairSlots.getD s DomC.empty) := by
  decide
theorem hmemMaxPairSlots : DomConstraint.maxPair (.slot 0) (.slot 1) (.slot 2) ∈ pMaxPairSlots.constraints := by
  simp [pMaxPairSlots, mkProblem]
def maxPairSlotsOut (view : EngineView) : PropOut pMaxPairSlots ({} : LitTable) :=
  (maxPairPropWith pMaxPairSlots ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMaxPairSlots).run view
def maxPairSlotsGen (view : EngineView) : PropOut pMaxPairSlots ({} : LitTable) :=
  (propCheckV2With pMaxPairSlots ({} : LitTable) (.maxPair (.slot 0) (.slot 1) (.slot 2))
    initMaxPairSlots (hinitFor hinitMaxPairSlots hmemMaxPairSlots) hmemMaxPairSlots).run view

def minPairLitPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }
def minPairLitConflictView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 6 10], level := 0 }
def maxPairLitPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }
def maxPairLitConflictView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 2], level := 0 }

def boxMinPairLit : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 0, hiLit 1 10]
def boxMinPairLitConflict : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 6, hiLit 1 10]
def boxMaxPairLitConflict : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 0, hiLit 1 2]

def checkPairs : IO Unit := do
  expectPrunes "minPair literal prune" pMinPairLit minPairLitPruneView
    (minPairLitOut minPairLitPruneView)
    [P (posLe 1 5) boxMinPairLit]
  expectConflict "minPair literal conflict" pMinPairLit minPairLitConflictView
    (minPairLitOut minPairLitConflictView) boxMinPairLitConflict
  expectFix "minPair literal fix"
    (minPairLitOut { doms := #[DomC.bounds 0 10, DomC.bounds 0 5], level := 0 })
  expectPrunes "maxPair literal prune" pMaxPairLit maxPairLitPruneView
    (maxPairLitOut maxPairLitPruneView)
    [P (negLe 1 2) boxMinPairLit]
  expectConflict "maxPair literal conflict" pMaxPairLit maxPairLitConflictView
    (maxPairLitOut maxPairLitConflictView) boxMaxPairLitConflict
  expectFix "maxPair literal fix"
    (maxPairLitOut { doms := #[DomC.bounds 0 10, DomC.bounds 3 10], level := 0 })
  expectPrunes "minPair slots prune" pMinPairSlots minPruneView
    (minPairSlotsOut minPruneView)
    [P (negLe 0 3) boxMinPrune, P (negLe 1 3) boxMinPrune]
  expectConflict "minPair slots conflict" pMinPairSlots minConflictView
    (minPairSlotsOut minConflictView) boxMinConflict
  expectPrunes "maxPair slots prune" pMaxPairSlots maxPruneView
    (maxPairSlotsOut maxPruneView)
    [P (posLe 0 4) boxMaxPrune, P (posLe 1 4) boxMaxPrune]
  expectConflict "maxPair slots conflict" pMaxPairSlots maxConflictView
    (maxPairSlotsOut maxConflictView) boxMaxConflict
  checkHasAccepted "minPair literal" pMinPairLit
  checkHasAccepted "maxPair literal" pMaxPairLit
  checkHasAccepted "minPair slots" pMinPairSlots
  checkHasAccepted "maxPair slots" pMaxPairSlots

/-! ## Stage 2: `minGen` / `maxGen` -/

def pMinGenConst : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3] [.minGen [.lit 3, .lit 7] (.slot 0)]
def initMinGenConst : Array DomC := #[conv (-3) 3]
theorem hinitMinGenConst : ∀ dc ∈ pMinGenConst.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinGenConst.domains.getD s Dom.empty) = some (initMinGenConst.getD s DomC.empty) := by
  decide
theorem hmemMinGenConst : DomConstraint.minGen [.lit 3, .lit 7] (.slot 0) ∈ pMinGenConst.constraints := by
  simp [pMinGenConst, mkProblem]
def minGenConstOut (view : EngineView) : PropOut pMinGenConst ({} : LitTable) :=
  (minGenPropWith pMinGenConst ({} : LitTable) [.lit 3, .lit 7] (.slot 0) hmemMinGenConst).run view
def minGenConstGen (view : EngineView) : PropOut pMinGenConst ({} : LitTable) :=
  (propCheckV2With pMinGenConst ({} : LitTable) (.minGen [.lit 3, .lit 7] (.slot 0))
    initMinGenConst (hinitFor hinitMinGenConst hmemMinGenConst) hmemMinGenConst).run view

def pMinGenLitBad : CompiledProblem DomConstraint :=
  mkProblem [] [.minGen [.lit 3, .lit 7] (.lit 5)]
theorem hinitMinGenLitBad : ∀ dc ∈ pMinGenLitBad.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinGenLitBad.domains.getD s Dom.empty) = some ((#[] : Array DomC).getD s DomC.empty) := by
  decide
theorem hmemMinGenLitBad : DomConstraint.minGen [.lit 3, .lit 7] (.lit 5) ∈ pMinGenLitBad.constraints := by
  simp [pMinGenLitBad, mkProblem]
def minGenLitBadOut (view : EngineView) : PropOut pMinGenLitBad ({} : LitTable) :=
  (minGenPropWith pMinGenLitBad ({} : LitTable) [.lit 3, .lit 7] (.lit 5) hmemMinGenLitBad).run view

def pMinGenSlots : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3]
    [.minGen [.slot 0, .slot 1] (.slot 2)]
def initMinGenSlots : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMinGenSlots : ∀ dc ∈ pMinGenSlots.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinGenSlots.domains.getD s Dom.empty) = some (initMinGenSlots.getD s DomC.empty) := by
  decide
theorem hmemMinGenSlots : DomConstraint.minGen [.slot 0, .slot 1] (.slot 2) ∈ pMinGenSlots.constraints := by
  simp [pMinGenSlots, mkProblem]
def minGenSlotsOut (view : EngineView) : PropOut pMinGenSlots ({} : LitTable) :=
  (minGenPropWith pMinGenSlots ({} : LitTable) [.slot 0, .slot 1] (.slot 2) hmemMinGenSlots).run view
def minGenSlotsGen (view : EngineView) : PropOut pMinGenSlots ({} : LitTable) :=
  (propCheckV2With pMinGenSlots ({} : LitTable) (.minGen [.slot 0, .slot 1] (.slot 2))
    initMinGenSlots (hinitFor hinitMinGenSlots hmemMinGenSlots) hmemMinGenSlots).run view

def pMinGenEmpty : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3] [.minGen [] (.slot 0)]
def initMinGenEmpty : Array DomC := #[conv (-3) 3]
theorem hinitMinGenEmpty : ∀ dc ∈ pMinGenEmpty.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinGenEmpty.domains.getD s Dom.empty) = some (initMinGenEmpty.getD s DomC.empty) := by
  decide
theorem hmemMinGenEmpty : DomConstraint.minGen [] (.slot 0) ∈ pMinGenEmpty.constraints := by
  simp [pMinGenEmpty, mkProblem]
def minGenEmptyOut (view : EngineView) : PropOut pMinGenEmpty ({} : LitTable) :=
  (minGenPropWith pMinGenEmpty ({} : LitTable) [] (.slot 0) hmemMinGenEmpty).run view
def minGenEmptyGen (view : EngineView) : PropOut pMinGenEmpty ({} : LitTable) :=
  (propCheckV2With pMinGenEmpty ({} : LitTable) (.minGen [] (.slot 0))
    initMinGenEmpty (hinitFor hinitMinGenEmpty hmemMinGenEmpty) hmemMinGenEmpty).run view

def pMinGenEmptyLit : CompiledProblem DomConstraint :=
  mkProblem [] [.minGen [] (.lit 3)]
theorem hinitMinGenEmptyLit : ∀ dc ∈ pMinGenEmptyLit.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMinGenEmptyLit.domains.getD s Dom.empty) = some ((#[] : Array DomC).getD s DomC.empty) := by
  decide
theorem hmemMinGenEmptyLit : DomConstraint.minGen [] (.lit 3) ∈ pMinGenEmptyLit.constraints := by
  simp [pMinGenEmptyLit, mkProblem]
def minGenEmptyLitOut (view : EngineView) : PropOut pMinGenEmptyLit ({} : LitTable) :=
  (minGenPropWith pMinGenEmptyLit ({} : LitTable) [] (.lit 3) hmemMinGenEmptyLit).run view

def pMaxGenConst : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3] [.maxGen [.lit 2, .lit 9] (.slot 0)]
def initMaxGenConst : Array DomC := #[conv (-3) 3]
theorem hinitMaxGenConst : ∀ dc ∈ pMaxGenConst.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxGenConst.domains.getD s Dom.empty) = some (initMaxGenConst.getD s DomC.empty) := by
  decide
theorem hmemMaxGenConst : DomConstraint.maxGen [.lit 2, .lit 9] (.slot 0) ∈ pMaxGenConst.constraints := by
  simp [pMaxGenConst, mkProblem]
def maxGenConstOut (view : EngineView) : PropOut pMaxGenConst ({} : LitTable) :=
  (maxGenPropWith pMaxGenConst ({} : LitTable) [.lit 2, .lit 9] (.slot 0) hmemMaxGenConst).run view
def maxGenConstGen (view : EngineView) : PropOut pMaxGenConst ({} : LitTable) :=
  (propCheckV2With pMaxGenConst ({} : LitTable) (.maxGen [.lit 2, .lit 9] (.slot 0))
    initMaxGenConst (hinitFor hinitMaxGenConst hmemMaxGenConst) hmemMaxGenConst).run view

def pMaxGenLitBad : CompiledProblem DomConstraint :=
  mkProblem [] [.maxGen [.lit 2, .lit 9] (.lit 5)]
theorem hinitMaxGenLitBad : ∀ dc ∈ pMaxGenLitBad.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxGenLitBad.domains.getD s Dom.empty) = some ((#[] : Array DomC).getD s DomC.empty) := by
  decide
theorem hmemMaxGenLitBad : DomConstraint.maxGen [.lit 2, .lit 9] (.lit 5) ∈ pMaxGenLitBad.constraints := by
  simp [pMaxGenLitBad, mkProblem]
def maxGenLitBadOut (view : EngineView) : PropOut pMaxGenLitBad ({} : LitTable) :=
  (maxGenPropWith pMaxGenLitBad ({} : LitTable) [.lit 2, .lit 9] (.lit 5) hmemMaxGenLitBad).run view

def pMaxGenSlots : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3, d (-3) 3, d (-3) 3]
    [.maxGen [.slot 0, .slot 1] (.slot 2)]
def initMaxGenSlots : Array DomC := #[conv (-3) 3, conv (-3) 3, conv (-3) 3]
theorem hinitMaxGenSlots : ∀ dc ∈ pMaxGenSlots.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxGenSlots.domains.getD s Dom.empty) = some (initMaxGenSlots.getD s DomC.empty) := by
  decide
theorem hmemMaxGenSlots : DomConstraint.maxGen [.slot 0, .slot 1] (.slot 2) ∈ pMaxGenSlots.constraints := by
  simp [pMaxGenSlots, mkProblem]
def maxGenSlotsOut (view : EngineView) : PropOut pMaxGenSlots ({} : LitTable) :=
  (maxGenPropWith pMaxGenSlots ({} : LitTable) [.slot 0, .slot 1] (.slot 2) hmemMaxGenSlots).run view
def maxGenSlotsGen (view : EngineView) : PropOut pMaxGenSlots ({} : LitTable) :=
  (propCheckV2With pMaxGenSlots ({} : LitTable) (.maxGen [.slot 0, .slot 1] (.slot 2))
    initMaxGenSlots (hinitFor hinitMaxGenSlots hmemMaxGenSlots) hmemMaxGenSlots).run view

def pMaxGenEmpty : CompiledProblem DomConstraint :=
  mkProblem [d (-3) 3] [.maxGen [] (.slot 0)]
def initMaxGenEmpty : Array DomC := #[conv (-3) 3]
theorem hinitMaxGenEmpty : ∀ dc ∈ pMaxGenEmpty.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxGenEmpty.domains.getD s Dom.empty) = some (initMaxGenEmpty.getD s DomC.empty) := by
  decide
theorem hmemMaxGenEmpty : DomConstraint.maxGen [] (.slot 0) ∈ pMaxGenEmpty.constraints := by
  simp [pMaxGenEmpty, mkProblem]
def maxGenEmptyOut (view : EngineView) : PropOut pMaxGenEmpty ({} : LitTable) :=
  (maxGenPropWith pMaxGenEmpty ({} : LitTable) [] (.slot 0) hmemMaxGenEmpty).run view
def maxGenEmptyGen (view : EngineView) : PropOut pMaxGenEmpty ({} : LitTable) :=
  (propCheckV2With pMaxGenEmpty ({} : LitTable) (.maxGen [] (.slot 0))
    initMaxGenEmpty (hinitFor hinitMaxGenEmpty hmemMaxGenEmpty) hmemMaxGenEmpty).run view

def pMaxGenEmptyLit : CompiledProblem DomConstraint :=
  mkProblem [] [.maxGen [] (.lit 3)]
theorem hinitMaxGenEmptyLit : ∀ dc ∈ pMaxGenEmptyLit.constraints, ∀ s ∈ dcSlotsFull dc,
    DomC.ofDom? (pMaxGenEmptyLit.domains.getD s Dom.empty) = some ((#[] : Array DomC).getD s DomC.empty) := by
  decide
theorem hmemMaxGenEmptyLit : DomConstraint.maxGen [] (.lit 3) ∈ pMaxGenEmptyLit.constraints := by
  simp [pMaxGenEmptyLit, mkProblem]
def maxGenEmptyLitOut (view : EngineView) : PropOut pMaxGenEmptyLit ({} : LitTable) :=
  (maxGenPropWith pMaxGenEmptyLit ({} : LitTable) [] (.lit 3) hmemMaxGenEmptyLit).run view

def genPruneView : EngineView :=
  { doms := #[DomC.bounds 0 10], level := 0 }
def genFixView : EngineView :=
  { doms := #[DomC.bounds 3 3], level := 0 }
def genConflictFixView : EngineView :=
  { doms := #[DomC.bounds 3 3, DomC.bounds 4 4, DomC.bounds 5 5], level := 0 }

def checkGen : IO Unit := do
  expectPrunes "minGen const prune" pMinGenConst genPruneView
    (minGenConstOut genPruneView)
    [P (negLe 0 2) [loLit 0 0, hiLit 0 10],
     P (posLe 0 3) [loLit 0 0, hiLit 0 10]]
  expectFix "minGen const fix" (minGenConstOut genFixView)
  expectConflict "minGen literal conflict" pMinGenLitBad
    { doms := #[], level := 0 } (minGenLitBadOut { doms := #[], level := 0 }) []
  expectFix "minGen slots fallback"
    (minGenSlotsOut { doms := #[DomC.bounds 0 10, DomC.bounds 2 5, DomC.bounds 0 10], level := 0 })
  expectFix "minGen slots fixed fallback" (minGenSlotsOut genConflictFixView)
  expectConflict "minGen empty conflict" pMinGenEmpty genPruneView
    (minGenEmptyOut genPruneView) [loLit 0 0, hiLit 0 10]
  expectConflict "minGen empty literal conflict" pMinGenEmptyLit
    { doms := #[], level := 0 } (minGenEmptyLitOut { doms := #[], level := 0 }) []
  expectPrunes "maxGen const prune" pMaxGenConst genPruneView
    (maxGenConstOut genPruneView)
    [P (negLe 0 8) [loLit 0 0, hiLit 0 10],
     P (posLe 0 9) [loLit 0 0, hiLit 0 10]]
  expectFix "maxGen const fix"
    (maxGenConstOut { doms := #[DomC.bounds 9 9], level := 0 })
  expectConflict "maxGen literal conflict" pMaxGenLitBad
    { doms := #[], level := 0 } (maxGenLitBadOut { doms := #[], level := 0 }) []
  expectFix "maxGen slots fallback"
    (maxGenSlotsOut { doms := #[DomC.bounds 0 10, DomC.bounds 2 5, DomC.bounds 0 10], level := 0 })
  expectFix "maxGen slots fixed fallback" (maxGenSlotsOut genConflictFixView)
  expectConflict "maxGen empty conflict" pMaxGenEmpty genPruneView
    (maxGenEmptyOut genPruneView) [loLit 0 0, hiLit 0 10]
  expectConflict "maxGen empty literal conflict" pMaxGenEmptyLit
    { doms := #[], level := 0 } (maxGenEmptyLitOut { doms := #[], level := 0 }) []

/-! ## Stage 3: `times` -/

def timesPosView : EngineView :=
  { doms := #[DomC.bounds 2 3, DomC.bounds 4 5, DomC.bounds 0 30], level := 0 }
def timesNegView : EngineView :=
  { doms := #[DomC.bounds (-3) (-2), DomC.bounds 4 5, DomC.bounds (-30) 30], level := 0 }
def timesMixedView : EngineView :=
  { doms := #[DomC.bounds (-2) 3, DomC.bounds (-4) 5, DomC.bounds (-30) 30], level := 0 }
def timesZeroView : EngineView :=
  { doms := #[DomC.bounds (-5) 5, DomC.bounds 0 0, DomC.bounds (-10) 10], level := 0 }
def timesZeroConflictView : EngineView :=
  { doms := #[DomC.bounds (-5) 5, DomC.bounds 0 0, DomC.bounds 5 5], level := 0 }
def timesFixedConflictView : EngineView :=
  { doms := #[DomC.bounds 2 2, DomC.bounds 3 3, DomC.bounds 7 7], level := 0 }
def timesReverseView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 2 2, DomC.bounds 6 8], level := 0 }
def timesReverseNegView : EngineView :=
  { doms := #[DomC.bounds (-10) 0, DomC.bounds (-2) (-2), DomC.bounds 6 8], level := 0 }
def timesFixView : EngineView :=
  { doms := #[DomC.bounds 1 2, DomC.bounds 1 2, DomC.bounds 1 4], level := 0 }

def boxTimesPos : List Literal :=
  [loLit 0 2, hiLit 0 3, loLit 1 4, hiLit 1 5, loLit 2 0, hiLit 2 30]
def boxTimesNeg : List Literal :=
  [loLit 0 (-3), hiLit 0 (-2), loLit 1 4, hiLit 1 5, loLit 2 (-30), hiLit 2 30]
def boxTimesMixed : List Literal :=
  [loLit 0 (-2), hiLit 0 3, loLit 1 (-4), hiLit 1 5, loLit 2 (-30), hiLit 2 30]
def boxTimesZero : List Literal :=
  [loLit 0 (-5), hiLit 0 5, loLit 1 0, hiLit 1 0, loLit 2 (-10), hiLit 2 10]
def boxTimesZeroConflict : List Literal :=
  [loLit 0 (-5), hiLit 0 5, loLit 1 0, hiLit 1 0, loLit 2 5, hiLit 2 5]
def boxTimesFixedConflict : List Literal :=
  [loLit 0 2, hiLit 0 2, loLit 1 3, hiLit 1 3, loLit 2 7, hiLit 2 7]
def boxTimesReverse : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 2, hiLit 1 2, loLit 2 6, hiLit 2 8]
def boxTimesReverseNeg : List Literal :=
  [loLit 0 (-10), hiLit 0 0, loLit 1 (-2), hiLit 1 (-2), loLit 2 6, hiLit 2 8]

def checkTimes : IO Unit := do
  expectPrunes "times positive" pTimes timesPosView (timesOut timesPosView)
    [P (negLe 2 7) boxTimesPos, P (posLe 2 15) boxTimesPos]
  expectPrunes "times negative" pTimes timesNegView (timesOut timesNegView)
    [P (negLe 2 (-16)) boxTimesNeg, P (posLe 2 (-8)) boxTimesNeg]
  expectPrunes "times mixed" pTimes timesMixedView (timesOut timesMixedView)
    [P (negLe 2 (-13)) boxTimesMixed, P (posLe 2 15) boxTimesMixed]
  expectPrunes "times zero factor" pTimes timesZeroView (timesOut timesZeroView)
    [P (negLe 2 (-1)) boxTimesZero, P (posLe 2 0) boxTimesZero]
  expectConflict "times zero conflict" pTimes timesZeroConflictView
    (timesOut timesZeroConflictView) boxTimesZeroConflict
  expectConflict "times fixed conflict" pTimes timesFixedConflictView
    (timesOut timesFixedConflictView) boxTimesFixedConflict
  expectPrunes "times reverse division" pTimes timesReverseView
    (timesOut timesReverseView)
    [P (negLe 0 2) boxTimesReverse, P (posLe 0 4) boxTimesReverse]
  expectPrunes "times reverse negative divisor" pTimes timesReverseNegView
    (timesOut timesReverseNegView)
    [P (negLe 0 (-5)) boxTimesReverseNeg, P (posLe 0 (-3)) boxTimesReverseNeg]
  expectFix "times fix" (timesOut timesFixView)
  checkHasAccepted "times" pTimes

/-! ## Stage 4: `div` and `mod` -/

def divZeroView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 0, DomC.bounds 0 10], level := 0 }
def divPosTouchView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 0 5, DomC.bounds 0 10], level := 0 }
def divNegTouchView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds (-5) 0, DomC.bounds 0 10], level := 0 }
def divTruncView : EngineView :=
  { doms := #[DomC.bounds (-7) (-7), DomC.bounds 2 2, DomC.bounds (-10) 10], level := 0 }
def divReverseView : EngineView :=
  { doms := #[DomC.bounds 0 100, DomC.bounds 2 2, DomC.bounds 5 5], level := 0 }
def divReverseNegView : EngineView :=
  { doms := #[DomC.bounds (-100) 0, DomC.bounds (-2) (-2), DomC.bounds 5 5], level := 0 }
def divFixedFixView : EngineView :=
  { doms := #[DomC.bounds (-7) (-7), DomC.bounds 2 2, DomC.bounds (-3) (-3)], level := 0 }
def divFixedConflictView : EngineView :=
  { doms := #[DomC.bounds (-7) (-7), DomC.bounds 2 2, DomC.bounds 0 0], level := 0 }
def divConservativeView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds (-5) 5, DomC.bounds 0 10], level := 0 }

def boxDivZero : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 0, hiLit 1 0, loLit 2 0, hiLit 2 10]
def boxDivPosTouch : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 0, hiLit 1 5, loLit 2 0, hiLit 2 10]
def boxDivNegTouch : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 (-5), hiLit 1 0, loLit 2 0, hiLit 2 10]
def boxDivTrunc : List Literal :=
  [loLit 0 (-7), hiLit 0 (-7), loLit 1 2, hiLit 1 2, loLit 2 (-10), hiLit 2 10]
def boxDivReverse : List Literal :=
  [loLit 0 0, hiLit 0 100, loLit 1 2, hiLit 1 2, loLit 2 5, hiLit 2 5]
def boxDivReverseNeg : List Literal :=
  [loLit 0 (-100), hiLit 0 0, loLit 1 (-2), hiLit 1 (-2), loLit 2 5, hiLit 2 5]
def boxDivFixedConflict : List Literal :=
  [loLit 0 (-7), hiLit 0 (-7), loLit 1 2, hiLit 1 2, loLit 2 0, hiLit 2 0]

def checkDiv : IO Unit := do
  -- Source semantics: truncation toward zero.
  check "div: (-7) tdiv 2 = -3" (Int.tdiv (-7) 2 == -3)
  check "mod: (-7) tmod 2 = -1" (Int.tmod (-7) 2 == -1)
  expectConflict "div zero divisor" pDiv divZeroView (divOut divZeroView) boxDivZero
  expectPrunes "div positive touching zero" pDiv divPosTouchView
    (divOut divPosTouchView)
    [P (negLe 1 0) boxDivPosTouch]
  expectPrunes "div negative touching zero" pDiv divNegTouchView
    (divOut divNegTouchView)
    [P (posLe 1 (-1)) boxDivNegTouch]
  expectPrunes "div truncation" pDiv divTruncView (divOut divTruncView)
    [P (negLe 2 (-4)) boxDivTrunc, P (posLe 2 (-3)) boxDivTrunc]
  expectPrunes "div reverse dividend" pDiv divReverseView
    (divOut divReverseView)
    [P (negLe 0 8) boxDivReverse, P (posLe 0 11) boxDivReverse]
  expectPrunes "div reverse negative divisor" pDiv divReverseNegView
    (divOut divReverseNegView)
    [P (negLe 0 (-12)) boxDivReverseNeg, P (posLe 0 (-9)) boxDivReverseNeg]
  expectFix "div fixed fix" (divOut divFixedFixView)
  expectConflict "div fixed conflict" pDiv divFixedConflictView
    (divOut divFixedConflictView) boxDivFixedConflict
  expectFix "div conservative straddling zero" (divOut divConservativeView)
  checkHasAccepted "div" pDiv

def modZeroView : EngineView := divZeroView
def modPosTouchView : EngineView := divPosTouchView
def modNegTouchView : EngineView := divNegTouchView
def modTruncView : EngineView := divTruncView
def modHullView : EngineView :=
  { doms := #[DomC.bounds 0 10, DomC.bounds 3 3, DomC.bounds (-5) 5], level := 0 }
def modNegDivisorView : EngineView :=
  { doms := #[DomC.bounds 7 7, DomC.bounds (-2) (-2), DomC.bounds (-5) 5], level := 0 }
def modFixedFixView : EngineView :=
  { doms := #[DomC.bounds (-7) (-7), DomC.bounds 2 2, DomC.bounds (-1) (-1)], level := 0 }
def modFixedConflictView : EngineView :=
  { doms := #[DomC.bounds (-7) (-7), DomC.bounds 2 2, DomC.bounds 0 0], level := 0 }
def modConservativeView : EngineView := divConservativeView

def boxModHull : List Literal :=
  [loLit 0 0, hiLit 0 10, loLit 1 3, hiLit 1 3, loLit 2 (-5), hiLit 2 5]
def boxModNegDiv : List Literal :=
  [loLit 0 7, hiLit 0 7, loLit 1 (-2), hiLit 1 (-2), loLit 2 (-5), hiLit 2 5]

def checkMod : IO Unit := do
  check "mod: 7 tmod (-2) = 1" (Int.tmod 7 (-2) == 1)
  expectConflict "mod zero divisor" pMod modZeroView (modOut modZeroView) boxDivZero
  expectPrunes "mod positive touching zero" pMod modPosTouchView
    (modOut modPosTouchView) [P (negLe 1 0) boxDivPosTouch]
  expectPrunes "mod negative touching zero" pMod modNegTouchView
    (modOut modNegTouchView) [P (posLe 1 (-1)) boxDivNegTouch]
  expectPrunes "mod truncation" pMod modTruncView (modOut modTruncView)
    [P (negLe 2 (-2)) boxDivTrunc, P (posLe 2 (-1)) boxDivTrunc]
  expectPrunes "mod wide hull" pMod modHullView (modOut modHullView)
    [P (negLe 2 (-3)) boxModHull, P (posLe 2 2) boxModHull]
  expectPrunes "mod negative divisor sign" pMod modNegDivisorView
    (modOut modNegDivisorView)
    [P (negLe 2 0) boxModNegDiv, P (posLe 2 1) boxModNegDiv]
  expectFix "mod fixed fix" (modOut modFixedFixView)
  expectConflict "mod fixed conflict" pMod modFixedConflictView
    (modOut modFixedConflictView) boxDivFixedConflict
  expectFix "mod conservative straddling zero" (modOut modConservativeView)
  checkHasAccepted "mod" pMod

/-! ## Missing bounds and non-integer (Boolean) slots -/

def missingView : EngineView :=
  { doms := #[DomC.bool 0, DomC.bounds 0 10, DomC.bounds 0 10], level := 0 }

def checkMalformed : IO Unit := do
  check "missing bounds: expected fix" (isFix (plusOut missingView))
  -- Boolean domains have no integer kind: the arithmetic propagators
  -- treat them as malformed and make no claim.
  let boolView : EngineView :=
    { doms := #[DomC.bool 2, DomC.bool 2, DomC.bounds 0 2], level := 0 }
  check "boolean slots: expected fix" (isFix (plusOut boolView))
  -- The same constraint is unsatisfiable on all-Boolean assignments, so
  -- the vacuous entailment of any emitted clause is not used here.
  check "boolean slots: accepts rejects Boolean arithmetic"
    (!(accepts pPlus [.bool true, .bool true, .int 2]))

/-! ## Differential tables -/

def boxesA : List DomC :=
  [DomC.bounds 0 2, DomC.bounds 1 2, DomC.bounds (-1) 1,
   DomC.bounds 2 2, DomC.bounds 0 0]
def boxesB : List DomC :=
  [DomC.bounds 0 2, DomC.bounds 1 2, DomC.bounds 2 2,
   DomC.bounds (-2) (-1), DomC.bounds 0 0, DomC.bounds (-1) 1]
def boxesZ : List DomC :=
  [DomC.bounds 0 2, DomC.bounds 1 2, DomC.bounds (-1) 1]

def checkDifferential : IO Unit := do
  diffCheck "plus" pPlus ({} : LitTable) initPlus hinitPlus
    (.plusSlot 0 1 2) (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus)
    (propCheckV2With pPlus ({} : LitTable) (.plusSlot 0 1 2) initPlus (hinitFor hinitPlus hmemPlus) hmemPlus)
    (cross3 boxesA boxesA boxesZ) true
  diffCheck "min" pMin ({} : LitTable) initMin hinitMin
    (.minSlot 0 1 2) (minPropWith pMin ({} : LitTable) 0 1 2 hmemMin)
    (propCheckV2With pMin ({} : LitTable) (.minSlot 0 1 2) initMin (hinitFor hinitMin hmemMin) hmemMin)
    (cross3 boxesA boxesA boxesZ) true
  diffCheck "max" pMax ({} : LitTable) initMax hinitMax
    (.maxSlot 0 1 2) (maxPropWith pMax ({} : LitTable) 0 1 2 hmemMax)
    (propCheckV2With pMax ({} : LitTable) (.maxSlot 0 1 2) initMax (hinitFor hinitMax hmemMax) hmemMax)
    (cross3 boxesA boxesA boxesZ) true
  diffCheck "abs" pAbs ({} : LitTable) initAbs hinitAbs
    (.absSlot 0 1) (absPropWith pAbs ({} : LitTable) 0 1 hmemAbs)
    (propCheckV2With pAbs ({} : LitTable) (.absSlot 0 1) initAbs (hinitFor hinitAbs hmemAbs) hmemAbs)
    (cross2 boxesB boxesZ) true
  diffCheck "times" pTimes ({} : LitTable) initTimes hinitTimes
    (.timesSlot 0 1 2) (timesPropWith pTimes ({} : LitTable) 0 1 2 hmemTimes)
    (propCheckV2With pTimes ({} : LitTable) (.timesSlot 0 1 2) initTimes (hinitFor hinitTimes hmemTimes) hmemTimes)
    (cross3 boxesA boxesB boxesZ) true
  diffCheck "div" pDiv ({} : LitTable) initDiv hinitDiv
    (.divGen (.slot 0) (.slot 1) (.slot 2))
    (divPropWith pDiv ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemDiv)
    (propCheckV2With pDiv ({} : LitTable) (.divGen (.slot 0) (.slot 1) (.slot 2))
      initDiv (hinitFor hinitDiv hmemDiv) hmemDiv)
    (cross3 boxesA boxesB boxesZ) true
  diffCheck "mod" pMod ({} : LitTable) initMod hinitMod
    (.modGen (.slot 0) (.slot 1) (.slot 2))
    (modPropWith pMod ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMod)
    (propCheckV2With pMod ({} : LitTable) (.modGen (.slot 0) (.slot 1) (.slot 2))
      initMod (hinitFor hinitMod hmemMod) hmemMod)
    (cross3 boxesA boxesB boxesZ) true
  diffCheck "minPair literal" pMinPairLit ({} : LitTable) initMinPairLit hinitMinPairLit
    (.minPair (.lit 5) (.slot 0) (.slot 1))
    (minPairPropWith pMinPairLit ({} : LitTable) (.lit 5) (.slot 0) (.slot 1) hmemMinPairLit)
    (propCheckV2With pMinPairLit ({} : LitTable) (.minPair (.lit 5) (.slot 0) (.slot 1))
      initMinPairLit (hinitFor hinitMinPairLit hmemMinPairLit) hmemMinPairLit)
    (cross2 boxesA boxesZ) true
  diffCheck "maxPair literal" pMaxPairLit ({} : LitTable) initMaxPairLit hinitMaxPairLit
    (.maxPair (.lit 3) (.slot 0) (.slot 1))
    (maxPairPropWith pMaxPairLit ({} : LitTable) (.lit 3) (.slot 0) (.slot 1) hmemMaxPairLit)
    (propCheckV2With pMaxPairLit ({} : LitTable) (.maxPair (.lit 3) (.slot 0) (.slot 1))
      initMaxPairLit (hinitFor hinitMaxPairLit hmemMaxPairLit) hmemMaxPairLit)
    (cross2 boxesA boxesZ) true
  diffCheck "minPair slots" pMinPairSlots ({} : LitTable) initMinPairSlots hinitMinPairSlots
    (.minPair (.slot 0) (.slot 1) (.slot 2))
    (minPairPropWith pMinPairSlots ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMinPairSlots)
    (propCheckV2With pMinPairSlots ({} : LitTable) (.minPair (.slot 0) (.slot 1) (.slot 2))
      initMinPairSlots (hinitFor hinitMinPairSlots hmemMinPairSlots) hmemMinPairSlots)
    (cross3 boxesA boxesA boxesZ) true
  diffCheck "maxPair slots" pMaxPairSlots ({} : LitTable) initMaxPairSlots hinitMaxPairSlots
    (.maxPair (.slot 0) (.slot 1) (.slot 2))
    (maxPairPropWith pMaxPairSlots ({} : LitTable) (.slot 0) (.slot 1) (.slot 2) hmemMaxPairSlots)
    (propCheckV2With pMaxPairSlots ({} : LitTable) (.maxPair (.slot 0) (.slot 1) (.slot 2))
      initMaxPairSlots (hinitFor hinitMaxPairSlots hmemMaxPairSlots) hmemMaxPairSlots)
    (cross3 boxesA boxesA boxesZ) true
  diffCheck "minGen const" pMinGenConst ({} : LitTable) initMinGenConst hinitMinGenConst
    (.minGen [.lit 3, .lit 7] (.slot 0))
    (minGenPropWith pMinGenConst ({} : LitTable) [.lit 3, .lit 7] (.slot 0) hmemMinGenConst)
    (propCheckV2With pMinGenConst ({} : LitTable) (.minGen [.lit 3, .lit 7] (.slot 0))
      initMinGenConst (hinitFor hinitMinGenConst hmemMinGenConst) hmemMinGenConst)
    (cross2 boxesA boxesA) true
  diffCheck "maxGen const" pMaxGenConst ({} : LitTable) initMaxGenConst hinitMaxGenConst
    (.maxGen [.lit 2, .lit 9] (.slot 0))
    (maxGenPropWith pMaxGenConst ({} : LitTable) [.lit 2, .lit 9] (.slot 0) hmemMaxGenConst)
    (propCheckV2With pMaxGenConst ({} : LitTable) (.maxGen [.lit 2, .lit 9] (.slot 0))
      initMaxGenConst (hinitFor hinitMaxGenConst hmemMaxGenConst) hmemMaxGenConst)
    (cross2 boxesA boxesA) true
  diffCheck "minGen empty" pMinGenEmpty ({} : LitTable) initMinGenEmpty hinitMinGenEmpty
    (.minGen [] (.slot 0))
    (minGenPropWith pMinGenEmpty ({} : LitTable) [] (.slot 0) hmemMinGenEmpty)
    (propCheckV2With pMinGenEmpty ({} : LitTable) (.minGen [] (.slot 0))
      initMinGenEmpty (hinitFor hinitMinGenEmpty hmemMinGenEmpty) hmemMinGenEmpty)
    (cross2 boxesA boxesA) true
  diffCheck "maxGen empty" pMaxGenEmpty ({} : LitTable) initMaxGenEmpty hinitMaxGenEmpty
    (.maxGen [] (.slot 0))
    (maxGenPropWith pMaxGenEmpty ({} : LitTable) [] (.slot 0) hmemMaxGenEmpty)
    (propCheckV2With pMaxGenEmpty ({} : LitTable) (.maxGen [] (.slot 0))
      initMaxGenEmpty (hinitFor hinitMaxGenEmpty hmemMaxGenEmpty) hmemMaxGenEmpty)
    (cross2 boxesA boxesA) true
  diffCheck "minGen slots (conservative)" pMinGenSlots ({} : LitTable)
    initMinGenSlots hinitMinGenSlots
    (.minGen [.slot 0, .slot 1] (.slot 2))
    (minGenPropWith pMinGenSlots ({} : LitTable) [.slot 0, .slot 1] (.slot 2) hmemMinGenSlots)
    (propCheckV2With pMinGenSlots ({} : LitTable) (.minGen [.slot 0, .slot 1] (.slot 2))
      initMinGenSlots (hinitFor hinitMinGenSlots hmemMinGenSlots) hmemMinGenSlots)
    (cross3 boxesA boxesA boxesZ) false
  diffCheck "maxGen slots (conservative)" pMaxGenSlots ({} : LitTable)
    initMaxGenSlots hinitMaxGenSlots
    (.maxGen [.slot 0, .slot 1] (.slot 2))
    (maxGenPropWith pMaxGenSlots ({} : LitTable) [.slot 0, .slot 1] (.slot 2) hmemMaxGenSlots)
    (propCheckV2With pMaxGenSlots ({} : LitTable) (.maxGen [.slot 0, .slot 1] (.slot 2))
      initMaxGenSlots (hinitFor hinitMaxGenSlots hmemMaxGenSlots) hmemMaxGenSlots)
    (cross3 boxesA boxesA boxesZ) false

/-! ## Compile-time contract checks -/

/-- `ViewWF` for a three-slot bounds view. -/
theorem boundsViewWF3 (d0 d1 d2 : DomC) (h0 : d0.WF) (h1 : d1.WF) (h2 : d2.WF) :
    ViewWF { doms := #[d0, d1, d2], level := 0 } #[0, 1, 2] := by
  intro i hi
  have hi' : i < 3 := by simpa using hi
  have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h3 with rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- `ViewWF` for a two-slot bounds view. -/
theorem boundsViewWF2 (d0 d1 : DomC) (h0 : d0.WF) (h1 : d1.WF) :
    ViewWF { doms := #[d0, d1], level := 0 } #[0, 1] := by
  intro i hi
  have hi' : i < 2 := by simpa using hi
  have h2 : i = 0 ∨ i = 1 := by omega
  rcases h2 with rfl | rfl
  · simpa using h0
  · simpa using h1

example (ec : EClause pPlus ({} : LitTable))
    (h : (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus).run
      plusConflictView = .conflict ec) :
    Entailed pPlus (({} : LitTable).decodeClause ec.lits) :=
  plusPropWith_conflict_entailed pPlus ({} : LitTable) 0 1 2 hmemPlus
    plusConflictView
    (boundsViewWF3 (DomC.bounds 4 10) (DomC.bounds 1 10) (DomC.bounds 0 3)
      (by simp [DomC.WF]) (by simp [DomC.WF]) (by simp [DomC.WF])) h

example (ps : Array (PLit × EClause pPlus ({} : LitTable)))
    (q : PLit × EClause pPlus ({} : LitTable))
    (h : (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus).run
      plusPruneXView = .prune ps)
    (hq : q ∈ ps.toList) :
    Entailed pPlus (({} : LitTable).decodeClause q.2.lits) :=
  plusPropWith_prune_reason_entailed pPlus ({} : LitTable) 0 1 2 hmemPlus
    plusPruneXView
    (boundsViewWF3 (DomC.bounds 0 10) (DomC.bounds 3 3) (DomC.bounds 5 8)
      (by simp [DomC.WF]) (by simp [DomC.WF]) (by simp [DomC.WF])) h hq

example (ps : Array (PLit × EClause pPlus ({} : LitTable)))
    (q : PLit × EClause pPlus ({} : LitTable))
    (h : (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus).run
      plusPruneXView = .prune ps)
    (hq : q ∈ ps.toList) :
    (plusPruneXView.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit
        = none ∧
      ∀ q' ∈ ({} : LitTable).decodeClause q.2.lits, q' ≠ q.1.lit →
        (plusPruneXView.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q'
          = some false :=
  plusPropWith_prune_lit_none pPlus ({} : LitTable) 0 1 2 hmemPlus
    plusPruneXView
    (boundsViewWF3 (DomC.bounds 0 10) (DomC.bounds 3 3) (DomC.bounds 5 8)
      (by simp [DomC.WF]) (by simp [DomC.WF]) (by simp [DomC.WF])) h hq

example :
    (plusPropWith pPlus ({} : LitTable) 0 1 2 hmemPlus).run missingView = .fix :=
  plusPropWith_run_fix_of_no_bounds pPlus ({} : LitTable) 0 1 2 hmemPlus
    missingView (by simp [missingView, mkGBox?, mkGArg?, argBounds?])

example (ec : EClause pMinGenEmpty ({} : LitTable))
    (h : (minGenPropWith pMinGenEmpty ({} : LitTable) [] (.slot 0)
      hmemMinGenEmpty).run genPruneView = .conflict ec) :
    Entailed pMinGenEmpty (({} : LitTable).decodeClause ec.lits) :=
  minGenPropWith_conflict_entailed pMinGenEmpty ({} : LitTable) [] (.slot 0)
    hmemMinGenEmpty genPruneView
    (by
      intro i hi
      have : i < 1 := by simpa [dcSlotsFull, DomIntArg.slots] using hi
      have h0 : i = 0 := by omega
      subst h0
      simp [dcSlotsFull, DomIntArg.slots, genPruneView, DomC.WF])
    h

example (ec : EClause pDiv ({} : LitTable))
    (h : (divPropWith pDiv ({} : LitTable) (.slot 0) (.slot 1) (.slot 2)
      hmemDiv).run divZeroView = .conflict ec) :
    Entailed pDiv (({} : LitTable).decodeClause ec.lits) :=
  divPropWith_conflict_entailed pDiv ({} : LitTable) (.slot 0) (.slot 1) (.slot 2)
    hmemDiv divZeroView
    (boundsViewWF3 (DomC.bounds 0 10) (DomC.bounds 0 0) (DomC.bounds 0 10)
      (by simp [DomC.WF]) (by simp [DomC.WF]) (by simp [DomC.WF])) h

/-- The standard search loop is available, but it hard-wires `propsOf`;
this reports baseline counters on small synthetic arithmetic problems as
evidence only.  Comparing a custom table needs the coordinator's wiring
in `Search.lean`. -/
def reportSearchBaseline : IO Unit := do
  let some st0 := initState pPlus ({} : LitTable) | fail "baseline: initState rejected plus"
  IO.println s!"baseline plus: props={st0.props.size} subs={st0.subs.size}"
  let (r, st) := coreSolveFull pTimes {} 10000
  let verdict := match r with
    | .sat _ => "sat"
    | .unsat => "unsat"
    | .gaveUp => "gaveUp"
  IO.println s!"baseline times: verdict={verdict} decisions={st.decisions} \
    propagations={st.propagations} conflicts={st.conflicts} learned={st.learned} \
    gaveUp={st.gaveUp}"

def run : IO UInt32 := do
  checkPlus
  checkMin
  checkMax
  checkAbs
  checkPairs
  checkGen
  checkTimes
  checkDiv
  checkMod
  checkMalformed
  checkDifferential
  reportSearchBaseline
  IO.println "ArithTest: OK"
  return 0

end Tests.Engine.ArithTest

open Tests.Engine.ArithTest in
def main : IO UInt32 := Tests.Engine.ArithTest.run
