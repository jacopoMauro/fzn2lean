/-
Runtime tests for the dedicated element propagators in
`LeanFzn/Engine/Props/Element.lean`.

Run with:
  lake env lean --run Tests/Engine/Props/ElementTest.lean

Coverage: the constant-table `array_int_element` propagator, the
variable-table `array_var_int_element` link in both directions, the
Boolean variable-table `array_var_bool_element` propagator, malformed
inputs, runtime entailment over all accepted assignments, and a local
differential table comparing the dedicated builders with the generic
checker (`propsOfTest` versus `Search.propsOf` / `propCheckV2With`) plus
two synthetic search instances.
-/
import LeanFzn.Engine.Props.Element
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration
open LeanFzn.Engine

namespace Tests.Engine.Props.ElementTest

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"ElementTest FAIL: {msg}"
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

def conflictClause? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option Clause
  | .conflict c => some (T.decodeClause c.lits)
  | _ => none

def pruneLits? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option (List Literal)
  | .prune ps => some (ps.toList.map fun q => q.1.lit)
  | _ => none

def prunePairs? {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Option (List (Literal × Clause))
  | .prune ps => some (ps.toList.map fun q => (q.1.lit, T.decodeClause q.2.lits))
  | _ => none

/-- Compare two propagator outputs by kind, decoded clauses and literals. -/
def sameOutput {p : CompiledProblem DomConstraint} {T : LitTable}
    (a b : PropOut p T) : Bool :=
  conflictClause? a == conflictClause? b &&
  pruneLits? a == pruneLits? b &&
  prunePairs? a == prunePairs? b &&
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

/-- One expected prune batch, with exact literal/reason pairs. -/
def checkPruneBatch (label : String) (p : CompiledProblem DomConstraint)
    (view : EngineView) (out : PropOut p ({} : LitTable))
    (expected : List (Literal × Clause)) : IO Unit :=
  match prunePairs? out with
  | some actual => do
      check s!"{label}: pairs {repr actual} expected {repr expected}" (actual == expected)
      for q in actual do
        checkLitNone label view q.1
        checkAllFalse label view (q.2.filter (fun l => l != q.1))
        checkClauseEntailedRuntime label p q.2
  | none => fail s!"{label}: expected .prune, got another output kind"

def checkFix {p : CompiledProblem DomConstraint} {T : LitTable}
    (label : String) (out : PropOut p T) : IO Unit :=
  check s!"{label}: expected .fix" (isFix out)

/-! ## Concrete domains and views -/

def dom0_10 : Dom := ⟨.holes 0 10 []⟩
def dom0_30 : Dom := ⟨.holes 0 30 []⟩
def domBool : Dom := ⟨.general [.bool false, .bool true]⟩
def domBoolTrue : Dom := ⟨.general [.bool true]⟩
def domBoolFalse : Dom := ⟨.general [.bool false]⟩

def view2 (d0 d1 : DomC) : EngineView := { doms := #[d0, d1], level := 0 }
def view3 (d0 d1 d2 : DomC) : EngineView := { doms := #[d0, d1, d2], level := 0 }
def view5 (d0 d1 d2 d3 d4 : DomC) : EngineView :=
  { doms := #[d0, d1, d2, d3, d4], level := 0 }

/-! ## 1-2. `array_int_element [10, 20, 30]` -/

def pAie : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.arrayIntElementSlot [10, 20, 30] 0 1]

theorem hmemAie : DomConstraint.arrayIntElementSlot [10, 20, 30] 0 1 ∈ pAie.constraints := by
  simp [pAie, mkProblem]

def aieOut (view : EngineView) : PropOut pAie ({} : LitTable) :=
  (arrayIntElementPropWith pAie ({} : LitTable) [10, 20, 30] 0 1 hmemAie).run view

/-- Index pruning by result support: result fixed to 20 removes 0, 1, 3. -/
def checkAieIndexPrune : IO Unit := do
  let view := view2 (DomC.bounds 0 3) (DomC.bounds 20 20)
  checkPruneBatch "aie index prune" pAie view (aieOut view)
    [ (posNe 0 0, [posNe 0 0])
    , (posNe 0 1, [posNe 0 1, negNe 1 10])
    , (posNe 0 3, [posNe 0 3, negNe 1 30]) ]

/-- The hull-image values absent from `[10, 20, 30]` are removed. -/
def aieHullExpected : List (Literal × Clause) :=
  ([11, 12, 13, 14, 15, 16, 17, 18, 19,
    21, 22, 23, 24, 25, 26, 27, 28, 29] : List Int).map fun w =>
      (posNe 1 w, [posNe 1 w, posLe 0 0, negLe 0 3])

/-- Non-contiguous index domain and a result domain that excludes entries. -/
def checkAieNonContiguous : IO Unit := do
  let view := view2 (DomC.boundsHoles 1 4 #[2]) (DomC.bounds 10 10)
  checkPruneBatch "aie non-contiguous index" pAie view (aieOut view)
    [ (posNe 0 3, [posNe 0 3, negNe 1 30])
    , (posNe 0 4, [posNe 0 4]) ]
  -- The result keeps 10 and 30 but excludes 20, so index 2 is removed;
  -- the remaining result values outside the table image are hull-pruned.
  let viewHoles := view2 (DomC.bounds 1 3) (DomC.boundsHoles 10 30 #[20])
  checkPruneBatch "aie non-contiguous result" pAie viewHoles (aieOut viewHoles)
    ((posNe 0 2, [posNe 0 2, negNe 1 20]) :: aieHullExpected)

/-- Fixed-index result propagation: prune the result to the table entry. -/
def checkAieFixedPrune : IO Unit := do
  let view := view2 (DomC.bounds 2 2) (DomC.bounds 15 25)
  checkPruneBatch "aie fixed-index prune" pAie view (aieOut view)
    [ (posLe 1 20, [posLe 1 20, posNe 0 2])
    , (negLe 1 19, [negLe 1 19, posNe 0 2]) ]

/-- Fixed-index conflict: the table entry is absent from the result. -/
def checkAieFixedConflict : IO Unit := do
  let view := view2 (DomC.bounds 2 2) (DomC.bounds 0 10)
  checkConflict "aie fixed-index conflict" pAie view (aieOut view)
    [posNe 0 2, negNe 1 20]

/-- Out-of-range fixed index is a conflict. -/
def checkAieOutOfRange : IO Unit := do
  let view := view2 (DomC.bounds 4 4) (DomC.bounds 0 30)
  checkConflict "aie out-of-range index" pAie view (aieOut view) [posNe 0 4]
  let view0 := view2 (DomC.bounds 0 0) (DomC.bounds 0 30)
  checkConflict "aie index zero" pAie view0 (aieOut view0) [posNe 0 0]

/-- A satisfiable loose box pruned to the hull image. -/
def checkAieFix : IO Unit := do
  let view := view2 (DomC.bounds 1 3) (DomC.bounds 10 30)
  checkPruneBatch "aie hull value prune" pAie view (aieOut view) aieHullExpected
  let viewFixed := view2 (DomC.bounds 2 2) (DomC.bounds 20 20)
  checkFix "aie fixed satisfiable fix" (aieOut viewFixed)

/-- The result-width guard leaves a wide result domain to bounds only. -/
def checkAieWideGuard : IO Unit := do
  let view := view2 (DomC.bounds 1 3) (DomC.bounds 0 300)
  checkPruneBatch "aie wide result guard" pAie view (aieOut view)
    [ (negLe 1 9, [negLe 1 9, posLe 0 0, negLe 0 3])
    , (posLe 1 30, [posLe 1 30, posLe 0 0, negLe 0 3]) ]

/-- With holes in the index domain the hull-bounds batch is skipped;
the value batch is already skipped by the wide result. -/
def checkAieHolesGuard : IO Unit := do
  let view := view2 (DomC.boundsHoles 1 3 #[2]) (DomC.bounds 0 300)
  checkFix "aie index-holes guard" (aieOut view)

/-- A table image wider than 192 values is left to the other rules. -/
def pAieWide : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10] [.arrayIntElementSlot [0, 2, 250] 0 1]

theorem hmemAieWide : DomConstraint.arrayIntElementSlot [0, 2, 250] 0 1 ∈
    pAieWide.constraints := by
  simp [pAieWide, mkProblem]

def aieWideOut (view : EngineView) : PropOut pAieWide ({} : LitTable) :=
  (arrayIntElementPropWith pAieWide ({} : LitTable) [0, 2, 250] 0 1 hmemAieWide).run view

def checkAieWideImageGuard : IO Unit := do
  let view := view2 (DomC.bounds 1 3) (DomC.bounds 0 300)
  checkFix "aie wide image guard" (aieWideOut view)

/-- Empty index or result domains make the stage-1 propagator a no-op. -/
def checkAieMalformed : IO Unit := do
  let view := view2 (DomC.bounds 1 0) (DomC.bounds 0 10)
  checkFix "aie empty index" (aieOut view)
  let viewK := view2 (DomC.bounds 1 3) (DomC.bounds 1 0)
  checkFix "aie empty result" (aieOut viewK)

/-! ## 3. `array_var_int_element [2, 3, 4]` -/

def pAvie : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, dom0_10, dom0_10, dom0_10]
    [.arrayVarIntElementSlot [2, 3, 4] 0 1]

theorem hmemAvie : DomConstraint.arrayVarIntElementSlot [2, 3, 4] 0 1 ∈
    pAvie.constraints := by
  simp [pAvie, mkProblem]

def avieOut (view : EngineView) : PropOut pAvie ({} : LitTable) :=
  (arrayVarIntElementPropWith pAvie ({} : LitTable) [2, 3, 4] 0 1 hmemAvie).run view

/-- Fixed index 2 selects slot 3; the result is pruned to the slot's hull. -/
def checkAvieFixedPruneK : IO Unit := do
  let view := view5 (DomC.bounds 2 2) (DomC.bounds 5 9) (DomC.bounds 0 10)
    (DomC.bounds 5 8) (DomC.bounds 0 10)
  checkPruneBatch "avie fixed-index result prune" pAvie view (avieOut view)
    [ (posNe 1 9, [posNe 1 9, posNe 0 2, negNe 3 9]) ]

/-- Fixed index 2 selects slot 3; the selected slot is pruned to the result. -/
def checkAvieFixedPruneJ : IO Unit := do
  let view := view5 (DomC.bounds 2 2) (DomC.bounds 5 8) (DomC.bounds 0 10)
    (DomC.bounds 5 9) (DomC.bounds 0 10)
  checkPruneBatch "avie fixed-index slot prune" pAvie view (avieOut view)
    [ (posNe 3 9, [posNe 3 9, posNe 0 2, negNe 1 9]) ]

/-- Fixed index with a value conflict between the selected slot and result. -/
def checkAvieFixedConflict : IO Unit := do
  let view := view5 (DomC.bounds 2 2) (DomC.boundsHoles 1 9 #[7])
    (DomC.bounds 0 10) (DomC.bounds 7 7) (DomC.bounds 0 10)
  checkConflict "avie fixed-index conflict" pAvie view (avieOut view)
    [posNe 3 7, posNe 0 2, negNe 1 7]

/-- Index values whose selected slot is disjoint from the result. -/
def checkAvieIndexPrune : IO Unit := do
  let view := view5 (DomC.bounds 1 3) (DomC.bounds 20 20)
    (DomC.bounds 20 20) (DomC.bounds 30 30) (DomC.bounds 40 40)
  checkPruneBatch "avie index prune" pAvie view (avieOut view)
    [ (posNe 0 2, [posNe 0 2, negLe 1 20, posLe 3 29])
    , (posNe 0 3, [posNe 0 3, negLe 1 20, posLe 4 39]) ]

/-- A satisfiable fixed-index link with equal domains. -/
def checkAvieFix : IO Unit := do
  let view := view5 (DomC.bounds 2 2) (DomC.bounds 5 9) (DomC.bounds 0 10)
    (DomC.bounds 5 9) (DomC.bounds 0 10)
  checkFix "avie satisfiable fix" (avieOut view)

/-- Duplicate table slots remain sound and propagate the link. -/
def pAvieDup : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, dom0_10, dom0_10, dom0_10, dom0_10]
    [.arrayVarIntElementSlot [2, 2, 4] 0 1]

theorem hmemAvieDup : DomConstraint.arrayVarIntElementSlot [2, 2, 4] 0 1 ∈
    pAvieDup.constraints := by
  simp [pAvieDup, mkProblem]

def avieDupOut (view : EngineView) : PropOut pAvieDup ({} : LitTable) :=
  (arrayVarIntElementPropWith pAvieDup ({} : LitTable) [2, 2, 4] 0 1 hmemAvieDup).run view

def checkAvieDuplicate : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bounds 5 9) (DomC.bounds 5 8)
    (DomC.bounds 0 10) (DomC.bounds 0 10)
  checkPruneBatch "avie duplicate slots" pAvieDup view (avieDupOut view)
    [ (posNe 1 9, [posNe 1 9, posNe 0 1, negNe 2 9]) ]

/-- A Boolean array slot is malformed for the integer family: no-op. -/
def checkAvieMalformed : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bounds 5 9) (DomC.bool 3)
    (DomC.bounds 0 10) (DomC.bounds 0 10)
  checkFix "avie Boolean array slot" (avieOut view)
  let viewEmpty := view5 (DomC.bounds 1 1) (DomC.bounds 1 0) (DomC.bounds 0 10)
    (DomC.bounds 0 10) (DomC.bounds 0 10)
  checkFix "avie empty result bounds" (avieOut viewEmpty)

/-! ## 4. `array_var_bool_element [2, 3, 4]` -/

def pAvbe : CompiledProblem DomConstraint :=
  mkProblem [dom0_10, domBool, domBool, domBool, domBool]
    [.arrayVarBoolElementSlot [2, 3, 4] 0 1]

theorem hmemAvbe : DomConstraint.arrayVarBoolElementSlot [2, 3, 4] 0 1 ∈
    pAvbe.constraints := by
  simp [pAvbe, mkProblem]

def avbeOut (view : EngineView) : PropOut pAvbe ({} : LitTable) :=
  (arrayVarBoolElementPropWith pAvbe ({} : LitTable) [2, 3, 4] 0 1 hmemAvbe).run view

/-- Fixed index 1 selects slot 2 fixed to `true`; the result is fixed. -/
def checkAvbeFixedTrue : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bool 3) (DomC.bool 2)
    (DomC.bool 3) (DomC.bool 3)
  checkPruneBatch "avbe selected true" pAvbe view (avbeOut view)
    [ (posBool 1 true, [posNe 0 1, posBool 2 false, posBool 1 true]) ]

/-- The same with a selected `false` entry. -/
def checkAvbeFixedFalse : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bool 3) (DomC.bool 1)
    (DomC.bool 3) (DomC.bool 3)
  checkPruneBatch "avbe selected false" pAvbe view (avbeOut view)
    [ (posBool 1 false, [posNe 0 1, posBool 2 true, posBool 1 false]) ]

/-- A fixed result propagates into the selected Boolean slot. -/
def checkAvbeResultFixed : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bool 2) (DomC.bool 3)
    (DomC.bool 3) (DomC.bool 3)
  checkPruneBatch "avbe result fixed" pAvbe view (avbeOut view)
    [ (posBool 2 true, [posNe 0 1, posBool 1 false, posBool 2 true]) ]

/-- Fixed index with opposite fixed Booleans is a conflict. -/
def checkAvbeConflict : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bool 2) (DomC.bool 1)
    (DomC.bool 3) (DomC.bool 3)
  checkConflict "avbe opposite fixed" pAvbe view (avbeOut view)
    [posNe 0 1, posBool 1 false, posBool 2 true]
  let viewEq := view5 (DomC.bounds 1 1) (DomC.bool 2) (DomC.bool 2)
    (DomC.bool 3) (DomC.bool 3)
  checkFix "avbe equal fixed" (avbeOut viewEq)

/-- General index pruning: out-of-range indices and opposite fixed entries. -/
def checkAvbeIndexPrune : IO Unit := do
  let view := view5 (DomC.bounds 0 4) (DomC.bool 2) (DomC.bool 2)
    (DomC.bool 1) (DomC.bool 3)
  checkPruneBatch "avbe index prune" pAvbe view (avbeOut view)
    [ (posNe 0 0, [posNe 0 0])
    , (posNe 0 2, [posNe 0 2, posBool 1 false, posBool 3 true])
    , (posNe 0 4, [posNe 0 4]) ]

/-- A non-Boolean result or array slot is malformed: no-op. -/
def checkAvbeMalformed : IO Unit := do
  let view := view5 (DomC.bounds 1 1) (DomC.bounds 0 1) (DomC.bool 3)
    (DomC.bool 3) (DomC.bool 3)
  checkFix "avbe integer result" (avbeOut view)
  let viewSlot := view5 (DomC.bounds 1 1) (DomC.bool 3) (DomC.bounds 0 1)
    (DomC.bool 3) (DomC.bool 3)
  checkFix "avbe integer array slot" (avbeOut viewSlot)

/-! ## 5. Runtime entailment coverage

The `checkConflict` and `checkPruneBatch` helpers above run
`checkClauseEntailedRuntime` on every emitted conflict clause and every
emitted prune reason.  They also check the exact `evalLit` facts on the
current view.  The fixtures therefore cover the full entailment surface
of all three builders. -/

/-! ## 6. Local differential: dedicated builders vs `Search.propsOf` -/

/-- Test-local adapters: dedicated element builders, generic checker for
the rest.  This mirrors `Search.propsOf` for the three element families. -/
def propsOfTest (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    match hx : x.1 with
    | .arrayIntElementSlot xs i k =>
        arrayIntElementPropWith p T xs i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarIntElementSlot is i k =>
        arrayVarIntElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | .arrayVarBoolElementSlot is i k =>
        arrayVarBoolElementPropWith p T is i k
          (by simpa [hx] using List.mem_toArray.mp x.2)
    | dc =>
        propCheckV2With p T dc init
          (by
            have h := hinit x.1 (List.mem_toArray.mp x.2)
            rw [hx] at h
            exact h)
          (by simpa [hx] using List.mem_toArray.mp x.2)

/-- The fully generic table: every constraint goes through
`propCheckV2With`. -/
def propsOfGeneric (p : CompiledProblem DomConstraint) (T : LitTable) (init : Array DomC)
    (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) :
    Array (PropV2 p T) :=
  p.constraints.toArray.attach.map fun x =>
    propCheckV2With p T x.1 init
      (hinit x.1 (List.mem_toArray.mp x.2))
      (List.mem_toArray.mp x.2)

/-- Output kind as a small tag. -/
def outTag {p : CompiledProblem DomConstraint} {T : LitTable} :
    PropOut p T → Nat
  | .fix => 0
  | .conflict _ => 1
  | .prune _ => 2

/-- Compare the dedicated table with the generic table on one view. -/
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
        check s!"{label}: prop {i} verdict ({outTag t} vs {outTag g})"
          (outTag t == outTag g)
    | _, _ => fail s!"{label}: missing propagator {i}"

/-! ### Fixed-view fixture agreement -/

theorem hreadyAie : initReady pAie (convInit pAie.domains) = true := by
  simp [initReady, pAie, mkProblem, convInit, dom0_10, dcSlotsFull, slotReadyB,
    DomC.ofDom?]

theorem hreadyAvie : initReady pAvie (convInit pAvie.domains) = true := by
  simp [initReady, pAvie, mkProblem, convInit, dom0_10, dcSlotsFull, slotReadyB,
    DomC.ofDom?]

theorem hreadyAvbe : initReady pAvbe (convInit pAvbe.domains) = true := by
  simp [initReady, pAvbe, mkProblem, convInit, dom0_10, domBool, dcSlotsFull,
    slotReadyB, DomC.ofDom?, boolFold]

def aieSatView : EngineView := view2 (DomC.bounds 2 2) (DomC.bounds 20 20)
def aieUnsatView : EngineView := view2 (DomC.bounds 2 2) (DomC.bounds 10 10)
def avieSatView : EngineView :=
  view5 (DomC.bounds 2 2) (DomC.bounds 7 7) (DomC.bounds 0 0)
    (DomC.bounds 7 7) (DomC.bounds 0 0)
def avieUnsatView : EngineView :=
  view5 (DomC.bounds 2 2) (DomC.bounds 7 7) (DomC.bounds 0 0)
    (DomC.bounds 8 8) (DomC.bounds 0 0)
def avbeSatView : EngineView :=
  view5 (DomC.bounds 1 1) (DomC.bool 2) (DomC.bool 2)
    (DomC.bool 1) (DomC.bool 1)
def avbeUnsatView : EngineView :=
  view5 (DomC.bounds 1 1) (DomC.bool 2) (DomC.bool 1)
    (DomC.bool 1) (DomC.bool 1)

def checkDifferentialFixtures : IO Unit := do
  checkPropTableAgreement "aie fixed sat" pAie (convInit pAie.domains)
    (initReady_spec hreadyAie) aieSatView
  checkPropTableAgreement "aie fixed unsat" pAie (convInit pAie.domains)
    (initReady_spec hreadyAie) aieUnsatView
  checkPropTableAgreement "avie fixed sat" pAvie (convInit pAvie.domains)
    (initReady_spec hreadyAvie) avieSatView
  checkPropTableAgreement "avie fixed unsat" pAvie (convInit pAvie.domains)
    (initReady_spec hreadyAvie) avieUnsatView
  checkPropTableAgreement "avbe fixed sat" pAvbe (convInit pAvbe.domains)
    (initReady_spec hreadyAvbe) avbeSatView
  checkPropTableAgreement "avbe fixed unsat" pAvbe (convInit pAvbe.domains)
    (initReady_spec hreadyAvbe) avbeUnsatView

/-! ### Synthetic search instances -/

/-- A test-local copy of `Search.initState` parameterized by the
propagator table builder, so the differential can compare the dedicated
table against a fully generic one. -/
def initStateWith
    (mkProps : (p : CompiledProblem DomConstraint) → (T : LitTable) → (init : Array DomC) →
      (hinit : ∀ dc ∈ p.constraints, ∀ s ∈ dcSlotsFull dc,
        DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty)) →
      Array (PropV2 p T))
    (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  if !gateOkFast (propagationProblem p) then none
  else
    match convertDomains p.domains with
    | none => none
    | some doms =>
        if hready : initReady p doms = true then
          let hinitAll := initReady_spec hready
          let props := mkProps p T doms hinitAll
          let st : EngineState p T :=
            { table := T
              doms := doms
              trail := #[]
              levelStart := #[0]
              level := 0
              changeIndex := Array.replicate doms.size (#[] : Array Nat)
              db := {}
              reasons := #[]
              props := props
              subs := #[]
              queueHigh := #[]
              queueLow := #[]
              inQueue := ByteArray.empty
              activity := Array.replicate doms.size (0.0 : Float)
              activityHeap := #[]
              phases := #[]
              restarts := 0
              stats := {} }
          let st := registerProps st
          let st := (List.range props.size).foldl (fun st i => enqueueProp st i) st
          some st
        else none

def initStateTest (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  initStateWith propsOfTest p T

def initStateGeneric (p : CompiledProblem DomConstraint) (T : LitTable) :
    Option (EngineState p T) :=
  initStateWith propsOfGeneric p T

/-- The `coreSolveFull` body with a chosen propagator table. -/
def coreSolveWith
    (initFn : (p : CompiledProblem DomConstraint) → (T : LitTable) → Option (EngineState p T))
    (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult × EngineStats :=
  let T : LitTable := {}
  match initFn p T with
  | none => (.gaveUp, { gaveUp := 1 })
  | some st0 =>
      let prio := annotPrioArray p
      let orders := LeanFzn.Engine.configOrders p o
      match addSeedClauses p T st0 with
      | (st, some _) =>
          let st := { st with stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
          (.unsat, st.stats)
      | (st, none) =>
          match st.db.emptyConflict? with
          | some _ => (.unsat, st.stats)
          | none =>
              let (db, out) := st.db.propagateUnits p T st.doms
              match out with
              | .none =>
                  let st := { st with db := db }
                  let (r, st) := search p T st.doms o prio orders st #[] fuel
                  (r, st.stats)
              | .prune ps =>
                  let st := { st with db := db }
                  let (r, st) := search p T st.doms o prio orders st
                    (pushClausePrunes #[] ps) fuel
                  (r, st.stats)
              | .conflict ec _ =>
                  let a := analyze p T st.doms st ec fuel
                  let st := { st with db := db }
                  if !a.ok then (.gaveUp, { st.stats with gaveUp := 1 })
                  else
                    match a.learned with
                    | none => (.gaveUp, { st.stats with gaveUp := 1 })
                    | some lc =>
                        if lc.lits.isEmpty then (.unsat, st.stats)
                        else (.gaveUp, { st.stats with gaveUp := 1 })

def coreSolveTest (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveWith initStateTest p o fuel

def coreSolveGeneric (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveWith initStateGeneric p o fuel

def verdictName : CoreResult → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .gaveUp => "gaveUp"

/-- A loose constant-table instance: the dedicated table propagates the
index and then the result, while the generic checker waits for both
slots to be fixed. -/
def pDiffAie : CompiledProblem DomConstraint :=
  mkProblem [⟨.holes 0 3 []⟩, ⟨.holes 0 30 []⟩]
    [.arrayIntElementSlot [10, 20, 30] 0 1]

/-- A fixed Boolean-element conflict: both tables report `unsat`. -/
def pDiffAvbeBad : CompiledProblem DomConstraint :=
  mkProblem
    [⟨.holes 1 1 []⟩, ⟨.general [.bool true]⟩, ⟨.general [.bool false]⟩]
    [.arrayVarBoolElementSlot [2] 0 1]

/-- Run both tables on a synthetic instance and compare verdicts and
decision counts. -/
def checkSearchDifferential (label : String)
    (p : CompiledProblem DomConstraint) (expectFewer : Bool) : IO Unit := do
  let o : SearchConfig := { var := .minc, val := .act }
  let fuel := 10000
  let (rg, sg) := coreSolveGeneric p o fuel
  let (rt, st) := coreSolveTest p o fuel
  check s!"{label}: verdict agreement ({verdictName rt} vs {verdictName rg})"
    (verdictName rt == verdictName rg)
  if expectFewer then
    check s!"{label}: dedicated needs fewer decisions (dedicated {st.decisions}, generic {sg.decisions})"
      (st.decisions < sg.decisions)
  IO.println s!"  element differential {label}: generic={verdictName rg} \
(decisions={sg.decisions}, propagations={sg.propagations}, conflicts={sg.conflicts}) \
dedicated={verdictName rt} (decisions={st.decisions}, propagations={st.propagations}, \
conflicts={st.conflicts})"

def checkSearchDifferentials : IO Unit := do
  checkSearchDifferential "element loose" pDiffAie true
  checkSearchDifferential "element bool bad" pDiffAvbeBad false

/-! ## Entry point -/

def run : IO UInt32 := do
  checkAieIndexPrune
  checkAieNonContiguous
  checkAieFixedPrune
  checkAieFixedConflict
  checkAieOutOfRange
  checkAieFix
  checkAieWideGuard
  checkAieHolesGuard
  checkAieWideImageGuard
  checkAieMalformed
  checkAvieFixedPruneK
  checkAvieFixedPruneJ
  checkAvieFixedConflict
  checkAvieIndexPrune
  checkAvieFix
  checkAvieDuplicate
  checkAvieMalformed
  checkAvbeFixedTrue
  checkAvbeFixedFalse
  checkAvbeResultFixed
  checkAvbeConflict
  checkAvbeIndexPrune
  checkAvbeMalformed
  checkDifferentialFixtures
  checkSearchDifferentials
  IO.println "ElementTest: OK"
  return 0

end Tests.Engine.Props.ElementTest

open Tests.Engine.Props.ElementTest in
def main : IO UInt32 := Tests.Engine.Props.ElementTest.run
