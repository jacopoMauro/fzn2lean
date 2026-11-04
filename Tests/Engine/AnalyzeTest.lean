/-
N8 runtime test: first-UIP conflict analysis over concrete array-trail
states.  The checks cover

1. a level-0 conflict explained entirely by the initial domains
   (learned clause is empty, and the enumeration evaluator accepts it);
2. a resolution step through a stored reason clause, checked by enumerating
   `allAssigns p.domains`;
3. the no-claim failure path for an unexplained conflict literal;
4. an asserting result whose asserting literal occurs in the learned clause
   and whose backjump is below the current level;
5. a chain-clause step over two successive bound entries on one slot,
   checking both entailment and the prefix negations;
6. the documented `subsumeItems` identity fallback.

Run with:
  lake env lean --run Tests/Engine/AnalyzeTest.lean
-/
import LeanFzn.Engine.Analyze

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Analyze

/-! ## A small compiled-problem harness -/

def T : LitTable := {}

def mkP (ds : List Dom) (cs : List DomConstraint) : CompiledProblem DomConstraint :=
  { names := [], domains := ds, constraints := cs, objective := (), source := default,
    toStore := fun _ _ => none }

def litLe (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := true }

/-- `x > k`, the negative `intLe` literal. -/
def litGt (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := false }

def litNe (s : Nat) (k : Int) : Literal :=
  { atom := .intNe s k, positive := true }

/-- `x = k`, the negative `intNe` literal. -/
def litEqV (s : Nat) (k : Int) : Literal :=
  { atom := .intNe s k, positive := false }

def pl (i : Nat) (l : Literal) : PLit := { idx := i, lit := l }

def mkEntry (l : PLit) (lev slot : Nat) (prev : DomC) (r : ReasonRef) : Entry :=
  { lit := l, level := lev, reason := r, slot := slot, prev := prev }

/-- Assemble a state with empty queues, no propagators and no stored clauses. -/
def mkState (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (trail : Array Entry) (levelStart : Array Nat)
    (level : Nat) (changeIndex : Array (Array Nat))
    (reasons : Array (EClause p T)) : EngineState p T :=
  { table := T
    doms := doms
    trail := trail
    levelStart := levelStart
    level := level
    changeIndex := changeIndex
    db := {}
    reasons := reasons
    props := #[]
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := Array.replicate doms.size (0.0 : Float)
    activityHeap := #[]
    phases := #[]
    restarts := 0
    stats := {} }

/-- Boolean clause evaluator over one assignment. -/
def clauseEvalB (c : Clause) (a : Assignment) : Bool :=
  c.any fun l => l.eval a == some true

/-- Enumeration check: every accepted assignment satisfies `c`. -/
def entailedB (p : CompiledProblem DomConstraint) (c : Clause) : Bool :=
  (allAssigns p.domains).all fun a => !(accepts p a) || clauseEvalB c a

/-- Turn a successful enumeration check into the propositional contract. -/
theorem entailedB_sound {p : CompiledProblem DomConstraint} {c : Clause}
    (h : entailedB p c = true) : Entailed p c := by
  intro b hb hacc
  have hall := (List.all_eq_true.mp h) b hb
  rw [Bool.or_eq_true] at hall
  rcases hall with hrej | hsat
  · rw [hacc] at hrej
    simp at hrej
  · obtain ⟨l, hl, hev⟩ := List.any_eq_true.mp hsat
    exact ⟨l, hl, beq_iff_eq.mp hev⟩

/-- Build a proof-carrying clause from an enumeration check. -/
def ect (p : CompiledProblem DomConstraint) (ls : List Literal)
    (h : entailedB p ls = true) : EClause p T :=
  EClause.ofLiterals p T ls (entailedB_sound h)

/-- Decoded literals of the learned clause (empty when the analysis failed). -/
def learnedLits {p : CompiledProblem DomConstraint} (a : Analysis p T) : List Literal :=
  match a.learned with
  | none => []
  | some ec => ec.lits.toList.map PLit.decode

/-! ## Concrete domains -/

def d3 : Dom := ⟨.holes 0 3 []⟩
def d2 : Dom := ⟨.holes 0 2 []⟩

def i3 : DomC := .boundsHoles 0 3 #[]
def i2 : DomC := .boundsHoles 0 2 #[]
def iEmpty : DomC := .boundsHoles 1 0 #[]

/-! ## Case 1: level-0 conflict, all literals false initially -/

def p1 : CompiledProblem DomConstraint := mkP [⟨.holes 1 0 []⟩] []

def init1 : Array DomC := #[iEmpty]

def st1 : EngineState p1 T := mkState p1 T #[iEmpty] #[] #[0] 0 #[] #[]

/-- The negative `intNe` literal is false on the empty initial domain. -/
def c1 : EClause p1 T := ect p1 [litEqV 0 0] (by decide)

/-! ## Case 2: a resolution step through a stored reason clause -/

/-- `x < y`, both slots `0..3`. -/
def p2 : CompiledProblem DomConstraint := mkP [d3, d3] [.ltSlot 0 1]

def init2 : Array DomC := #[i3, i3]

/-- `y <= 0` at level 0 (slot 1). -/
def eY2 : Entry := mkEntry (pl 0 (litLe 1 0)) 0 1 i3 .decision

/-- `x <= 0` at level 1 (slot 0), justified by `x <= 0 or y > 0`. -/
def eX2 : Entry := mkEntry (pl 0 (litLe 0 0)) 1 0 i3 (.reason 0)

/-- The reason clause `x <= 0 or y > 0`, entailed because `x < y`. -/
def c2r : EClause p2 T := ect p2 [litLe 0 0, litGt 1 0] (by decide)

def st2 : EngineState p2 T :=
  mkState p2 T #[i3.applyLit (litLe 0 0), i3.applyLit (litLe 1 0)]
    #[eY2, eX2] #[0, 1] 1 #[#[1], #[0]] #[c2r]

/-- The conflict clause `x > 0 or y > 0`, false at `x = y = 0`. -/
def c2 : EClause p2 T := ect p2 [litGt 0 0, litGt 1 0] (by decide)

/-! ## Case 3: unexplained literal, no claim -/

/-- `x >= 1`, so `x > 0` is entailed but not false initially. -/
def p3 : CompiledProblem DomConstraint := mkP [d3] [.leConstLo 0 1]

def init3 : Array DomC := #[i3]

def st3 : EngineState p3 T := mkState p3 T #[i3] #[] #[0] 0 #[] #[]

def c3 : EClause p3 T := ect p3 [litGt 0 0] (by decide)

/-! ## Case 4: asserting decision at level 1 -/

def p4 : CompiledProblem DomConstraint := p3

def init4 : Array DomC := #[i3]

def st4 : EngineState p4 T :=
  mkState p4 T #[i3.applyLit (litLe 0 0)]
    #[mkEntry (pl 0 (litLe 0 0)) 1 0 i3 .decision] #[0, 0] 1 #[#[0]] #[]

def c4 : EClause p4 T := ect p4 [litGt 0 0] (by decide)

/-! ## Case 5: chain clause over two bound entries on slot 0 -/

/-- `x < y`, both slots `0..2`. -/
def p5 : CompiledProblem DomConstraint := mkP [d2, d2] [.ltSlot 0 1]

def init5 : Array DomC := #[i2, i2]

/-- `y <= 0` at level 0 (slot 1). -/
def eY5 : Entry := mkEntry (pl 0 (litLe 1 0)) 0 1 i2 .decision

/-- First slot-0 change: `x <= 1` at level 0. -/
def e05 : Entry := mkEntry (pl 0 (litLe 0 1)) 0 0 i2 .decision

/-- Second slot-0 change: `x <= 0` at level 1, justified by `x <= 0 or y > 0`. -/
def e15 : Entry :=
  mkEntry (pl 0 (litLe 0 0)) 1 0 (i2.applyLit (litLe 0 1)) (.reason 0)

def c5r : EClause p5 T := ect p5 [litLe 0 0, litGt 1 0] (by decide)

def st5 : EngineState p5 T :=
  mkState p5 T #[i2.applyLit (litLe 0 0), i2.applyLit (litLe 1 0)]
    #[eY5, e05, e15] #[0, 2] 1 #[#[1, 2], #[0]] #[c5r]

/-- The conflict clause `x != 0 or y != 0`, false at `x = y = 0`. -/
def c5 : EClause p5 T := ect p5 [litNe 0 0, litNe 1 0] (by decide)

/-! ## Case 6: the documented subsumption fallback -/

def itA : CItem := { lit := litLe 0 1, pos := 0, level := 0, cidx := 0 }
def itB : CItem := { lit := litLe 0 2, pos := 1, level := 0, cidx := 1 }

def items6 : Array CItem := #[itA, itB]

/-! ## Compile-time spot checks -/

example : (analyze p1 T init1 st1 c1 8).ok = true := by decide +kernel

example : ∃ ec, (analyze p2 T init2 st2 c2 8).learned = some ec ∧
    Entailed p2 (T.decodeClause ec.lits) :=
  analyze_sound (by decide +kernel)

example : (analyze p3 T init3 st3 c3 8).ok = false := by decide +kernel

example : ∀ ec l, (analyze p4 T init4 st4 c4 8).learned = some ec →
    (analyze p4 T init4 st4 c4 8).asserting = some l →
      l.lit ∈ ec.lits.toList.map PLit.decode := by
  intro ec l hlearned hassserting
  exact analyze_asserting_mem hlearned hassserting


/-! ## Runtime checks -/

def check (name : String) (cond : Bool) : IO Nat :=
  if cond then
    pure 0
  else do
    IO.eprintln s!"FAIL: {name}"
    pure 1

def main : IO Unit := do
  let mut fails := 0

  -- Case 1
  let a1 := analyze p1 T init1 st1 c1 8
  fails := fails + (← check "case1 ok" (a1.ok == true))
  fails := fails + (← check "case1 learned is some" a1.learned.isSome)
  fails := fails + (← check "case1 learned clause empty"
    (match a1.learned with
     | some ec => ec.lits.isEmpty
     | none => false))
  fails := fails + (← check "case1 decoded lits empty" (learnedLits a1 == []))
  fails := fails + (← check "case1 enumeration entailed"
    (entailedB p1 (learnedLits a1) == true))
  fails := fails + (← check "case1 backjump zero" (a1.backjump == 0))
  fails := fails + (← check "case1 no asserting" (a1.asserting == none))

  -- Case 2
  let a2 := analyze p2 T init2 st2 c2 8
  fails := fails + (← check "case2 ok" (a2.ok == true))
  fails := fails + (← check "case2 learned is some" a2.learned.isSome)
  fails := fails + (← check "case2 learned lits are y > 0 twice"
    (learnedLits a2 == [litGt 1 0, litGt 1 0]))
  fails := fails + (← check "case2 enumeration entailed"
    (entailedB p2 (learnedLits a2) == true))
  fails := fails + (← check "case2 backjump zero" (a2.backjump == 0))

  -- Case 3
  let a3 := analyze p3 T init3 st3 c3 8
  fails := fails + (← check "case3 fails" (a3.ok == false))
  fails := fails + (← check "case3 no learned clause" a3.learned.isNone)
  fails := fails + (← check "case3 has a reason" (!a3.why.isEmpty))

  -- Case 4
  let a4 := analyze p4 T init4 st4 c4 8
  fails := fails + (← check "case4 ok" (a4.ok == true))
  fails := fails + (← check "case4 asserting is x > 0"
    (a4.asserting == some (pl 0 (litGt 0 0))))
  fails := fails + (← check "case4 learned is x > 0"
    (learnedLits a4 == [litGt 0 0]))
  fails := fails + (← check "case4 asserting literal in learned clause"
    (match a4.asserting with
     | some l => (learnedLits a4).contains l.lit
     | none => false))
  fails := fails + (← check "case4 backjump below current level"
    (a4.backjump < st4.level))
  fails := fails + (← check "case4 enumeration entailed"
    (entailedB p4 (learnedLits a4) == true))

  -- Case 5
  let a5 := analyze p5 T init5 st5 c5 8
  fails := fails + (← check "case5 ok" (a5.ok == true))
  fails := fails + (← check "case5 learned lits"
    (learnedLits a5 == [litNe 1 0, litGt 0 1, litGt 1 0]))
  fails := fails + (← check "case5 learned clause keeps the first chain negation"
    ((learnedLits a5).contains (litGt 0 1)))
  fails := fails + (← check "case5 chain clause has both prefix negations"
    (let c := (chainReasonLits st5 0 2 (litNe 0 0)).toList
     c.contains (litGt 0 1) && c.contains (litGt 0 0)))
  fails := fails + (← check "case5 enumeration entailed"
    (entailedB p5 (learnedLits a5) == true))

  -- Case 6 (`subsumeItems` is the documented identity fallback)
  fails := fails + (← check "case6 subsumeItems keeps the item list"
    (subsumeItems items6 == items6))
  fails := fails + (← check "case6 subsumeItems keeps both literals"
    ((subsumeItems items6).toList.map (fun it => it.lit) ==
      [litLe 0 1, litLe 0 2]))

  if fails == 0 then
    IO.println "AnalyzeTest: all checks passed"
  else do
    IO.eprintln s!"AnalyzeTest: {fails} check(s) failed"
    IO.Process.exit 1

end Tests.Engine.Analyze

def main (_args : List String) : IO UInt32 := do
  Tests.Engine.Analyze.main
  pure 0
