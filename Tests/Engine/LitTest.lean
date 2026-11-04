/-
Concrete checks for the literal layer (`LeanFzn.Engine.Lit`).

Build/run (from the repository root, under the shared build lock):

  lake env lean Tests/Engine/LitTest.lean
  lake env lean --run Tests/Engine/LitTest.lean

The file is proof-hole free; `#eval` covers the intern table, the packed
negation, the decoded-clause laws, and the syntactic implication test, while
`main` re-checks the same facts at runtime and exits non-zero on failure.
-/
import LeanFzn.Engine.Lit

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.LitTest

/-- An empty table. -/
def T0 : LitTable := {}

/-- The empty table after interning `posLe 0 5`. -/
def T1 : LitTable := (T0.intern (posLe 0 5)).2

/-- Three representative literals (order, order-negation, Boolean). -/
def sample : Array Literal := #[posLe 0 5, negLe 1 3, posBool 2 true]

/-- A negative Boolean literal (local helper; the engine normalizes these
away, but the implication test must still be sound on them). -/
def negBool (s : Nat) (b : Bool) : Literal := ⟨.boolEq s b, false⟩

/-! ### Compile-time checks of the public API -/

#check EClause.ofLits
#check LitTable.decodeClause_canonical
#check EClause.reindex
#check resolve_entailed
#check entailed_nil_unsat
#check Entailed_mono
#check litImpliesNot_sound
#check LitTable.intern_fst_lit
#check LitTable.intern_existing
#check LitTable.intern_append_only
#check LitTable.intern_size
#check LitTable.intern_wf
#check LitTable.intern_tableWF
#check LitTable.decode_pLit
#check LitTable.decode_negate
#check LitTable.decodeClause_internArray
#check LitTable.decodeClause_internArray_snd
#check LitTable.internArray_lits
#check LitTable.internArray_append_only
#check LitTable.internArray_tableWF
#check LitTable.internArray_wf

/-- The intern laws instantiated at the empty table. -/
example : (T0.intern (posLe 0 5)).1.lit = posLe 0 5 :=
  LitTable.intern_fst_lit T0 (posLe 0 5)

example : (T0.intern (posLe 0 5)).1 = ⟨0, posLe 0 5⟩ := by
  rw [LitTable.intern_of_get?_none (T := T0) (l := posLe 0 5) (by simp [T0])]
  simp [T0]

/-- The decoded clause of an interned array is exactly the input list. -/
example : (T0.internArray sample).2.decodeClause (T0.internArray sample).1 =
    sample.toList :=
  LitTable.decodeClause_internArray_snd T0 sample

/-- Resolution and entailment lemmas are usable without unfolding `Clause`. -/
example {p : CompiledProblem DomConstraint} {c : Clause} (h : Entailed p c) :
    Entailed p c := h

/-! ### Concrete evaluation (also run by `main`) -/

#eval (T0.intern (posLe 0 5)).1.idx
#eval (T0.intern (posLe 0 5)).2.lits.size
#eval (T1.intern (posLe 0 5)).1.idx
#eval (T1.intern (posLe 0 6)).1.idx
#eval (T0.internArray sample).1.toList.map PLit.decode == sample.toList
#eval T0.decode (pLit (posLe 0 5))
#eval T0.decode (pLit (posLe 0 5)).negate
#eval litImpliesNot (negLe 0 5) (posLe 0 3)
#eval litImpliesNot (posLe 0 3) (negLe 0 5)
#eval litImpliesNot (posBool 1 true) (posBool 1 false)
#eval litImpliesNot (negBool 1 true) (posBool 1 true)
#eval (posBool 0 true).eval [.bool true]
#eval (posBool 0 false).eval [.bool true]

def check (name : String) (b : Bool) : IO Bool := do
  if b then
    IO.println s!"ok   {name}"
  else
    IO.println s!"FAIL {name}"
  pure b

def main : IO UInt32 := do
  let mut ok := true
  ok := (← check "intern miss gives index 0"
    ((T0.intern (posLe 0 5)).1.idx == 0)) && ok
  ok := (← check "intern miss appends one literal"
    ((T0.intern (posLe 0 5)).2.lits.size == 1)) && ok
  ok := (← check "intern hit reuses index 0"
    ((T1.intern (posLe 0 5)).1.idx == 0)) && ok
  ok := (← check "intern hit keeps table size"
    ((T1.intern (posLe 0 5)).2.lits.size == 1)) && ok
  ok := (← check "second distinct literal gets index 1"
    ((T1.intern (posLe 0 6)).1.idx == 1)) && ok
  ok := (← check "internArray decodes to the input list"
    ((T0.internArray sample).1.toList.map PLit.decode == sample.toList)) && ok
  ok := (← check "internArray table size"
    ((T0.internArray sample).2.lits.size == 3)) && ok
  ok := (← check "decode pLit"
    (T0.decode (pLit (posLe 0 5)) == posLe 0 5)) && ok
  ok := (← check "decode packed negation"
    (T0.decode (pLit (posLe 0 5)).negate == negLe 0 5)) && ok
  ok := (← check "negLe implies not posLe below the bound"
    (litImpliesNot (negLe 0 5) (posLe 0 3))) && ok
  ok := (← check "posLe implies not negLe above the bound"
    (litImpliesNot (posLe 0 3) (negLe 0 5))) && ok
  ok := (← check "Boolean two-value: true excludes false"
    (litImpliesNot (posBool 1 true) (posBool 1 false))) && ok
  ok := (← check "Boolean two-value: negated true excludes true"
    (litImpliesNot (negBool 1 true) (posBool 1 true))) && ok
  ok := (← check "a true Boolean literal evaluates true"
    ((posBool 0 true).eval [.bool true] == some true)) && ok
  ok := (← check "a false Boolean literal evaluates false"
    ((posBool 0 false).eval [.bool true] == some false)) && ok
  if ok then
    IO.println "all LitTest checks passed"
    pure 0
  else
    IO.println "LitTest FAILED"
    pure 1

end Tests.Engine.LitTest

/-- Root entry point for `lake env lean --run Tests/Engine/LitTest.lean`. -/
def main : IO UInt32 := Tests.Engine.LitTest.main
