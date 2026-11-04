/-
N4 runtime test: push/new-level/backjump, the per-slot change index, the
whole-`PLit` identity of `latestEntryOf`, and a differential check of the
binary-search `earliestImplying` against a linear reference.

Run with:
  lake env lean --run Tests/Engine/TrailTest.lean
-/
import LeanFzn.Engine.Trail

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Trail

/-! ## A tiny compiled-problem harness -/

/-- An empty compiled domain, used only to make the dummy problem's
`Entailed` obligation vacuous for the transient reason store. -/
def emptyDom : Domain := { rep := .general [] }

def p : CompiledProblem DomConstraint :=
  { names := [], domains := [emptyDom], constraints := [], objective := (),
    source := default, toStore := fun _ _ => none }

def T : LitTable := {}

theorem emptyDom_elems : DomainElems.elems emptyDom = [] := rfl

theorem allAssigns_p : allAssigns (α := Domain) p.domains = [] := by
  change allAssigns (α := Domain) [emptyDom] = []
  rw [allAssigns_cons_eq_nil (d := emptyDom) (rest := []) emptyDom_elems]

/-- A dummy transient reason (no variables, so entailment is vacuous). -/
def dummyReason : EClause p T :=
  { lits := #[], ent := by
      intro b hb
      rw [allAssigns_p] at hb
      simp at hb }

/-- Assemble a state with empty queues and no propagators. -/
def mkState (doms : Array DomC) (trail : Array Entry) (levelStart : Array Nat)
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

def litLe (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := true }

/-- `x > k`, i.e. the negative `intLe` literal. -/
def litGt (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := false }

def pl (idx : Nat) (l : Literal) : PLit := { idx := idx, lit := l }

def mkEntry (l : PLit) (lev slot : Nat) (prev : DomC) : Entry :=
  { lit := l, level := lev, reason := .decision, slot := slot, prev := prev }

/-- The linear scan which `earliestImplying` replaces; kept here as the
differential reference. -/
def earliestLinear (st : EngineState p T) (s : Slot) (l : Literal) : Option Nat :=
  (st.changeList s).foldl
    (fun acc pos =>
      match acc with
      | some _ => acc
      | none => if falsifiedAfter st pos l then some pos else none)
    none

/-- A chain of `n` slot-0 entries at positions `0..n-1`.  Entry `i` has
previous domain `[0, 10-i]` and sets `x ≤ 9-i`, so the target `x > 5`
becomes false exactly at position `4`. -/
def chainEntry (i : Nat) : Entry :=
  mkEntry (pl i (litLe 0 (Int.ofNat (9 - i)))) 0 0
    (.bounds 0 (Int.ofNat (10 - i)))

def chainState (n : Nat) : EngineState p T :=
  let trail := (List.range n).toArray.map chainEntry
  mkState #[.bounds 0 10] trail #[0] 0 #[((List.range n).toArray)] #[]

/-! ## Checks -/

def check (name : String) (cond : Bool) : IO Nat :=
  if cond then
    pure 0
  else do
    IO.eprintln s!"FAIL: {name}"
    pure 1

def main : IO Unit := do
  let d0 : DomC := .bounds 0 10
  let d1 : DomC := .bounds 0 20
  let st0 := mkState #[d0, d1] #[] #[0] 0 (Array.replicate 2 #[]) #[dummyReason]
  let e0 := mkEntry (pl 0 (litLe 0 3)) 0 0 d0
  let st1 := trailPush st0 e0
  let st2 := newLevel st1
  let e1 := mkEntry (pl 1 (litLe 1 4)) 1 1 d1
  let st3 := trailPush st2 e1
  let e2 := mkEntry (pl 2 (litLe 0 2)) 1 0 (d0.applyLit (litLe 0 3))
  let st4 := trailPush st3 e2

  let mut fails := 0

  -- `trailPush`
  fails := fails + (← check "trailPush trail size" (st1.trail.size == 1))
  fails := fails + (← check "trailPush levelStart unchanged"
    (st1.levelStart == #[0]))
  fails := fails + (← check "trailPush level unchanged" (st1.level == 0))
  fails := fails + (← check "trailPush change list self"
    (st1.changeList 0 == #[0]))
  fails := fails + (← check "trailPush change list other"
    (st1.changeList 1 == #[]))
  fails := fails + (← check "trailPush old entry preserved"
    (st1.trail[0]?.map (fun e => e.lit.idx) == some 0))
  fails := fails + (← check "trailPush old levelStart preserved"
    (st1.levelStart[0]? == some 0))

  -- `newLevel`
  fails := fails + (← check "newLevel level" (st2.level == 1))
  fails := fails + (← check "newLevel appends trail size"
    (st2.levelStart == #[0, 1]))
  fails := fails + (← check "newLevel trail unchanged"
    (st2.trail.size == st1.trail.size))
  fails := fails + (← check "newLevel doms unchanged"
    (st2.doms == st1.doms))

  fails := fails + (← check "second level change list"
    (st3.changeList 1 == #[1]))
  fails := fails + (← check "two changes on slot 0"
    (st4.changeList 0 == #[0, 2]))

  -- `latestEntryOf` uses whole-`PLit` identity, not just `lit`.
  fails := fails + (← check "latestEntryOf exact packed literal"
    (latestEntryOf st4 (pl 2 (litLe 0 2)) == some 2))
  fails := fails + (← check "latestEntryOf same denotation, other index"
    (latestEntryOf st4 (pl 9 (litLe 0 2)) == none))
  fails := fails + (← check "latestEntryOf old literal"
    (latestEntryOf st4 (pl 0 (litLe 0 3)) == some 0))

  -- `backjump` to the current level / above is a no-op (defensive clamp).
  let stNoop := backjump st4 1
  fails := fails + (← check "backjump to current level is no-op"
    (stNoop.trail.size == st4.trail.size && stNoop.level == 1 &&
      stNoop.changeList 0 == st4.changeList 0))
  let stClamp := backjump st4 7
  fails := fails + (← check "backjump above current level clamps"
    (stClamp.trail.size == st4.trail.size && stClamp.level == 1))

  -- `backjump` to level 0: keep the level-0 prefix, restore `prev`, filter
  -- the change index, and leave the append-only reason store alone.
  let stb := backjump st4 0
  fails := fails + (← check "backjump level" (stb.level == 0))
  fails := fails + (← check "backjump trail prefix size" (stb.trail.size == 1))
  fails := fails + (← check "backjump levelStart truncated"
    (stb.levelStart == #[0]))
  fails := fails + (← check "backjump changeIndex slot 0"
    (stb.changeList 0 == #[0]))
  fails := fails + (← check "backjump changeIndex slot 1 emptied"
    (stb.changeList 1 == #[]))
  fails := fails + (← check "backjump restored slot 0 domain"
    (stb.doms.getD 0 DomC.empty == e2.prev))
  fails := fails + (← check "backjump restored slot 1 domain"
    (stb.doms.getD 1 DomC.empty == d1))
  fails := fails + (← check "backjump does not truncate reasons"
    (stb.reasons.size == 1 && st4.reasons.size == 1))

  -- `dbgTraceIfShared` is test-only, as required: on freshly allocated
  -- arrays it must not report a shared backing store.
  let ownedTrail := dbgTraceIfShared "trail" (#[e0] : Array Entry)
  let ownedChangeIndex := dbgTraceIfShared "changeIndex" (#[#[0]] : Array (Array Nat))
  fails := fails + (← check "dbg-traced trail size" (ownedTrail.size == 1))
  fails := fails + (← check "dbg-traced changeIndex size"
    (ownedChangeIndex.size == 1))

  -- Earliest-implying: hand-built case with two qualifying entries.
  let lFalse := litLe 0 (-1)
  fails := fails + (← check "earliestImplying finds first qualifying"
    (earliestImplying st4 0 lFalse == some 0))
  fails := fails + (← check "earliestImplying none when no entry qualifies"
    (earliestImplying st4 0 (litLe 0 2) == none))
  fails := fails + (← check "earliestImplying empty slot after backjump"
    (earliestImplying stb 1 lFalse == none))

  -- Differential check on generated monotone chains: `earliestImplying`
  -- must agree with the linear reference, including the `none` cases.
  let targets := [litGt 0 9, litGt 0 5, litGt 0 3, lFalse, litLe 0 100]
  for n in [0, 1, 2, 3, 4, 5, 8] do
    let st := chainState n
    for target in targets do
      let binary := earliestImplying st 0 target
      let linear := earliestLinear st 0 target
      fails := fails + (← check s!"chain n={n} target={repr target} binary=linear"
        (binary == linear))
    let binary := earliestImplying st 0 (litGt 0 5)
    let expected := if n > 4 then some 4 else none
    fails := fails + (← check s!"chain n={n} x>5 expected"
      (binary == expected))
    let neg := earliestImplying st 0 lFalse
    fails := fails + (← check s!"chain n={n} x<=-1 earliest is 0"
      (neg == (if n > 0 then some 0 else none)))
    let noneCase := earliestImplying st 0 (litLe 0 100)
    fails := fails + (← check s!"chain n={n} x<=100 is none"
      (noneCase == none))
    if n > 0 then
      fails := fails + (← check s!"chain n={n} latest packed entry"
        (latestEntryOf st (chainEntry (n - 1)).lit == some (n - 1)))

  if fails == 0 then
    IO.println "TrailTest: all checks passed"
  else do
    IO.eprintln s!"TrailTest: {fails} check(s) failed"
    IO.Process.exit 1

end Tests.Engine.Trail

def main (_args : List String) : IO UInt32 := do
  Tests.Engine.Trail.main
  pure 0
