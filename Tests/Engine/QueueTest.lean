/-
Runtime tests for the N7 event queue, pending assignments, slot-domain
history and the propagation fixpoint.

Run with:
  lake env lean --run Tests/Engine/QueueTest.lean

These are runtime checks only; the contractual statements live in
`LeanFzn.Engine.Queue` (`insertPending_*`, `SlotHistory`, `drain_frame`,
`propagate_*`, `drain_failed`).
-/
import LeanFzn.Engine.Queue

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Queue

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"QueueTest FAIL: {msg}"
  IO.Process.exit 1

def check (name : String) (cond : Bool) : IO Nat :=
  if cond then pure 0
  else do
    IO.eprintln s!"FAIL: {name}"
    pure 1

/-! ## A tiny compiled-problem harness

`p` has an empty domain so every `Entailed` obligation is vacuous; the
engine states used below carry their own `doms`, independent of
`p.domains`. -/

def emptyDom : Domain := { rep := .general [] }

def p : CompiledProblem DomConstraint :=
  { names := [], domains := [emptyDom], constraints := [], objective := (),
    source := default, domainsArray := [emptyDom].toArray,
    domainsArray_toList := List.toList_toArray,
    toStore := fun _ _ => none }

def T : LitTable := {}

theorem emptyDom_elems : DomainElems.elems emptyDom = [] := rfl

theorem allAssigns_p : allAssigns (α := Domain) p.domains = [] := by
  change allAssigns (α := Domain) [emptyDom] = []
  rw [allAssigns_cons_eq_nil (d := emptyDom) (rest := []) emptyDom_elems]

/-- A vacuous transient reason clause. -/
def dummyReason : EClause p T :=
  { lits := #[], ent := by
      intro b hb
      rw [allAssigns_p] at hb
      simp at hb }

def litLe (s : Nat) (k : Int) : Literal :=
  { atom := .intLe s k, positive := true }

def pl (idx : Nat) (l : Literal) : PLit := { idx := idx, lit := l }

/-- A vacuously entailed unit clause, used as a stored DB clause. -/
def unitClause : EClause p T :=
  { lits := #[{ idx := 0, lit := litLe 0 0 }], ent := by
      intro b hb
      rw [allAssigns_p] at hb
      simp at hb }

/-- Component key of a trail entry; `Entry` has no `BEq`, but every field
does, so prefix checks use these keys. -/
def entryKey (e : Entry) : PLit × Nat × ReasonRef × Nat × DomC :=
  (e.lit, e.level, e.reason, e.slot, e.prev)


def pend (l : PLit) (r : ReasonRef) (count : Bool := false) : Pending :=
  { lit := l, reason := r, count := count }

/-- Assemble a state with empty queues and no propagators. -/
def mkState (doms : Array DomC) (reasons : Array (EClause p T) := #[]) :
    EngineState p T :=
  { table := T
    doms := doms
    trail := #[]
    levelStart := #[]
    level := 0
    changeIndex := #[]
    db := {}
    reasons := reasons
    props := #[]
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := ⟨Array.replicate doms.size (0.0 : Float)⟩
    activityHeap := #[]
    phases := #[]
    restarts := 0
    stats := {} }

/-! ## Fake propagators -/

/-- Binary: high priority, subscribed to `domain` and `bounds` of slot 0. -/
def prHigh : PropV2 p T :=
  { vars := #[0, 1], events := #[(0, .domain), (0, .bounds)]
    run := fun _ => .fix }

/-- Ternary: low priority, subscribed to `domain` of slot 0. -/
def prLow : PropV2 p T :=
  { vars := #[0, 1, 2], events := #[(0, .domain)]
    run := fun _ => .fix }

/-- Unary: high priority, subscribed to `fix` of slot 0. -/
def prFix : PropV2 p T :=
  { vars := #[0], events := #[(0, .fix)]
    run := fun _ => .fix }

/-- Prunes `x0 ≤ 1` once, with a transient reason. -/
def prPrune : PropV2 p T :=
  { vars := #[0], events := #[]
    run := fun _ => .prune #[(pl 0 (litLe 0 1), dummyReason)] }

/-- Reports a conflict immediately. -/
def prConflict : PropV2 p T :=
  { vars := #[0], events := #[]
    run := fun _ => .conflict dummyReason }

def registered : EngineState p T :=
  registerProps { mkState #[.bounds 0 3] with props := #[prHigh, prLow, prFix] }

def queuedPrune : EngineState p T :=
  { mkState #[.bounds 0 3] with
    props := #[prPrune]
    queueHigh := #[0]
    inQueue := ByteArray.empty.push 1 }

def queuedConflict : EngineState p T :=
  { mkState #[.bounds 0 3] with
    props := #[prConflict]
    queueHigh := #[0]
    inQueue := ByteArray.empty.push 1 }

/-! ## Checks -/

def main : IO Unit := do
  let mut fails := 0

  /- `registerProps` builds the three subscription rows. -/
  fails := fails + (← check "registerProps subs size" (registered.subs.size == 3))
  fails := fails + (← check "registerProps fix row" (registered.subs[0]!.toList == [2]))
  fails := fails + (← check "registerProps bounds row"
    (registered.subs[1]!.toList == [0]))
  fails := fails + (← check "registerProps domain row"
    (registered.subs[2]!.toList == [0, 1]))

  /- `emitSlot` on a bound change: domain subscribers fire first, high
  (binary) before low (wider), with dedup on the second event. -/
  let chg := emitSlot registered 0 (.bounds 0 3) (.bounds 1 3)
  fails := fails + (← check "emitSlot bounds high queue"
    (chg.queueHigh.toList == [0]))
  fails := fails + (← check "emitSlot bounds low queue"
    (chg.queueLow.toList == [1]))
  fails := fails + (← check "emitSlot bounds inQueue high"
    (chg.inQueue.get! 0 == (1 : UInt8)))
  fails := fails + (← check "emitSlot bounds inQueue low"
    (chg.inQueue.get! 1 == (2 : UInt8)))
  fails := fails + (← check "emitSlot bounds dedup"
    ((chg.queueHigh.toList ++ chg.queueLow.toList).length == 2))

  /- A fix event additionally notifies `.fix` subscribers. -/
  let fixd := emitSlot registered 0 (.bounds 0 3) (.bounds 2 2)
  fails := fails + (← check "emitSlot fix high queue"
    (fixd.queueHigh.toList == [0, 2]))
  fails := fails + (← check "emitSlot fix low queue"
    (fixd.queueLow.toList == [1]))
  fails := fails + (← check "emitSlot fix inQueue"
    (fixd.inQueue.get! 2 == (1 : UInt8)))

  /- A no-op emit changes nothing. -/
  let same := emitSlot registered 0 (.bounds 0 3) (.bounds 0 3)
  fails := fails + (← check "emitSlot no-op"
    (same.queueHigh.toList == [] && same.queueLow.toList == []))

  /- `insertPending`: a literal already true is a no-op. -/
  let st0 := mkState #[.bounds 0 3]
  let rTrue := insertPending st0 (pend (pl 0 (litLe 0 5)) .decision)
  fails := fails + (← check "insertPending true conf" (rTrue.2.1.isNone))
  fails := fails + (← check "insertPending true neg" (rTrue.2.2.1.isNone))
  fails := fails + (← check "insertPending true failed" (rTrue.2.2.2 == false))
  fails := fails + (← check "insertPending true doms"
    (rTrue.1.doms == st0.doms))
  fails := fails + (← check "insertPending true trail"
    (rTrue.1.trail.size == 0))

  /- A false literal with `.decision` is the defensive `failed` flag. -/
  let rFalse := insertPending st0 (pend (pl 0 (litLe 0 (-1))) .decision)
  fails := fails + (← check "insertPending false conf" (rFalse.2.1.isNone))
  fails := fails + (← check "insertPending false failed" (rFalse.2.2.2 == true))
  fails := fails + (← check "insertPending false doms"
    (rFalse.1.doms == st0.doms))

  /- A false literal with a resolvable reason returns a conflict clause. -/
  let stR := mkState #[.bounds 0 3] #[dummyReason]
  let rConf := insertPending stR (pend (pl 0 (litLe 0 (-1))) (.reason 0))
  fails := fails + (← check "insertPending conflict some" rConf.2.1.isSome)
  fails := fails + (← check "insertPending conflict failed"
    (rConf.2.2.2 == false))
  fails := fails + (← check "insertPending conflict doms"
    (rConf.1.doms == stR.doms))

  /- An unassigned literal pushes the trail with the right undo image. -/
  let rPush := insertPending st0 (pend (pl 0 (litLe 0 1)) .decision true)
  let stPush := rPush.1
  fails := fails + (← check "insertPending push no conflict" rPush.2.1.isNone)
  fails := fails + (← check "insertPending push neg some" rPush.2.2.1.isSome)
  fails := fails + (← check "insertPending push failed" (rPush.2.2.2 == false))
  fails := fails + (← check "insertPending push dom"
    (stPush.doms.getD 0 DomC.empty == DomC.bounds 0 1))
  fails := fails + (← check "insertPending push trail size"
    (stPush.trail.size == 1))
  fails := fails + (← check "insertPending push entry slot"
    ((stPush.trail.getD 0 default).slot == 0))
  fails := fails + (← check "insertPending push entry prev"
    ((stPush.trail.getD 0 default).prev == DomC.bounds 0 3))
  fails := fails + (← check "insertPending push entry level"
    ((stPush.trail.getD 0 default).level == 0))
  fails := fails + (← check "insertPending push entry lit"
    ((stPush.trail.getD 0 default).lit.lit == litLe 0 1))
  fails := fails + (← check "insertPending push change list"
    ((stPush.changeList 0).toList == [0]))
  fails := fails + (← check "insertPending push stats"
    (stPush.stats.propagations == 1))

  /- `SlotHistory` replay: two pushes on slot 0. -/
  let init : Array DomC := #[.bounds 0 3]
  let sA := (insertPending (mkState init) (pend (pl 0 (litLe 0 1)) .decision)).1
  let sB := (insertPending sA (pend (pl 0 (litLe 0 0)) .decision)).1
  fails := fails + (← check "history doms" (sB.doms.getD 0 DomC.empty == DomC.bounds 0 0))
  fails := fails + (← check "history change list size"
    ((sB.changeList 0).size == 2))
  fails := fails + (← check "history domAfter full"
    (domAfter init sB 0 (sB.changeList 0).size == sB.doms.getD 0 DomC.empty))
  fails := fails + (← check "history domAfter zero"
    (domAfter init sB 0 0 == DomC.bounds 0 3))
  fails := fails + (← check "history prev 0"
    ((sB.trail.getD ((sB.changeList 0).getD 0 0) default).prev ==
      domAfter init sB 0 0))
  fails := fails + (← check "history prev 1"
    ((sB.trail.getD ((sB.changeList 0).getD 1 0) default).prev ==
      domAfter init sB 0 1))
  fails := fails + (← check "history prev 1 value"
    ((sB.trail.getD ((sB.changeList 0).getD 1 0) default).prev ==
      DomC.bounds 0 1))

  /- `propagate`: a fake unit prop prunes `x0 ≤ 1` and reaches fixpoint. -/
  let p1 := propagate p T queuedPrune 10
  fails := fails + (← check "propagate prune conflict" p1.conflict.isNone)
  fails := fails + (← check "propagate prune failed" (p1.failed == false))
  fails := fails + (← check "propagate prune dom"
    (p1.st.doms.getD 0 DomC.empty == DomC.bounds 0 1))
  fails := fails + (← check "propagate prune trail size" (p1.st.trail.size == 1))
  fails := fails + (← check "propagate prune reasons size"
    (p1.st.reasons.size == 1))
  fails := fails + (← check "propagate prune reason resolves"
    ((reasonClause? p1.st (.reason 0)).isSome))
  fails := fails + (← check "propagate prune queues empty"
    (p1.st.queueHigh.isEmpty && p1.st.queueLow.isEmpty))
  /- The loop spends one fuel unit on the high-worklist dispatch and one on
  the pending insertion, then stops with the remaining fuel. -/
  fails := fails + (← check "propagate prune fuel" (p1.fuel == 8))

  /- Fuel exhaustion is not an error: `fuel = 0` is the identity. -/
  let pz := propagate p T queuedPrune 0
  fails := fails + (← check "propagate fuel0 identity" (pz.st.doms == queuedPrune.doms))
  fails := fails + (← check "propagate fuel0 fuel" (pz.fuel == 0))
  fails := fails + (← check "propagate fuel0 failed" (pz.failed == false))

  /- Fuel 1 runs the prop and stops before the pending literal. -/
  let p1f := propagate p T queuedPrune 1
  fails := fails + (← check "propagate fuel1 conflict" p1f.conflict.isNone)
  fails := fails + (← check "propagate fuel1 trail" (p1f.st.trail.size == 0))
  fails := fails + (← check "propagate fuel1 reasons" (p1f.st.reasons.size == 1))
  fails := fails + (← check "propagate fuel1 fuel" (p1f.fuel == 0))

  /- Conflict stops the loop and carries the prop's clause. -/
  let pc := propagate p T queuedConflict 5
  fails := fails + (← check "propagate conflict some" pc.conflict.isSome)
  fails := fails + (← check "propagate conflict failed" (pc.failed == false))
  fails := fails + (← check "propagate conflict doms"
    (pc.st.doms == queuedConflict.doms))

  /- The clause database is not extended by propagation. -/
  let withDB : EngineState p T :=
    { queuedPrune with
      db := { clauses := #[{ e := unitClause, w1 := 0, w2 := 0 }] } }
  let pdb := propagate p T withDB 10
  fails := fails + (← check "propagate db size" (pdb.st.db.clauses.size == 1))
  fails := fails + (← check "propagate db clause present"
    ((pdb.st.db.clauses[0]?).isSome))
  fails := fails + (← check "propagate db unit clause size"
    ((pdb.st.db.clauses[0]?).map (fun sc => sc.e.lits.size) == some 1))
  fails := fails + (← check "propagate db clause denotation unchanged"
    ((pdb.st.db.clauses[0]?).map (fun sc => sc.e.lits) ==
      (withDB.db.clauses[0]?).map (fun sc => sc.e.lits)))

  /- A second run on the fixpoint state changes nothing. -/
  let p2 := propagate p T p1.st 10
  fails := fails + (← check "second propagate trail"
    (p2.st.trail.size == p1.st.trail.size))
  fails := fails + (← check "second propagate reasons"
    (p2.st.reasons.size == p1.st.reasons.size))
  fails := fails + (← check "second propagate doms"
    (p2.st.doms == p1.st.doms))
  fails := fails + (← check "second propagate reasons prefix"
    (List.isPrefixOf (p1.st.reasons.toList.map (fun c => c.lits))
      (p2.st.reasons.toList.map (fun c => c.lits))))
  fails := fails + (← check "second propagate trail prefix"
    (List.isPrefixOf (p1.st.trail.toList.map entryKey)
      (p2.st.trail.toList.map entryKey)))

  if fails == 0 then
    IO.println "QueueTest: all checks passed"
  else
    IO.eprintln s!"QueueTest: {fails} check(s) failed"
    IO.Process.exit 1

end Tests.Engine.Queue

open Tests.Engine.Queue in
def main : IO UInt32 := do
  Tests.Engine.Queue.main
  return 0
