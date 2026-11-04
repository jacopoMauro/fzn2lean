/-
N13 runtime tests: LBD computation, `setLbd`, watch compaction, the
certified reduction policy, the `Inv` preservation lemmas, the reduction
schedule, and small end-to-end runs with reduction forced on.

Run with:
  lake env lean --run Tests/Engine/ReduceTest.lean
-/
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

namespace Tests.Engine.Reduce

/-- Abort with a diagnostic on the first failing check. -/
def fail (msg : String) : IO Unit := do
  IO.eprintln s!"ReduceTest FAIL: {msg}"
  IO.Process.exit 1

def check (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else fail msg

/-! ## A vacuous compiled-problem harness for the clause database -/

/-- An empty compiled domain; `allAssigns` over it is empty, so every clause
is vacuously entailed. -/
def emptyDom : Domain := { rep := .general [] }

def p : CompiledProblem DomConstraint :=
  { names := [], domains := [emptyDom], constraints := [], objective := (),
    source := default, toStore := fun _ _ => none }

def T : LitTable := {}

theorem emptyDom_elems : DomainElems.elems emptyDom = [] := rfl

theorem allAssigns_p : allAssigns (α := Domain) p.domains = [] := by
  change allAssigns (α := Domain) [emptyDom] = []
  rw [allAssigns_cons_eq_nil (d := emptyDom) (rest := []) emptyDom_elems]

/-- Any literal list is entailed by the empty problem. -/
theorem entList (ls : List Literal) : Entailed p ls := by
  intro b hb
  rw [allAssigns_p] at hb
  simp at hb

/-- Build a runtime clause with a vacuous entailment proof. -/
def mkClause (lits : Array PLit) : EClause p T :=
  EClause.ofLits p T lits (entList (T.decodeClause lits))

def litLe (s : Nat) (k : Int) : Literal := { atom := .intLe s k, positive := true }

def pl (idx : Nat) (l : Literal) : PLit := { idx := idx, lit := l }

/-- Add a clause of `size` literals with the given LBD and watch-index base. -/
def addTag (db : ClauseDB p T) (lbd size idx : Nat) : ClauseDB p T × Nat :=
  let lits := (Array.range size).map fun k =>
    pl (idx + k) (litLe 0 (Int.ofNat k))
  let (db, id) := db.add (mkClause lits)
  (db.setLbd id lbd, id)

/-- 60 LBD-5 ternary clauses, 60 LBD-3 ternary clauses, 5 LBD-2 ternary
clauses and 5 LBD-5 binary clauses.  Only the first group is a candidate for
deletion at a half-coverage cutoff of LBD 5. -/
def manyDB : ClauseDB p T :=
  let db0 : ClauseDB p T := {}
  let db1 := (List.range 60).foldl (fun db i =>
    (addTag db 5 3 (10 + 3 * i)).1) db0
  let db2 := (List.range 60).foldl (fun db i =>
    (addTag db 3 3 (300 + 3 * i)).1) db1
  let db3 := (List.range 5).foldl (fun db i =>
    (addTag db 2 3 (600 + 3 * i)).1) db2
  (List.range 5).foldl (fun db i =>
    (addTag db 5 2 (700 + 3 * i)).1) db3

def deletedAt (db : ClauseDB p T) (id : Nat) : Bool :=
  match db.clauses[id]? with
  | some sc => sc.deleted
  | none => true

def lbdAt (db : ClauseDB p T) (id : Nat) : Option Nat :=
  (db.clauses[id]?).map (fun sc => sc.lbd)

/-- Every watch entry points at a live slot. -/
def watchesOnlyLive (db : ClauseDB p T) : Bool :=
  db.watch.all fun ids => ids.all fun id =>
    match db.clauses[id]? with
    | some sc => !sc.deleted
    | none => false

/-- Every live clause is still watched at both watched positions. -/
def liveClausesWatched (db : ClauseDB p T) : Bool :=
  (List.range db.clauses.size).all fun id =>
    match db.clauses[id]? with
    | some sc =>
        if sc.deleted then true
        else
          match sc.e.lits[sc.w1]?, sc.e.lits[sc.w2]? with
          | some l0, some l1 =>
              (db.watch.getD l0.idx #[]).contains id &&
                (db.watch.getD l1.idx #[]).contains id
          | _, _ => true
    | none => false

/-- Structural invariant checks (the Prop-level preservation is checked by
the compile-time examples further down). -/
theorem setLbd_inv_check {db : ClauseDB p T} (h : db.Inv) (id n : Nat) :
    (db.setLbd id n).Inv :=
  ClauseDB.setLbd_inv db id n h

theorem compactWatches_inv_check {db : ClauseDB p T} (h : db.Inv) :
    db.compactWatches.Inv :=
  ClauseDB.compactWatches_inv db h

theorem retireWhere_inv_check {db : ClauseDB p T}
    (doomed : Nat → StoredClause p T → Bool) (h : db.Inv) :
    (db.retireWhere doomed).Inv :=
  ClauseDB.retireWhere_inv db doomed h

theorem reduce_inv_check {db : ClauseDB p T} (h : db.Inv) :
    db.reduce.Inv :=
  ClauseDB.reduce_inv db h

theorem maybeReduce_inv_check {st : EngineState p T} (h : st.db.Inv) :
    (maybeReduce st).db.Inv :=
  maybeReduce_inv st h

/-! ## LBD computation -/

def item (level : Nat) : CItem :=
  { lit := litLe 0 (Int.ofNat level), pos := 0, level := level, cidx := 0 }

def items5 : Array CItem := #[item 0, item 4, item 0, item 2, item 4]

def lbdChecks : IO Unit := do
  check "lbd: empty items" (lbdOfItems #[] == 0)
  check "lbd: one item" (lbdOfItems #[item 7] == 1)
  check "lbd: distinct levels" (lbdOfItems items5 == 3)
  let a := finishAnalysis p T items5 none 0 (entList (items5.toList.map (fun it => it.lit)))
  check "lbd: finishAnalysis carries the item LBD" (a.lbd == 3)
  let f := failAnalysis p T 0 "test"
  check "lbd: failed analysis is zero" (f.lbd == 0)

/-! ## `setLbd` -/

def setLbdChecks : IO Unit := do
  let db := manyDB
  let db' := db.setLbd 0 11
  check "setLbd: target updated" (lbdAt db' 0 == some 11)
  check "setLbd: neighbour untouched" (lbdAt db' 1 == lbdAt db 1)
  check "setLbd: clause count unchanged"
    (db'.clauses.size == db.clauses.size)
  check "setLbd: live count unchanged" (db'.live == db.live)
  check "setLbd: out-of-range id is a no-op"
    ((db.setLbd 9999 4).clauses.size == db.clauses.size)

/-! ## Reduction policy and watch compaction -/

def reduceChecks : IO Unit := do
  let db := manyDB
  let r := db.reduce
  check "reduce: candidate count is 120" (reduceCandidateCount db.reduceHistogram == 120)
  check "reduce: threshold is the LBD-5 bucket" (db.reduceThreshold == 5)
  check "reduce: all first 60 LBD-5 candidates deleted"
    ((List.range 60).all fun id => deletedAt r id)
  check "reduce: all 60 LBD-3 candidates retained"
    ((List.range 60).all fun i => !deletedAt r (60 + i))
  check "reduce: low-LBD ternary clauses retained"
    ((List.range 5).all fun i => !deletedAt r (120 + i))
  check "reduce: binary clauses retained"
    ((List.range 5).all fun i => !deletedAt r (125 + i))
  check "reduce: clauses.size unchanged" (r.clauses.size == db.clauses.size)
  check "reduce: live count is 70" (r.live == 70)
  check "reduce: live count never increases" (r.live <= db.live)
  check "reduce: watch lists point only at live slots" (watchesOnlyLive r)
  check "reduce: every live clause is still watched" (liveClausesWatched r)

  -- Fewer than 100 candidates: the database is returned unchanged.
  let small := (addTag ({} : ClauseDB p T) 5 3 10).1
  check "reduce: small database is unchanged"
    (small.reduce.clauses.size == small.clauses.size &&
      small.reduce.live == small.live)

  -- Direct compaction test: a deleted slot disappears from every row while
  -- the live slots keep their memberships.
  let dbc := (addTag ({} : ClauseDB p T) 3 3 10).1
  let (dbc1, id0) := dbc.add (mkClause #[pl 20 (litLe 0 1), pl 21 (litLe 0 2), pl 22 (litLe 0 3)])
  let (dbc2, id1) := dbc1.add (mkClause #[pl 20 (litLe 0 4), pl 21 (litLe 0 5), pl 22 (litLe 0 6)])
  let dbc3 := dbc2.delete id0
  let dbcc := dbc3.compactWatches
  check "compact: deleted id removed" (!(dbcc.watch.getD 20 #[]).contains id0)
  check "compact: live ids kept"
    ((dbcc.watch.getD 20 #[]).contains id1 &&
      (dbcc.watch.getD 21 #[]).contains id1)
  check "compact: only live ids remain" (watchesOnlyLive dbcc)

/-! ## `maybeReduce` schedule -/

def mkState (db : ClauseDB p T) (learned nextReduce : Nat) : EngineState p T :=
  { table := T
    doms := #[.bounds 0 10]
    trail := #[]
    levelStart := #[0]
    level := 0
    changeIndex := Array.replicate 1 #[]
    db := db
    reasons := #[]
    props := #[]
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := Array.replicate 1 (0.0 : Float)
    activityHeap := #[]
    phases := #[]
    restarts := 0
    nextReduce := nextReduce
    stats := { learned := learned } }

def scheduleChecks : IO Unit := do
  let db := manyDB
  let st0 := mkState db 1999 2000
  let st0' := maybeReduce st0
  check "schedule: below threshold does nothing" (st0'.nextReduce == 2000)
  check "schedule: below threshold keeps the database" (st0'.db.live == db.live)
  check "schedule: doms preserved" (st0'.doms == st0.doms)
  check "schedule: trail size preserved" (st0'.trail.size == st0.trail.size)
  check "schedule: level preserved" (st0'.level == st0.level)
  check "schedule: stats preserved" (st0'.stats == st0.stats)

  let st1 := mkState db 2000 2000
  let st1' := maybeReduce st1
  check "schedule: threshold doubles" (st1'.nextReduce == 4000)
  check "schedule: reduction ran" (st1'.db.live == 70)
  check "schedule: stats still preserved" (st1'.stats == st1.stats)
  check "schedule: table preserved" (st1'.table.lits.size == st1.table.lits.size)

  let st2 := mkState db 800000 800000
  check "schedule: threshold doubles past the old cap"
    ((maybeReduce st2).nextReduce == 1600000)
  let st3 := mkState db 1000000 1000000
  let st3' := maybeReduce st3
  check "schedule: threshold advances strictly past learned"
    (st3'.nextReduce == 2000000 && st3'.nextReduce > st3.stats.learned)
  let st4 := mkState st3'.db 1000000 st3'.nextReduce
  check "schedule: no repeat reduction at the same learned count"
    ((maybeReduce st4).nextReduce == st3'.nextReduce &&
      (maybeReduce st4).db.live == st3'.db.live)

/-! ## End-to-end: a small SAT model and an UNSAT model, reduction forced on -/

def mkProblem (ds : List Dom) (dcs : List DomConstraint) :
    CompiledProblem DomConstraint :=
  { names := []
    domains := ds
    constraints := dcs
    objective := ()
    source := default
    toStore := fun _ _ => none }

/-- Two ternary slots multiplied into a fixed 1: decision conflicts force
learning before the SAT leaf. -/
def satProblem : CompiledProblem DomConstraint :=
  mkProblem
    [⟨.small false 0 0b111⟩, ⟨.small false 0 0b111⟩, ⟨.small false 0 0b10⟩]
    [.timesSlot 0 1 2]

/-- Pigeonhole PHP(4,3), a small UNSAT Boolean clause problem. -/
def php (P H : Nat) : CompiledProblem DomConstraint :=
  let ds := List.replicate (P * H) ⟨.small true 0 0b11⟩
  let pos := (List.range P).map fun p =>
    .boolClauseSlot ((List.range H).map fun h => p * H + h) []
  let neg := (List.range H).foldr (fun h acc =>
    (List.range P).foldr (fun p acc2 =>
      ((List.range P).filter fun q => p < q).foldr (fun q acc3 =>
        .boolClauseSlot [] [p * H + h, q * H + h] :: acc3) acc2) acc) []
  mkProblem ds (pos ++ neg)

def unsatProblem : CompiledProblem DomConstraint := php 4 3

def config : SearchConfig := {}

/-- A copy of `coreSolveFull`'s entry tail with the reduction threshold forced
to zero, so every decision boundary runs `maybeReduce` from the start.  The
solver interface itself is untouched; this is a test-local synthetic state. -/
def solveReduced (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) : CoreResult × EngineStats :=
  let T : LitTable := {}
  match initState p T with
  | none => (.gaveUp, { gaveUp := 1 })
  | some st0 =>
      let st0 : EngineState p T := { st0 with nextReduce := 0 }
      let prio := annotPrioArray p
      let orders := LeanFzn.Engine.configOrders p o
      match addSeedClauses p T st0 with
      | (st, some _) =>
          let st := { st with
            stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
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

def noAccepted (p : CompiledProblem DomConstraint) : Bool :=
  (allAssigns p.domains).all fun a => !accepts p a

def endToEndChecks : IO Unit := do
  -- SAT through the ordinary entry (reduction scheduled at 2000).
  match coreSolveFull satProblem config coreFuel with
  | (.sat a, _) =>
      check "e2e: coreSolve SAT in box" ((allAssigns satProblem.domains).contains a)
      check "e2e: coreSolve SAT accepted" (accepts satProblem a)
  | (r, _) => fail s!"e2e: coreSolve SAT unexpected verdict {repr r}"

  -- UNSAT through the ordinary entry.
  check "e2e: coreSolve UNSAT on PHP(4,3)"
    (match coreSolveFull unsatProblem config coreFuel with
     | (.unsat, _) => noAccepted unsatProblem
     | _ => false)

  -- The same two runs with `nextReduce := 0`, so reduction runs at every
  -- decision boundary that the search reaches.
  match solveReduced satProblem config coreFuel with
  | (.sat a, _) =>
      check "e2e: reduced SAT in box" ((allAssigns satProblem.domains).contains a)
      check "e2e: reduced SAT accepted" (accepts satProblem a)
  | (r, _) => fail s!"e2e: reduced SAT unexpected verdict {repr r}"

  match solveReduced unsatProblem config coreFuel with
  | (.unsat, _) => check "e2e: reduced UNSAT on PHP(4,3)" (noAccepted unsatProblem)
  | (r, _) => fail s!"e2e: reduced UNSAT unexpected verdict {repr r}"

def run : IO UInt32 := do
  lbdChecks
  setLbdChecks
  reduceChecks
  scheduleChecks
  endToEndChecks
  IO.println "ReduceTest: OK"
  return 0

end Tests.Engine.Reduce

open Tests.Engine.Reduce in
def main : IO UInt32 := Tests.Engine.Reduce.run
