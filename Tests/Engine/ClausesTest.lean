/-
N5 runtime tests: clause insertion/live counting, two-watched-literal
propagation (conflict, pruning, watch move, stale skip), lazy deletion and
slot reuse, unit propagation, canonicalisation, reason lookup, and a small
differential check against a reference clause-status evaluator.

Run with:
  lake env lean --run Tests/Engine/ClausesTest.lean
-/
import LeanFzn.Engine.Clauses

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

namespace Tests.Engine.Clauses

/-! ## A tiny compiled-problem harness -/

/-- An empty compiled domain; `allAssigns` over it is empty, so every clause
is vacuously entailed.  This keeps the test problem's proof obligations
vacuous without constructing a real FlatZinc model. -/
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

/-- Any literal array is entailed by the empty problem. -/
theorem entVacuous (lits : Array PLit) : Entailed p (T.decodeClause lits) := by
  intro b hb
  rw [allAssigns_p] at hb
  simp at hb

/-- Build a runtime clause with a vacuous entailment proof. -/
def mkClause (lits : Array PLit) : EClause p T :=
  EClause.ofLits p T lits (entVacuous lits)

/-- Assemble a state with empty queues, no propagators, and a chosen clause
database / reason store. -/
def mkState (table : LitTable) (db : ClauseDB p T)
    (reasons : Array (EClause p T)) : EngineState p T :=
  { table := table
    doms := #[.bounds 0 10]
    trail := #[]
    levelStart := #[0]
    level := 0
    changeIndex := Array.replicate 1 #[]
    db := db
    reasons := reasons
    props := #[]
    subs := #[]
    queueHigh := #[]
    queueLow := #[]
    inQueue := ByteArray.empty
    activity := ⟨Array.replicate 1 (0.0 : Float)⟩
    activityHeap := #[]
    phases := #[]
    restarts := 0
    stats := {} }

/-! ## Literals and domains -/

def litLe (s : Nat) (k : Int) : Literal := { atom := .intLe s k, positive := true }

def pl (idx : Nat) (l : Literal) : PLit := { idx := idx, lit := l }

/-- `x ≤ 3`, `x ≤ 6`, `x ≤ 9` on slot 0. -/
def a : PLit := pl 0 (litLe 0 3)
def b : PLit := pl 1 (litLe 0 6)
def c : PLit := pl 2 (litLe 0 9)

def d0 : DomC := .bounds 0 10
def dA : DomC := .bounds 4 10
def dAB : DomC := .bounds 7 10
def dABC : DomC := .bounds 10 10
def dTrue : DomC := .bounds 0 3

/-! ## Result helpers (the output type has no `BEq`) -/

def outStr {p : CompiledProblem DomConstraint} {T : LitTable}
    (o : WPropOut p T) : String :=
  match o with
  | .none => "none"
  | .conflict _ id => s!"conflict|{id}"
  | .prune ps =>
      match ps[0]? with
      | some x =>
          if ps.size == 1 then
            s!"prune|{x.1.idx}|{x.2}"
          else s!"prune|multi|{ps.size}"
      | none => "none"

def isNone {p : CompiledProblem DomConstraint} {T : LitTable}
    (o : WPropOut p T) : Bool :=
  match o with
  | .none => true
  | _ => false

def conflictIs {p : CompiledProblem DomConstraint} {T : LitTable}
    (o : WPropOut p T) (e : EClause p T) (id : Nat) : Bool :=
  match o with
  | .conflict c' id' => c'.lits == e.lits && id' == id
  | _ => false

def pruneHas {p : CompiledProblem DomConstraint} {T : LitTable}
    (o : WPropOut p T) (q : PLit) (id : Nat) : Bool :=
  match o with
  | .prune ps => ps.any (fun x => x.1 == q && x.2 == id)
  | _ => false

/-! ## Reference evaluator for one watched clause

The reference reads only the clause literals and the domains.  A conflict is
reported exactly when every literal is false; a pruning is reported exactly
when all literals except the other watched one are false and that other
watched literal is unassigned.  Otherwise propagation is silent (it either
keeps the watch or moves it). -/

def watchesL (sc : StoredClause p T) (l : PLit) : Bool :=
  (match sc.e.lits[sc.w1]? with
   | some q => q.idx == l.idx
   | none => false) ||
  (match sc.e.lits[sc.w2]? with
   | some q => q.idx == l.idx
   | none => false)

def refOut (sc : StoredClause p T) (id : Nat) (doms : Array DomC) (l : PLit) : String :=
  if sc.deleted || sc.e.lits.size < 2 || !(watchesL sc l) then
    "none"
  else
    let vals := sc.e.lits.map (fun q => litValueC doms q)
    if vals.all (fun v => v == some false) then
      s!"conflict|{id}"
    else
      let nf := sc.e.lits.filterMap
        (fun q => if litValueC doms q == some false then none else some q)
      if nf.size == 1 then
        match nf[0]? with
        | some q =>
            match sc.e.lits[otherWatchedPos sc l]? with
            | some other =>
                if other.idx == q.idx && litValueC doms q == none then
                  s!"prune|{q.idx}|{id}"
                else "none"
            | none => "none"
        | none => "none"
      else "none"

/-! ## Checks -/

def check (name : String) (cond : Bool) : IO Nat :=
  if cond then
    pure 0
  else do
    IO.eprintln s!"FAIL: {name}"
    pure 1

/-- Project the literal array out of an optional clause, avoiding a `BEq`
instance for `EClause` (whose proof field is not decidable). -/
def clauseLits? (o : Option (EClause p T)) : Option (Array PLit) :=
  o.map (fun e => e.lits)

def main : IO UInt32 := do
  let dbEmpty : ClauseDB p T := ClauseDB.empty
  let e2 := mkClause #[a, b]
  let e3 := mkClause #[a, b, c]
  let eUnit := mkClause #[a]
  let eEmpty := mkClause #[]

  let mut fails := 0

  -- Literal evaluation and slot extraction.
  fails := fails + (← check "litValueC false on dA"
    (litValueC #[dA] a == some false))
  fails := fails + (← check "litValueC unknown on d0"
    (litValueC #[d0] a == none))
  fails := fails + (← check "litSlotC reads the atom slot" (litSlotC a == 0))

  -- Empty database.
  fails := fails + (← check "empty db live = 0" (dbEmpty.live == 0))
  fails := fails + (← check "empty db no clauses" (dbEmpty.clauses.size == 0))
  fails := fails + (← check "empty db no conflict" dbEmpty.emptyConflict?.isNone)

  -- Add a size-2 clause: id 0, live 1, both watches installed.
  let db1 := dbEmpty.add e2
  fails := fails + (← check "add returns id 0" (db1.2 == 0))
  fails := fails + (← check "add live = 1" (db1.1.live == 1))
  fails := fails + (← check "add clause slot size" (db1.1.clauses.size == 1))
  fails := fails + (← check "add stored clause is e2"
    (db1.1.clauses[0]?.map (fun sc => sc.e.lits) == some e2.lits))
  fails := fails + (← check "add watches first literal"
    (db1.1.watchList a.idx == #[0]))
  fails := fails + (← check "add watches second literal"
    (db1.1.watchList b.idx == #[0]))
  fails := fails + (← check "add does not watch third index"
    (db1.1.watchList c.idx == #[]))
  fails := fails + (← check "watch positions of e2 are 0,1"
    (db1.1.clauses[0]?.map (fun sc => (sc.w1, sc.w2)) == some (0, 1)))

  -- Binary-clause direct path: falsifying one watch prunes the other
  -- without a general replacement scan.
  let propBin := db1.1.propagateLiteral p T #[dA] a
  fails := fails + (← check "binary clause prunes the other watch"
    (pruneHas propBin.2 b 0))
  fails := fails + (← check "binary clause keeps both watch positions"
    (propBin.1.clauses[0]?.map (fun sc => (sc.w1, sc.w2)) == some (0, 1)))

  -- Add a unit clause: it increments live but is not watched.
  let dbU := db1.1.add eUnit
  fails := fails + (← check "unit add id 1" (dbU.2 == 1))
  fails := fails + (← check "unit add live = 2" (dbU.1.live == 2))
  fails := fails + (← check "unit clause is not watched"
    (dbU.1.watchList a.idx == #[0]))

  -- Empty clause: `emptyConflict?` reports it, and deletion removes it.
  let dbE := db1.1.add eEmpty
  fails := fails + (← check "empty clause id 1" (dbE.2 == 1))
  fails := fails + (← check "emptyConflict? finds the empty clause"
    (clauseLits? dbE.1.emptyConflict? == some eEmpty.lits))
  fails := fails + (← check "emptyConflict? is none after deletion"
    (dbE.1.delete 1).emptyConflict?.isNone)

  -- Conflict on a size-2 clause when both literals are false.
  let conf2 := db1.1.propagateLiteral p T #[dAB] a
  fails := fails + (← check "two false literals conflict on e2"
    (conflictIs conf2.2 e2 0))
  fails := fails + (← check "conflict keeps clause slot count"
    (conf2.1.clauses.size == 1))
  fails := fails + (← check "conflict preserves live count"
    (conf2.1.live == 1))

  -- Conflict on the first of two clauses watching `a`: the row keeps the
  -- visited conflict clause and the still-unvisited suffix, without
  -- duplicating the already-processed prefix.
  let db2a := db1.1.add e3
  let conf2a := db2a.1.propagateLiteral p T #[dABC] a
  fails := fails + (← check "two-watch conflict names the first clause"
    (conflictIs conf2a.2 e2 0))
  fails := fails + (← check "conflict row keeps only the unvisited suffix"
    (conf2a.1.watchList a.idx == #[0, 1]))

  -- Watch move: [a,b,c], falsify a; the watch on a moves to c.
  let move := dbEmpty.add e3
  fails := fails + (← check "size-3 clause id 0" (move.2 == 0))
  let db3 := move.1
  let propA := db3.propagateLiteral p T #[dA] a
  fails := fails + (← check "watch move keeps the other watch"
    (propA.1.clauses[0]?.map (fun sc => (sc.w1, sc.w2)) == some (2, 1)))
  fails := fails + (← check "watch move is silent (no prune/conflict)"
    (isNone propA.2))
  fails := fails + (← check "moved watch is installed in c's row"
    (propA.1.watchList c.idx == #[0]))
  fails := fails + (← check "old a row is cleared after the watch moves"
    (propA.1.watchList a.idx == #[]))

  -- Second pass on the now empty a row is silent and changes nothing.
  let propA2 := propA.1.propagateLiteral p T #[dA] a
  fails := fails + (← check "second a pass is silent"
    (isNone propA2.2 &&
      propA2.1.clauses[0]?.map (fun sc => (sc.w1, sc.w2)) == some (2, 1) &&
      propA2.1.watchList a.idx == #[]))

  -- Falsify b: the clause watches b and c, c is the only unassigned
  -- literal, so propagation prunes c.
  let propB := propA.1.propagateLiteral p T #[dAB] b
  fails := fails + (← check "propagating b prunes the unit literal c"
    (pruneHas propB.2 c 0))

  -- Falsify all three: propagating b is now a conflict.
  let conf3 := propA.1.propagateLiteral p T #[dABC] b
  fails := fails + (← check "all literals false conflict on e3"
    (conflictIs conf3.2 e3 0))

  -- Unit propagation: the unit clause [a] conflicts / prunes / stays quiet.
  let unitsFalse := dbU.1.propagateUnits p T #[dA]
  fails := fails + (← check "unit propagation conflict on a=false"
    (conflictIs unitsFalse.2 eUnit 1))
  let unitsUnknown := dbU.1.propagateUnits p T #[d0]
  fails := fails + (← check "unit propagation prunes unassigned a"
    (pruneHas unitsUnknown.2 a 1))
  let unitsTrue := dbU.1.propagateUnits p T #[dTrue]
  fails := fails + (← check "unit propagation is quiet when a=true"
    (isNone unitsTrue.2))
  fails := fails + (← check "unit propagation never changes the db"
    (unitsFalse.1.clauses.size == dbU.1.clauses.size &&
      unitsFalse.1.live == dbU.1.live))

  -- Lazy deletion skips the clause; reusing the free slot restores it.
  let dbDel := db1.1.delete 0
  fails := fails + (← check "delete decrements live" (dbDel.live == 0))
  fails := fails + (← check "delete pushes the free slot" (dbDel.free == #[0]))
  fails := fails + (← check "delete marks the slot deleted"
    (dbDel.clauses[0]?.map (fun sc => sc.deleted) == some true))
  let deletedProp := dbDel.propagateLiteral p T #[dAB] a
  fails := fails + (← check "deleted clause is skipped" (isNone deletedProp.2))
  let reuse := dbDel.add e2
  fails := fails + (← check "add reuses the free slot" (reuse.2 == 0))
  fails := fails + (← check "reuse restores live" (reuse.1.live == 1))
  fails := fails + (← check "reuse empties the free list" (reuse.1.free == #[]))
  let reuseProp := reuse.1.propagateLiteral p T #[dAB] a
  fails := fails + (← check "reused slot propagates conflicts again"
    (conflictIs reuseProp.2 e2 0))

  -- Canonicalisation: re-intern after a nonempty prefix of the table.
  let (_, Tpre) := T.intern (litLe 9 9)
  let stPre := mkState Tpre db1.1 #[]
  let canon := canonClause stPre e2
  fails := fails + (← check "canonClause keeps the literal count"
    (canon.1.lits.size == 2))
  fails := fails + (← check "canonClause preserves denotations"
    (canon.1.lits.map PLit.decode == e2.lits.map PLit.decode))
  fails := fails + (← check "canonClause grows the table by two literals"
    (canon.2.table.lits.size == stPre.table.lits.size + 2))
  fails := fails + (← check "canonClause table is append-only"
    (canon.2.table.lits.toList.take stPre.table.lits.toList.length ==
      stPre.table.lits.toList))
  fails := fails + (← check "canonClause result literals are well-formed"
    (canon.1.lits.all (fun q => canon.2.table.lits[q.idx]? == some q.lit)))

  -- Hinted canonicalisation: validated indices are reused unchanged.
  let stCanon := mkState canon.2.table db1.1 #[]
  let canonAgain := canonClause stCanon canon.1
  fails := fails + (← check "canonClause reuses valid intern hints"
    (canonAgain.1.lits == canon.1.lits))
  fails := fails + (← check "hint reuse does not grow the table"
    (canonAgain.2.table.lits.size == stCanon.table.lits.size))
  -- A stale hint falls back to the hash-map interner and appends.
  let stale := mkClause #[pl 1 (litLe 0 4)]
  let canonStale := canonClause stCanon stale
  fails := fails + (← check "stale hint preserves the denotation"
    (canonStale.1.lits.map PLit.decode == #[litLe 0 4]))
  fails := fails + (← check "stale hint falls back to a fresh intern"
    (canonStale.2.table.lits.size == stCanon.table.lits.size + 1))

  -- Reason lookup: learned, transient, decision, missing, and deleted.
  let dbR := db1.1
  let stR := mkState T dbR #[eUnit]
  fails := fails + (← check "reasonClause? decision is none"
    (reasonClause? stR .decision).isNone)
  fails := fails + (← check "reasonClause? learned returns the stored e"
    (clauseLits? (reasonClause? stR (.learned 0)) == some e2.lits))
  fails := fails + (← check "reasonClause? reason returns the transient e"
    (clauseLits? (reasonClause? stR (.reason 0)) == some eUnit.lits))
  fails := fails + (← check "reasonClause? missing learned is none"
    (reasonClause? stR (.learned 7)).isNone)
  let stDel := mkState T (dbR.delete 0) #[]
  fails := fails + (← check "reasonClause? kept for a deleted clause"
    (clauseLits? (reasonClause? stDel (.learned 0)) == some e2.lits))

  -- Differential: for every false literal in a one-clause database, the
  -- propagation result agrees with the reference clause-status evaluator.
  let clauses : List (Array PLit) := [#[a, b], #[a, b, c], #[a], #[]]
  let domains : List (Array DomC) :=
    [#[d0], #[dA], #[dAB], #[dABC], #[dTrue], #[.bounds 4 6]]
  for lits in clauses do
    let e := mkClause lits
    let db := (ClauseDB.empty : ClauseDB p T).add e
    match db.1.clauses[0]? with
    | none =>
        fails := fails + (← check s!"differential missing clause size {lits.size}" false)
    | some sc =>
        for doms in domains do
          for l in lits do
            if litValueC doms l == some false then
              let out := db.1.propagateLiteral p T doms l
              let expected := refOut sc 0 doms l
              fails := fails + (← check
                s!"differential lits={lits.size} l={l.idx} out={outStr out.2} ref={expected}"
                (outStr out.2 == expected))
        -- An all-false domain must conflict whenever the clause has at least
        -- two literals; the differential above already checks the status of
        -- every watched literal.
        let allFalse : Array DomC := #[dABC]
        match lits[0]? with
        | some first =>
            if 2 ≤ lits.size then
              let out := db.1.propagateLiteral p T allFalse first
              fails := fails + (← check
                s!"all-false clause of size {lits.size} conflicts"
                (outStr out.2 == "conflict|0"))
        | none => pure ()

  if fails == 0 then
    IO.println "ClausesTest: all checks passed"
    pure 0
  else do
    IO.eprintln s!"ClausesTest: {fails} check(s) failed"
    pure 1

end Tests.Engine.Clauses

/-- Root entry point for `lake env lean --run Tests/Engine/ClausesTest.lean`. -/
def main : IO UInt32 := Tests.Engine.Clauses.main
