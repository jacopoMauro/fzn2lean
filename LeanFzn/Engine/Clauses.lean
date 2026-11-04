/-
File: LeanFzn/Engine/Clauses.lean

N5: the two-watched-literal clause database, canonicalisation, and reason
lookup.  The watch scheme is specified by the invariants in this module.

This module owns:

* `ClauseDB.ensureWatch` / `add` / `delete` / `emptyConflict?` (the clause
  slot store, lazy deletion and the free list);
* `litValueC` / `litSlotC` and the frozen two-watched-literal propagation
  `propagateLiteral` plus unit propagation `propagateUnits`;
* `canonLit` / `canonClause` (the re-intern/canonicalisation helpers used at
  propagator boundaries) and `reasonClause?` (the public reason API);
* the structural database invariant `ClauseDB.Inv` and its preservation
  proofs.

Design notes (N5 deviations, all stated in the handoff):

* The spike compared watch-list entries to the propagated literal with full
  `PLit` equality.  A watch-list row is indexed by `PLit.idx`, so staleness
  must be decided by `idx`; the port uses `q.idx == l.idx`.  Under
  `LitTable.WF` the two tests agree, and the `idx` test is the one the frozen
  scheme describes.
* When a watch moves, the clause id stays in `kept` (the surviving row for
  the propagated index) even if the new literal has a different index.  The
  old entry is then a legal stale entry, and the invariant survives the
  corner case where the replacement literal has the same index.
* On a conflict the clause id is kept in the surviving watch row (it is a
  live clause still watching that index); dropping it would violate the
  watch invariant.
* `propagateLiteral` returns `(db', out)` with `db'.clauses` pointwise equal
  to `db.clauses` in the `e` and `deleted` fields, but *not* literally equal:
  a watch move updates `w1`/`w2`, which live inside `StoredClause` in the
  frozen `ClauseDB` type.  The literal equality requested by the N5 prompt
  is therefore false for this representation; the shipped specification is
  the pointwise form (`propagateLiteral_clauses_e`,
  `propagateLiteral_clauses_deleted`, `propagateLiteral_clauses_size`).
-/
import LeanFzn.Engine.Types
import LeanFzn.Engine.Lit
import LeanFzn.Engine.Dom

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Propagation results -/

/-- Clause-propagation result.  Prunings carry the clause slot id so the
engine can use `ReasonRef.learned id` on the trail. -/
inductive WPropOut (p : CompiledProblem DomConstraint) (T : LitTable) where
  | none
  | prune (ps : Array (PLit × Nat))
  | conflict (c : EClause p T) (id : Nat)

/-- Turn an accumulated pruning array into the public result, hiding an
empty prune list. -/
def WPropOut.ofPrunes (ps : Array (PLit × Nat)) : WPropOut p T :=
  if ps.isEmpty then .none else .prune ps

/-- Public output shaping: hide an empty pruning list, leave conflicts
unchanged. -/
def WPropOut.shape (o : WPropOut p T) : WPropOut p T :=
  match o with
  | .prune ps => .ofPrunes ps
  | o => o

/-! ## Small array lemmas used by the proofs -/

/-- `getElem?` after `set!`, including the out-of-bounds no-op case. -/
private theorem array_getElem?_set! {α : Type} (xs : Array α) (i j : Nat) (v : α) :
    (xs.set! i v)[j]? =
      if i = j then (if i < xs.size then some v else xs[j]?) else xs[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst j
    by_cases h : i < xs.size
    · simp [h]
    · have hnone : xs[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h)
      simp [h, hnone]
  · simp [hij]

/-- Reading `set!` at the written index. -/
private theorem array_getD_set!_self {α : Type} [Inhabited α] (xs : Array α)
    (i : Nat) (v : α) (d : α) (h : i < xs.size) :
    (xs.set! i v).getD i d = v := by
  rw [Array.getD_eq_getD_getElem?, array_getElem?_set!]
  simp [h]

/-- Reading `set!` away from the written index. -/
private theorem array_getD_set!_ne {α : Type} [Inhabited α] (xs : Array α)
    (i j : Nat) (v : α) (d : α) (h : i ≠ j) :
    (xs.set! i v).getD j d = xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, array_getElem?_set!]
  simp [h]

/-! ## The clause database -/

/-- The empty clause database. -/
def ClauseDB.empty : ClauseDB p T := {}

/-- Grow the watch array to at least `n` rows. -/
def ClauseDB.ensureWatch (db : ClauseDB p T) (n : Nat) : ClauseDB p T :=
  if db.watch.size < n then
    { db with watch := db.watch ++ Array.replicate (n - db.watch.size) #[] }
  else db

/-- The watch list of index `i` (empty when the row does not exist). -/
def ClauseDB.watchList (db : ClauseDB p T) (i : Nat) : Array Nat :=
  db.watch.getD i #[]

/-- `ensureWatch` guarantees at least `n` rows. -/
theorem ClauseDB.ensureWatch_size_ge (db : ClauseDB p T) (n : Nat) :
    n ≤ (db.ensureWatch n).watch.size := by
  unfold ClauseDB.ensureWatch
  split <;> rename_i h
  · rw [Array.size_append]
    simp only [Array.size_replicate]
    omega
  · omega

/-- `ensureWatch` never changes an existing watch list (it only appends
empty rows). -/
theorem ClauseDB.ensureWatch_watchList (db : ClauseDB p T) (n i : Nat) :
    (db.ensureWatch n).watchList i = db.watchList i := by
  unfold ClauseDB.ensureWatch ClauseDB.watchList
  split <;> rename_i h
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    by_cases hi : i < db.watch.size
    · simp [hi]
    · have hle : db.watch.size ≤ i := Nat.le_of_not_lt hi
      have hnone : db.watch[i]? = none := Array.getElem?_eq_none hle
      rw [hnone]
      simp only [Nat.not_lt.mpr hle, if_false]
      rw [Array.getElem?_replicate]
      split <;> simp
  · rfl

/-- `ensureWatch` preserves membership in every watch list. -/
theorem ClauseDB.ensureWatch_mem (db : ClauseDB p T) (n i id : Nat)
    (h : id ∈ db.watchList i) : id ∈ (db.ensureWatch n).watchList i := by
  rw [ClauseDB.ensureWatch_watchList]
  exact h

/-- Append `id` to the watch lists of `l0` and `l1`, growing the watch array
first.  This is the only place that installs a clause's two watches. -/
def ClauseDB.addWatchPair (db : ClauseDB p T) (id : Nat) (l0 l1 : PLit) : ClauseDB p T :=
  let db := db.ensureWatch (max l0.idx l1.idx + 1)
  let db := { db with
    watch := db.watch.set! l0.idx ((db.watch.getD l0.idx #[]).push id) }
  { db with
    watch := db.watch.set! l1.idx ((db.watch.getD l1.idx #[]).push id) }

/-- The stored clause created by `add`: the first two literals are watched
for clauses of size at least two. -/
def ClauseDB.newStored (e : EClause p T) : StoredClause p T :=
  { e := e, w1 := 0, w2 := if e.lits.size ≥ 2 then 1 else 0, deleted := false }

/-- Install the two watch entries of a freshly stored clause (no entries for
unit and empty clauses). -/
def ClauseDB.installWatches (db : ClauseDB p T) (id : Nat) (e : EClause p T) :
    ClauseDB p T :=
  if e.lits.size ≥ 2 then
    match e.lits[0]?, e.lits[1]? with
    | some l0, some l1 => db.addWatchPair id l0 l1
    | _, _ => db
  else db

/-- The database after installing a reused slot, before its watches. -/
def ClauseDB.reuseBase (db : ClauseDB p T) (id : Nat) (sc : StoredClause p T) :
    ClauseDB p T :=
  { db with clauses := db.clauses.set! id sc, free := db.free.pop, live := db.live + 1 }

/-- The database after appending a fresh slot, before its watches. -/
def ClauseDB.pushBase (db : ClauseDB p T) (sc : StoredClause p T) : ClauseDB p T :=
  { db with clauses := db.clauses.push sc, live := db.live + 1 }

/-- Add a clause and return its slot.  Unit and empty clauses are stored
without watch entries; the caller propagates them at entry / immediately. -/
def ClauseDB.add (db : ClauseDB p T) (e : EClause p T) : ClauseDB p T × Nat :=
  let sc : StoredClause p T := ClauseDB.newStored e
  match db.free.back? with
  | some id => ((db.reuseBase id sc).installWatches id e, id)
  | none =>
      let id := db.clauses.size
      ((db.pushBase sc).installWatches id e, id)

/-- Lazily delete a clause slot. -/
def ClauseDB.delete (db : ClauseDB p T) (id : Nat) : ClauseDB p T :=
  match db.clauses[id]? with
  | some sc =>
      if sc.deleted then db
      else { db with
        clauses := db.clauses.set! id { sc with deleted := true }
        free := db.free.push id
        live := if db.live = 0 then 0 else db.live - 1 }
  | none => db

/-- First live empty clause, if any. -/
def ClauseDB.emptyConflict? (db : ClauseDB p T) : Option (EClause p T) :=
  db.clauses.findSome? fun sc =>
    if sc.deleted || sc.e.lits.size != 0 then none else some sc.e

/-- Evaluate a stored literal on the current domains.  The watch index
`l.idx` chooses the clause watch list; the domain is chosen by the atom's
slot (`l.slot`), never by the intern index. -/
def litValueC (doms : Array DomC) (l : PLit) : Option Bool :=
  match doms[l.slot]? with
  | some d => d.evalLit l.lit
  | none => none

/-- The slot of a stored literal is carried by its denotation, not by its
watch index. -/
def litSlotC (l : PLit) : Nat := l.slot

/-! ## Watch scanning -/

/-- The first watched position of `sc` denotes a literal with watch index
`l.idx`. -/
def ClauseWatches₁ (sc : StoredClause p T) (l : PLit) : Prop :=
  match sc.e.lits[sc.w1]? with
  | some q => q.idx = l.idx
  | none => False

/-- The second watched position of `sc` denotes a literal with watch index
`l.idx`. -/
def ClauseWatches₂ (sc : StoredClause p T) (l : PLit) : Prop :=
  match sc.e.lits[sc.w2]? with
  | some q => q.idx = l.idx
  | none => False

instance (sc : StoredClause p T) (l : PLit) : Decidable (ClauseWatches₁ sc l) := by
  unfold ClauseWatches₁
  split <;> infer_instance

instance (sc : StoredClause p T) (l : PLit) : Decidable (ClauseWatches₂ sc l) := by
  unfold ClauseWatches₂
  split <;> infer_instance

/-- The clause currently watches the propagated index at one of its two
watched positions. -/
def ClauseWatches (sc : StoredClause p T) (l : PLit) : Prop :=
  ClauseWatches₁ sc l ∨ ClauseWatches₂ sc l

instance (sc : StoredClause p T) (l : PLit) : Decidable (ClauseWatches sc l) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The other watched position, choosing the second position when the first
one is the one that matched `l.idx`. -/
def otherWatchedPos (sc : StoredClause p T) (l : PLit) : Nat :=
  match sc.e.lits[sc.w1]? with
  | some q => if q.idx = l.idx then sc.w2 else sc.w1
  | none => sc.w2

/-- Fuel-based search for the first position of `lits` that is not one of
the two watched positions and whose literal is not false.  The index is
returned together with the proof that it is in bounds. -/
private def scanFind (doms : Array DomC) (lits : Array PLit) (w1 w2 : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j =>
      if j < lits.size then
        if lits.size < 2 then
          none
        else if j = w1 ∨ j = w2 then
          scanFind doms lits w1 w2 fuel (j + 1)
        else
          match lits[j]? with
          | some q =>
              if litValueC doms q = some false then
                scanFind doms lits w1 w2 fuel (j + 1)
              else some j
          | none => scanFind doms lits w1 w2 fuel (j + 1)
      else none

/-- Scan one watch list.  `fuel` and `i` walk `olds`; `kept` is the future
content of `watch[l.idx]`, `prunes` the accumulated prunings.  The function
is total by structural recursion on `fuel`; `propagateLiteral` calls it with
`fuel = olds.size`, `i = 0`. -/
private def scanWatches (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (l : PLit) (olds : Array Nat) :
    Nat → Nat → Array Nat → Array (PLit × Nat) → ClauseDB p T →
    ClauseDB p T × WPropOut p T
  | 0, _, kept, prunes, db =>
      ({ db with watch := db.watch.set! l.idx kept }, .prune prunes)
  | fuel + 1, i, kept, prunes, db =>
      if i < olds.size then
        let id := olds[i]!
        match db.clauses[id]? with
        | none =>
            scanWatches p T doms l olds fuel (i + 1) kept prunes db
        | some sc =>
            if sc.deleted then
              scanWatches p T doms l olds fuel (i + 1) kept prunes db
            else if hw : ClauseWatches sc l then
              let otherPos := otherWatchedPos sc l
              match sc.e.lits[otherPos]? with
              | none =>
                  scanWatches p T doms l olds fuel (i + 1) kept prunes db
              | some other =>
                  match litValueC doms other with
                  | some true =>
                      scanWatches p T doms l olds fuel (i + 1) (kept.push id) prunes db
                  | otherVal =>
                      match scanFind doms sc.e.lits sc.w1 sc.w2 sc.e.lits.size 0 with
                      | some j =>
                          match sc.e.lits[j]? with
                          | some q =>
                              let sc' :=
                                if ClauseWatches₁ sc l then { sc with w1 := j }
                                else { sc with w2 := j }
                              let db := { db with clauses := db.clauses.set! id sc' }
                              let db := db.ensureWatch (q.idx + 1)
                              let w := (db.watch.getD q.idx #[]).push id
                              -- Drop the stale entry unless the clause still
                              -- watches `l.idx` at its other (or new) position.
                              let kept' :=
                                if q.idx = l.idx ∨ other.idx = l.idx then
                                  kept.push id
                                else kept
                              scanWatches p T doms l olds fuel (i + 1) kept'
                                prunes { db with watch := db.watch.set! q.idx w }
                          | none =>
                              scanWatches p T doms l olds fuel (i + 1) kept prunes db
                      | none =>
                          match otherVal with
                          | some false =>
                              let nw := (kept.push id) ++ olds.extract (i + 1) olds.size
                              let db := { db with watch := db.watch.set! l.idx nw }
                              (db, .conflict sc.e id)
                          | _ =>
                              scanWatches p T doms l olds fuel (i + 1) (kept.push id)
                                (prunes.push (other, id)) db
            else
              scanWatches p T doms l olds fuel (i + 1) kept prunes db
      else
        ({ db with watch := db.watch.set! l.idx kept }, .prune prunes)

/-- The raw scan performed by `propagateLiteral`, before output shaping.
Exposed privately so the proofs can name the scan state. -/
private def propagateScan (p : CompiledProblem DomConstraint) (T : LitTable)
    (db : ClauseDB p T) (doms : Array DomC) (l : PLit) :
    ClauseDB p T × WPropOut p T :=
  let db := db.ensureWatch (l.idx + 1)
  let olds := db.watchList l.idx
  scanWatches p T doms l olds olds.size 0 #[] #[] db

/-- Propagate a literal that just became false (the caller passes the
literal itself, not its negation).  Clause ids are returned for prunings;
the reason is the clause itself. -/
def ClauseDB.propagateLiteral (p : CompiledProblem DomConstraint) (T : LitTable)
    (db : ClauseDB p T) (doms : Array DomC) (l : PLit) :
    ClauseDB p T × WPropOut p T :=
  let r := propagateScan p T db doms l
  (r.1, r.2.shape)

/-! ## Unit propagation -/

/-- Fuel-based scan of the clause array for unit clauses.  It never modifies
the database; `propagateUnits` only reports prunings/conflicts. -/
private def unitsScan (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (db : ClauseDB p T) :
    Nat → Nat → Array (PLit × Nat) → ClauseDB p T × WPropOut p T
  | 0, _, prunes => (db, .prune prunes)
  | fuel + 1, i, prunes =>
      if i < db.clauses.size then
        match db.clauses[i]? with
        | some sc =>
            if sc.deleted || sc.e.lits.size != 1 then
              unitsScan p T doms db fuel (i + 1) prunes
            else
              match sc.e.lits[0]? with
              | some l =>
                  match litValueC doms l with
                  | some true => unitsScan p T doms db fuel (i + 1) prunes
                  | some false => (db, .conflict sc.e i)
                  | none => unitsScan p T doms db fuel (i + 1) (prunes.push (l, i))
              | none => unitsScan p T doms db fuel (i + 1) prunes
        | none => unitsScan p T doms db fuel (i + 1) prunes
      else (db, .prune prunes)

/-- Propagate all original/learned unit clauses once (entry and after an
explicit unit addition). -/
def ClauseDB.propagateUnits (p : CompiledProblem DomConstraint) (T : LitTable)
    (db : ClauseDB p T) (doms : Array DomC) : ClauseDB p T × WPropOut p T :=
  let r := unitsScan p T doms db db.clauses.size 0 #[]
  (r.1, r.2.shape)

/-! ## Canonicalisation across the propagator boundary -/

/-- Re-intern one packed literal in the live table. -/
def canonLit (st : EngineState p T) (l : PLit) : PLit × EngineState p T :=
  let (l', tab) := st.table.intern l.lit
  (l', { st with table := tab })

/-- Runtime twin of `canonLit` that passes the table fields separately. -/
@[inline] def canonLitFast (st : EngineState p T) (l : PLit) : PLit × EngineState p T :=
  let (l', tab) := LitTable.internOneFast st.table.lits st.table.lookup l.lit
  (l', { st with table := tab })

/-- The fast canonicaliser is the reference one. -/
theorem canonLitFast_eq (st : EngineState p T) (l : PLit) :
    canonLitFast st l = canonLit st l := by
  unfold canonLitFast canonLit
  rw [LitTable.internOneFast_eq]

/-- Compile `canonLit` as the field-threading twin; proofs keep the
reference definition. -/
@[csimp] theorem canonLit_eq_fast : @canonLit = @canonLitFast := by
  funext p T st l
  exact (canonLitFast_eq st l).symm

/-- The literal component of a canonicalised literal is unchanged. -/
theorem canonLit_lit (st : EngineState p T) (l : PLit) :
    (canonLit st l).1.lit = l.lit := by
  unfold canonLit
  exact LitTable.intern_fst_lit st.table l.lit

/-- The first component of `canonLit` is the interned pack. -/
theorem canonLit_fst (st : EngineState p T) (l : PLit) :
    (canonLit st l).1 = (st.table.intern l.lit).1 := by
  unfold canonLit
  rfl

/-- The table of the resulting state is the interned table. -/
theorem canonLit_table (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.table = (st.table.intern l.lit).2 := by
  unfold canonLit
  rfl

/-- `canonLit` extends the literal table append-only. -/
theorem canonLit_table_append_only (st : EngineState p T) (l : PLit) :
    st.table.lits.toList <+: (canonLit st l).2.table.lits.toList := by
  rw [canonLit_table]
  exact LitTable.intern_append_only st.table l.lit

/-- `canonLit` preserves the intern-table invariant. -/
theorem canonLit_tableWF (st : EngineState p T) (l : PLit)
    (hT : st.table.TableWF) : (canonLit st l).2.table.TableWF := by
  rw [canonLit_table]
  exact LitTable.intern_tableWF hT

/-- The canonicalised literal is well-formed in the resulting table. -/
theorem canonLit_wf (st : EngineState p T) (l : PLit)
    (hT : st.table.TableWF) : (canonLit st l).2.table.WF (canonLit st l).1 := by
  rw [canonLit_fst, canonLit_table]
  exact LitTable.intern_wf hT

/-- The auxiliary interning of a clause's decoded literals. -/
def canonClauseAux (st : EngineState p T) (c : EClause p T) :
    Array PLit × LitTable :=
  st.table.internArray (c.lits.map PLit.decode)

/-- Interning the decoded literals preserves the decoded literal list. -/
theorem canonClauseAux_lits (st : EngineState p T) (c : EClause p T) :
    (canonClauseAux st c).1.toList.map PLit.decode =
      c.lits.toList.map PLit.decode := by
  unfold canonClauseAux
  rw [LitTable.internArray_lits, Array.toList_map]

/-- Pointwise form of the decoded-list equality, in the shape used by
`EClause.reindex`. -/
theorem canonPointwise {c : EClause p T} {lits : Array PLit}
    (h : lits.toList.map PLit.decode = c.lits.toList.map PLit.decode) :
    ∀ i : Nat, lits[i]?.map PLit.decode = c.lits[i]?.map PLit.decode := by
  intro i
  rw [← Array.getElem?_toList, ← Array.getElem?_toList]
  have h' := congrArg (fun l : List Literal => l[i]?) h
  simpa only [List.getElem?_map] using h'

/-- Re-intern every literal of a reason/conflict clause.  The denotations
are unchanged, so the carried entailment proof is transported by
`EClause.reindex` through `LitTable.decodeClause_canonical`. -/
def canonClause (st : EngineState p T) (c : EClause p T) :
    EClause p T × EngineState p T :=
  (c.reindex (canonClauseAux st c).1
      (canonPointwise (canonClauseAux_lits st c)),
    { st with table := (canonClauseAux st c).2 })

/-- Table-level form of `canonClauseAux`: `T` is the clause's table type
and `T'` the live table value. -/
def canonClauseTab (T : LitTable) (T' : LitTable) (c : EClause p T) :
    Array PLit × LitTable :=
  T'.internArray (c.lits.map PLit.decode)

/-- Decoded lits are preserved by the table-level canonicaliser. -/
theorem canonClauseTab_lits (T : LitTable) (T' : LitTable) (c : EClause p T) :
    (canonClauseTab T T' c).1.toList.map PLit.decode =
      c.lits.toList.map PLit.decode := by
  unfold canonClauseTab
  rw [LitTable.internArray_lits, Array.toList_map]

/-- Runtime twin of `canonClause` that destructures the state before
canonicalising.  Passing the whole state to `canonClauseAux` makes the
compiler keep a reference to the state across the call, so the literal
array and lookup table enter the interner shared and every append copies
the whole array.  Destructuring transfers ownership of the table. -/
@[inline] def canonClauseFast (st : EngineState p T) (c : EClause p T) :
    EClause p T × EngineState p T :=
  match st with
  | ⟨table, doms, trail, levelStart, level, changeIndex, db, reasons, props,
      subs, queueHigh, queueLow, inQueue, activity, activityHeap, phases,
      restarts, nextReduce, stats⟩ =>
    let r := canonClauseTab T table c
    (c.reindex r.1 (canonPointwise (canonClauseTab_lits T table c)),
      ⟨r.2, doms, trail, levelStart, level, changeIndex, db, reasons, props,
        subs, queueHigh, queueLow, inQueue, activity, activityHeap, phases,
        restarts, nextReduce, stats⟩)

/-- The fast canonicaliser is the reference one. -/
theorem canonClauseFast_eq (st : EngineState p T) (c : EClause p T) :
    canonClauseFast st c = canonClause st c := by
  cases st with
  | mk table doms trail levelStart level changeIndex db reasons props subs
      queueHigh queueLow inQueue activity activityHeap phases restarts
      nextReduce stats =>
    simp [canonClauseFast, canonClause, canonClauseAux, canonClauseTab,
      EClause.reindex]

/-- Compile `canonClause` as the ownership-preserving twin; proofs keep
the reference definition. -/
@[csimp] theorem canonClause_eq_fast :
    @canonClause = @canonClauseFast := by
  funext p T st c
  exact (canonClauseFast_eq st c).symm

/-- The literal array of the canonicalised clause. -/
theorem canonClause_fst_lits (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).1.lits = (canonClauseAux st c).1 := by
  unfold canonClause
  dsimp only
  rfl

/-- The table of the resulting state. -/
theorem canonClause_table (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.table = (canonClauseAux st c).2 := by
  unfold canonClause
  rfl

/-- `canonClause` preserves the decoded clause pointwise. -/
theorem canonClause_lits_decode (st : EngineState p T) (c : EClause p T) :
    ∀ i : Nat,
      ((canonClause st c).1.lits[i]?).map PLit.decode =
        (c.lits[i]?).map PLit.decode := by
  intro i
  rw [canonClause_fst_lits]
  exact canonPointwise (canonClauseAux_lits st c) i

/-- `canonClause` preserves the clause length. -/
theorem canonClause_lits_size (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).1.lits.size = c.lits.size := by
  rw [canonClause_fst_lits, ← Array.length_toList, ← Array.length_toList]
  have h := canonClauseAux_lits st c
  have := congrArg List.length h
  simpa using this

/-- `canonClause` preserves the length and the pointwise literal
denotation of the clause. -/
theorem canonClause_lits (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).1.lits.size = c.lits.size ∧
      ∀ (i : Nat) (q : PLit), (canonClause st c).1.lits[i]? = some q →
        ∃ q0, c.lits[i]? = some q0 ∧ q.lit = q0.lit := by
  constructor
  · exact canonClause_lits_size st c
  · intro i q hq
    have hd := canonClause_lits_decode st c i
    rw [hq] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    cases h0 : c.lits[i]? with
    | none => rw [h0] at hd; simp at hd
    | some q0 =>
        exact ⟨q0, rfl, by rw [h0] at hd; simpa [PLit.decode] using hd⟩

/-- `canonClause` extends the literal table append-only. -/
theorem canonClause_table_append_only (st : EngineState p T) (c : EClause p T) :
    st.table.lits.toList <+: (canonClause st c).2.table.lits.toList := by
  rw [canonClause_table]
  exact LitTable.internArray_append_only st.table (c.lits.map PLit.decode)

/-- `canonClause` preserves the intern-table invariant. -/
theorem canonClause_tableWF (st : EngineState p T) (c : EClause p T)
    (hT : st.table.TableWF) : (canonClause st c).2.table.TableWF := by
  rw [canonClause_table]
  exact LitTable.internArray_tableWF hT (c.lits.map PLit.decode)

/-- Every literal of the canonicalised clause is well-formed in the
resulting table. -/
theorem canonClause_wf (st : EngineState p T) (c : EClause p T)
    (hT : st.table.TableWF) :
    ∀ (i : Nat) (q : PLit), (canonClause st c).1.lits[i]? = some q →
      (canonClause st c).2.table.WF q := by
  intro i q hq
  rw [canonClause_fst_lits] at hq
  rw [canonClause_table]
  exact LitTable.internArray_wf hT (c.lits.map PLit.decode) i q hq

/-- The canonicalised clause is still entailed (its proof is the transported
proof of the input clause). -/
theorem canonClause_entailed (st : EngineState p T) (c : EClause p T) :
    Entailed p (st.table.decodeClause (canonClause st c).1.lits) :=
  (canonClause st c).1.ent

/-- The clause a trail entry's `ReasonRef` points at, when it has one. -/
def reasonClause? (st : EngineState p T) (r : ReasonRef) : Option (EClause p T) :=
  match r with
  | .decision => none
  | .learned id => (st.db.clauses[id]?).map (fun sc => sc.e)
  | .reason id => st.reasons[id]?

/-- A decision has no reason clause. -/
theorem reasonClause?_none_decision (st : EngineState p T) :
    reasonClause? st .decision = none := rfl

/-- Computation rule for a learned-clause reference. -/
theorem reasonClause?_learned (st : EngineState p T) (id : Nat) :
    reasonClause? st (.learned id) = (st.db.clauses[id]?).map (fun sc => sc.e) := rfl

/-- Computation rule for a transient-reason reference. -/
theorem reasonClause?_reason (st : EngineState p T) (id : Nat) :
    reasonClause? st (.reason id) = st.reasons[id]? := rfl

/-- A stored clause is returned for its slot regardless of its `deleted`
flag: a deleted clause's proof is still valid. -/
theorem reasonClause?_learned_some (st : EngineState p T) (id : Nat)
    (sc : StoredClause p T) (h : st.db.clauses[id]? = some sc) :
    reasonClause? st (.learned id) = some sc.e := by
  rw [reasonClause?_learned, h]
  rfl

/-- Every clause returned by `reasonClause?` is entailed by the problem.
This is the public reason API used by N8/N9. -/
theorem reasonClause?_entailed (st : EngineState p T) (r : ReasonRef)
    (c : EClause p T) (h : reasonClause? st r = some c) :
    Entailed p (st.table.decodeClause c.lits) :=
  c.ent

/-! ## The clause-database invariant -/

/-- Number of deleted slots. -/
def ClauseDB.deletedCount (db : ClauseDB p T) : Nat :=
  db.clauses.countP (fun sc => sc.deleted)

/-- Number of live (non-deleted) slots. -/
def ClauseDB.liveCount (db : ClauseDB p T) : Nat :=
  db.clauses.size - ClauseDB.deletedCount db

/-- `id` occurs in the watch list of packed index `i`. -/
def ClauseDB.WatchesAt (db : ClauseDB p T) (i id : Nat) : Prop :=
  id ∈ db.watchList i

/-- The clause `sc` occurs in the watch lists of both of its watched
positions. -/
def ClauseDB.WatchedBy (db : ClauseDB p T) (id : Nat) (sc : StoredClause p T) : Prop :=
  (∀ q, sc.e.lits[sc.w1]? = some q → db.WatchesAt q.idx id) ∧
    (∀ q, sc.e.lits[sc.w2]? = some q → db.WatchesAt q.idx id)

/-- Structural clause-database invariant.

* every watch-list entry is a valid clause slot;
* the watched positions of a live clause of size at least two are in range;
* a live clause of size at least two occurs in the watch lists of both of its
  watched literals (stale entries elsewhere and deleted clauses are allowed);
* `live` is the exact number of non-deleted slots;
* the free list contains exactly reusable (deleted) slots, without
  duplicates. -/
structure ClauseDB.Inv (db : ClauseDB p T) : Prop where
  watch_lt : ∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
    ∀ id ∈ ids, id < db.clauses.size
  pos_lt : ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size →
      sc.w1 < sc.e.lits.size ∧ sc.w2 < sc.e.lits.size
  watches : ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size → db.WatchedBy id sc
  live_eq : db.live = db.liveCount
  free_deleted : ∀ id, id ∈ db.free → ∃ sc, db.clauses[id]? = some sc ∧ sc.deleted = true
  free_nodup : db.free.toList.Nodup

/-- `Inv` with the watch-entry obligation suspended for one slot.  This is
the invariant between installing a clause in the slot array and appending
its two watch entries. -/
def ClauseDB.InvExcept (db : ClauseDB p T) (except : Nat) : Prop :=
  (∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
    ∀ id ∈ ids, id < db.clauses.size) ∧
  (∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size →
      sc.w1 < sc.e.lits.size ∧ sc.w2 < sc.e.lits.size) ∧
  (∀ (id : Nat) (sc : StoredClause p T), id ≠ except → db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size → db.WatchedBy id sc) ∧
  db.live = db.liveCount ∧
  (∀ id, id ∈ db.free → ∃ sc, db.clauses[id]? = some sc ∧ sc.deleted = true) ∧
  db.free.toList.Nodup

/-- The full invariant is an `InvExcept` for every slot. -/
theorem ClauseDB.Inv.toInvExcept (db : ClauseDB p T) (h : db.Inv) (except : Nat) :
    db.InvExcept except :=
  ⟨h.watch_lt, h.pos_lt, fun id sc _ hcl hdel hsz => h.watches id sc hcl hdel hsz,
    h.live_eq, h.free_deleted, h.free_nodup⟩

/-- Recover the full invariant from `InvExcept` once the excepted slot's
watch entries are installed. -/
theorem ClauseDB.InvExcept.toInv (db : ClauseDB p T) (except : Nat)
    (h : db.InvExcept except)
    (hnew : ∀ sc, db.clauses[except]? = some sc → sc.deleted = false →
      2 ≤ sc.e.lits.size → db.WatchedBy except sc) :
    db.Inv := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  intro id sc hcl hdel hsz
  by_cases hid : id = except
  · subst id
    exact hnew sc hcl hdel hsz
  · exact h.2.2.1 id sc hid hcl hdel hsz

/-- `ensureWatch` preserves watch membership. -/
theorem ClauseDB.watchesAt_ensureWatch (db : ClauseDB p T) (n i id : Nat)
    (h : db.WatchesAt i id) : (db.ensureWatch n).WatchesAt i id :=
  ClauseDB.ensureWatch_mem db n i id h

/-- Appending an id to one watch row preserves all existing memberships. -/
theorem ClauseDB.watchesAt_push (db : ClauseDB p T) (j id' i id : Nat)
    (h : db.WatchesAt i id) :
    ({ db with watch := db.watch.set! j ((db.watch.getD j #[]).push id') }).WatchesAt i id := by
  unfold ClauseDB.WatchesAt ClauseDB.watchList at h ⊢
  dsimp only
  by_cases hij : i = j
  · subst j
    by_cases hlt : i < db.watch.size
    · rw [array_getD_set!_self (xs := db.watch) (i := i)
        (v := (db.watch.getD i #[]).push id') (d := #[]) hlt]
      exact Array.mem_push.mpr (Or.inl h)
    · have hnone : db.watch.getD i #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (Nat.le_of_not_lt hlt)]
        rfl
      rw [hnone] at h
      simp at h
  · rw [array_getD_set!_ne (xs := db.watch) (i := j) (j := i)
      (v := (db.watch.getD j #[]).push id') (d := #[]) (h := fun hji => hij hji.symm)]
    exact h

/-- Appending an id to its own watch row makes it a member. -/
theorem ClauseDB.watchesAt_set_push_self (db : ClauseDB p T) (j id' : Nat)
    (h : j < db.watch.size) :
    ({ db with watch := db.watch.set! j ((db.watch.getD j #[]).push id') }).WatchesAt j id' := by
  unfold ClauseDB.WatchesAt ClauseDB.watchList
  dsimp only
  rw [array_getD_set!_self (xs := db.watch) (i := j)
    (v := (db.watch.getD j #[]).push id') (d := #[]) h]
  exact Array.mem_push.mpr (Or.inr rfl)

set_option maxHeartbeats 1000000 in
/-- `addWatchPair` preserves all existing watch memberships. -/
theorem ClauseDB.addWatchPair_watchesAt (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) (i x : Nat) (h : db.WatchesAt i x) :
    (db.addWatchPair id l0 l1).WatchesAt i x := by
  unfold ClauseDB.addWatchPair
  dsimp only
  exact ClauseDB.watchesAt_push
    (db := { db.ensureWatch (max l0.idx l1.idx + 1) with
      watch := (db.ensureWatch (max l0.idx l1.idx + 1)).watch.set! l0.idx
        (((db.ensureWatch (max l0.idx l1.idx + 1)).watch.getD l0.idx #[]).push id) })
    l1.idx id i x
    (ClauseDB.watchesAt_push (db := db.ensureWatch (max l0.idx l1.idx + 1))
      l0.idx id i x
      (ClauseDB.watchesAt_ensureWatch db (max l0.idx l1.idx + 1) i x h))

set_option maxHeartbeats 1000000 in
/-- The left watched literal of the newly added clause is in its watch
list. -/
theorem ClauseDB.addWatchPair_watchesAt_left (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) : (db.addWatchPair id l0 l1).WatchesAt l0.idx id := by
  unfold ClauseDB.addWatchPair
  dsimp only
  exact ClauseDB.watchesAt_push
    (db := { db.ensureWatch (max l0.idx l1.idx + 1) with
      watch := (db.ensureWatch (max l0.idx l1.idx + 1)).watch.set! l0.idx
        (((db.ensureWatch (max l0.idx l1.idx + 1)).watch.getD l0.idx #[]).push id) })
    l1.idx id l0.idx id
    (ClauseDB.watchesAt_set_push_self (db := db.ensureWatch (max l0.idx l1.idx + 1))
      l0.idx id
      (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_left _ _))
        (ClauseDB.ensureWatch_size_ge db (max l0.idx l1.idx + 1))))

/-- The right watched literal of the newly added clause is in its watch
list. -/
theorem ClauseDB.addWatchPair_watchesAt_right (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) : (db.addWatchPair id l0 l1).WatchesAt l1.idx id := by
  unfold ClauseDB.addWatchPair
  dsimp only
  exact ClauseDB.watchesAt_set_push_self
    ({ db.ensureWatch (max l0.idx l1.idx + 1) with
      watch := (db.ensureWatch (max l0.idx l1.idx + 1)).watch.set! l0.idx
        (((db.ensureWatch (max l0.idx l1.idx + 1)).watch.getD l0.idx #[]).push id) })
    l1.idx id
    (by
      rw [Array.size_set!]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_max_right _ _))
        (ClauseDB.ensureWatch_size_ge db (max l0.idx l1.idx + 1)))

/-- Installing both watch entries makes the new clause watched by both of
its watched positions. -/
theorem ClauseDB.addWatchPair_watchedBy (db : ClauseDB p T) (id : Nat)
    (sc : StoredClause p T) (l0 l1 : PLit)
    (h0 : sc.e.lits[sc.w1]? = some l0) (h1 : sc.e.lits[sc.w2]? = some l1) :
    (db.addWatchPair id l0 l1).WatchedBy id sc := by
  constructor
  · intro q hq
    rw [h0] at hq
    have hq' : q = l0 := (Option.some.inj hq).symm
    subst q
    exact ClauseDB.addWatchPair_watchesAt_left db id l0 l1
  · intro q hq
    rw [h1] at hq
    have hq' : q = l1 := (Option.some.inj hq).symm
    subst q
    exact ClauseDB.addWatchPair_watchesAt_right db id l0 l1

/-- `addWatchPair` does not touch the clause array. -/
theorem ClauseDB.addWatchPair_clauses (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) :
    (db.addWatchPair id l0 l1).clauses = db.clauses := by
  unfold ClauseDB.addWatchPair ClauseDB.ensureWatch
  dsimp only
  split <;> rfl

/-- `addWatchPair` does not touch `live`. -/
theorem ClauseDB.addWatchPair_live (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) :
    (db.addWatchPair id l0 l1).live = db.live := by
  unfold ClauseDB.addWatchPair ClauseDB.ensureWatch
  dsimp only
  split <;> rfl

/-- `addWatchPair` does not touch the free list. -/
theorem ClauseDB.addWatchPair_free (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) :
    (db.addWatchPair id l0 l1).free = db.free := by
  unfold ClauseDB.addWatchPair ClauseDB.ensureWatch
  dsimp only
  split <;> rfl

/-! ### Counting helpers -/

/-- `deletedCount` is unchanged by overwriting a slot with a clause carrying
the same `deleted` flag. -/
theorem ClauseDB.deletedCount_set_same (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (hget : db.clauses[id]? = some sc)
    (hsize : id < db.clauses.size) (hdel : sc'.deleted = sc.deleted) :
    ({ db with clauses := db.clauses.set! id sc' }).deletedCount = db.deletedCount := by
  have hEq : db.clauses[id] = sc := by
    have h' := Array.getElem?_eq_getElem hsize
    rw [hget] at h'
    exact (Option.some.inj h').symm
  unfold ClauseDB.deletedCount
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  simp only [hsize, ↓reduceDIte]
  rw [Array.countP_set (p := fun sc => sc.deleted) hsize]
  rw [hEq, hdel]
  by_cases hd : sc.deleted
  · have hmem : sc ∈ db.clauses := by
      rw [Array.mem_iff_getElem?]
      exact ⟨id, hget⟩
    have hpos : 0 < db.deletedCount := by
      unfold ClauseDB.deletedCount
      rw [Array.countP_pos_iff]
      exact ⟨sc, hmem, hd⟩
    simp [hd]
    exact Nat.sub_add_cancel hpos
  · simp [hd]

/-- Overwriting a deleted slot by a live clause decrements `deletedCount`. -/
theorem ClauseDB.deletedCount_set_to_live (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (hget : db.clauses[id]? = some sc)
    (hsize : id < db.clauses.size) (hdel : sc.deleted = true)
    (hnew : sc'.deleted = false) :
    ({ db with clauses := db.clauses.set! id sc' }).deletedCount =
      db.deletedCount - 1 := by
  have hEq : db.clauses[id] = sc := by
    have h' := Array.getElem?_eq_getElem hsize
    rw [hget] at h'
    exact (Option.some.inj h').symm
  unfold ClauseDB.deletedCount
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  simp only [hsize, ↓reduceDIte]
  rw [Array.countP_set (p := fun sc => sc.deleted) hsize]
  rw [hEq, hdel, hnew]
  simp

/-- Overwriting a live slot by a deleted clause increments `deletedCount`. -/
theorem ClauseDB.deletedCount_set_to_deleted (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (hget : db.clauses[id]? = some sc)
    (hsize : id < db.clauses.size) (hdel : sc.deleted = false)
    (hnew : sc'.deleted = true) :
    ({ db with clauses := db.clauses.set! id sc' }).deletedCount =
      db.deletedCount + 1 := by
  have hEq : db.clauses[id] = sc := by
    have h' := Array.getElem?_eq_getElem hsize
    rw [hget] at h'
    exact (Option.some.inj h').symm
  unfold ClauseDB.deletedCount
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  simp only [hsize, ↓reduceDIte]
  rw [Array.countP_set (p := fun sc => sc.deleted) hsize]
  rw [hEq, hdel, hnew]
  simp

/-- Pushing a live clause leaves `deletedCount` unchanged. -/
theorem ClauseDB.deletedCount_push_live (db : ClauseDB p T)
    (sc : StoredClause p T) (hnew : sc.deleted = false) :
    ({ db with clauses := db.clauses.push sc }).deletedCount = db.deletedCount := by
  unfold ClauseDB.deletedCount
  rw [Array.countP_push]
  simp [hnew]

/-- Pushing a live clause increments `liveCount`. -/
theorem ClauseDB.liveCount_push_live (db : ClauseDB p T)
    (sc : StoredClause p T) (hnew : sc.deleted = false) :
    ({ db with clauses := db.clauses.push sc }).liveCount = db.liveCount + 1 := by
  have hle : db.deletedCount ≤ db.clauses.size := Array.countP_le_size
  unfold ClauseDB.liveCount
  rw [Array.size_push, ClauseDB.deletedCount_push_live db sc hnew]
  omega

/-- Reusing a deleted slot for a live clause increments `liveCount`. -/
theorem ClauseDB.liveCount_set_live (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (hget : db.clauses[id]? = some sc)
    (hsize : id < db.clauses.size) (hdel : sc.deleted = true)
    (hnew : sc'.deleted = false) :
    ({ db with clauses := db.clauses.set! id sc' }).liveCount = db.liveCount + 1 := by
  have hmem : sc ∈ db.clauses := by
    rw [Array.mem_iff_getElem?]
    exact ⟨id, hget⟩
  have hpos : 0 < db.deletedCount := by
    unfold ClauseDB.deletedCount
    rw [Array.countP_pos_iff]
    exact ⟨sc, hmem, hdel⟩
  have hle : db.deletedCount ≤ db.clauses.size := Array.countP_le_size
  unfold ClauseDB.liveCount
  rw [Array.size_set!, ClauseDB.deletedCount_set_to_live db id sc sc' hget hsize hdel hnew]
  omega

/-- Marking a live slot deleted decrements `liveCount`. -/
theorem ClauseDB.liveCount_set_deleted (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (hget : db.clauses[id]? = some sc)
    (hsize : id < db.clauses.size) (hdel : sc.deleted = false)
    (hnew : sc'.deleted = true) :
    ({ db with clauses := db.clauses.set! id sc' }).liveCount = db.liveCount - 1 := by
  have hmem : sc ∈ db.clauses := by
    rw [Array.mem_iff_getElem?]
    exact ⟨id, hget⟩
  have hlt : db.deletedCount < db.clauses.size := by
    rcases Nat.lt_or_ge db.deletedCount db.clauses.size with h | h
    · exact h
    · have heq : db.deletedCount = db.clauses.size := Nat.le_antisymm Array.countP_le_size h
      have heq' : db.clauses.countP (fun sc => sc.deleted) = db.clauses.size := by
        simpa [ClauseDB.deletedCount] using heq
      have hall := (Array.countP_eq_size (p := fun sc => sc.deleted)).mp heq' sc hmem
      simp [hdel] at hall
  unfold ClauseDB.liveCount
  rw [Array.size_set!, ClauseDB.deletedCount_set_to_deleted db id sc sc' hget hsize hdel hnew]
  omega

/-- The empty database satisfies the invariant. -/
theorem ClauseDB.inv_empty : (ClauseDB.empty (p := p) (T := T)).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids h
    simp [ClauseDB.empty] at h
  · intro id sc h
    simp [ClauseDB.empty] at h
  · intro id sc h
    simp [ClauseDB.empty] at h
  · simp [ClauseDB.empty, ClauseDB.liveCount, ClauseDB.deletedCount]
  · intro id h
    simp [ClauseDB.empty] at h
  · simp [ClauseDB.empty]

/-! ### Invariant preservation for slot reuse and push -/

/-- Reading `set!` at the written in-bounds index. -/
private theorem array_getElem?_set!_self {α : Type} (xs : Array α) (i : Nat)
    (v : α) (h : i < xs.size) : (xs.set! i v)[i]? = some v := by
  rw [array_getElem?_set!]
  simp [h]

/-- Reading `set!` away from the written index. -/
private theorem array_getElem?_set!_ne {α : Type} (xs : Array α) (i j : Nat)
    (v : α) (h : i ≠ j) : (xs.set! i v)[j]? = xs[j]? := by
  rw [array_getElem?_set!]
  simp [h]

/-- The last element of a duplicate-free array is not in its `pop`. -/
private theorem array_not_mem_pop_of_back?_eq_some {α : Type} {xs : Array α} {x : α}
    (h : xs.back? = some x) (hnodup : xs.toList.Nodup) : x ∉ xs.pop := by
  intro hx
  have hx' : x ∈ xs.pop := hx
  rw [Array.mem_iff_getElem?] at hx'
  obtain ⟨j, hj⟩ := hx'
  rw [Array.getElem?_pop] at hj
  by_cases hlt : j < xs.size - 1
  · rw [if_pos hlt] at hj
    have hlast : xs[xs.size - 1]? = some x := by
      rw [← Array.back?_eq_getElem?]
      exact h
    have hj' : xs.toList[j]? = some x := by
      simpa [Array.getElem?_toList] using hj
    have hl' : xs.toList[xs.size - 1]? = some x := by
      simpa [Array.getElem?_toList] using hlast
    have hidx := (List.getElem?_inj (l := xs.toList) (i := j) (j := xs.size - 1)
      (by simpa using Nat.lt_of_lt_of_le hlt (Nat.sub_le xs.size 1)) hnodup).mp
      (hj'.trans hl'.symm)
    omega
  · rw [if_neg hlt] at hj
    simp at hj

/-- Replacing a deleted slot by a live clause preserves `Inv` up to the
missing watch entries of the reused slot. -/
theorem ClauseDB.invExcept_reuse (db : ClauseDB p T) (id : Nat)
    (sc sc' : StoredClause p T) (h : db.Inv)
    (hget : db.clauses[id]? = some sc) (hdel : sc.deleted = true)
    (hnew : sc'.deleted = false) (hw1 : sc'.w1 = 0)
    (hw2 : sc'.w2 = if sc'.e.lits.size ≥ 2 then 1 else 0)
    (hfree : db.free.back? = some id) :
    (db.reuseBase id sc').InvExcept id := by
  unfold ClauseDB.reuseBase
  have hsize : id < db.clauses.size := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hget
    exact hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hrow x hx
    dsimp only at hrow ⊢
    have hxlt := h.watch_lt i ids hrow x hx
    rw [Array.size_set!]
    exact hxlt
  · intro j scj hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = id
    · subst j
      rw [array_getElem?_set!_self db.clauses id sc' hsize] at hrow
      have hscj : scj = sc' := (Option.some.inj hrow).symm
      subst scj
      constructor
      · rw [hw1]
        omega
      · rw [hw2]
        split <;> omega
    · rw [array_getElem?_set!_ne db.clauses id j sc' (fun h => hji h.symm)] at hrow
      exact h.pos_lt j scj hrow hlive hsz
  · intro j scj hjne hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = id
    · exact (hjne hji).elim
    · rw [array_getElem?_set!_ne db.clauses id j sc' (fun h => hji h.symm)] at hrow
      exact h.watches j scj hrow hlive hsz
  · change db.live + 1 = ({ db with clauses := db.clauses.set! id sc' }).liveCount
    rw [ClauseDB.liveCount_set_live db id sc sc' hget hsize hdel hnew, h.live_eq]
  · intro x hx
    dsimp only at hx
    have hxpop : x ∈ db.free.pop := hx
    have hxmem : x ∈ db.free := by
      have hx' : x ∈ db.free.pop := hxpop
      rw [Array.mem_iff_getElem?] at hx'
      obtain ⟨j, hj⟩ := hx'
      rw [Array.getElem?_pop] at hj
      rw [Array.mem_iff_getElem?]
      by_cases hlt : j < db.free.size - 1
      · rw [if_pos hlt] at hj
        exact ⟨j, hj⟩
      · rw [if_neg hlt] at hj
        simp at hj
    obtain ⟨sc0, hcl0, hdel0⟩ := h.free_deleted x hxmem
    have hid_not : id ∉ db.free.pop :=
      array_not_mem_pop_of_back?_eq_some (x := id) hfree h.free_nodup
    have hxne : x ≠ id := by
      intro hxid
      subst x
      exact hid_not hxpop
    refine ⟨sc0, ?_, hdel0⟩
    dsimp only
    rw [array_getElem?_set!_ne db.clauses id x sc' (fun h => hxne h.symm)]
    exact hcl0
  · dsimp only
    rw [Array.toList_pop]
    exact (List.dropLast_sublist _).nodup h.free_nodup

/-- Pushing a live clause preserves `Inv` up to the missing watch entries of
the new slot. -/
theorem ClauseDB.invExcept_push (db : ClauseDB p T) (sc : StoredClause p T)
    (h : db.Inv) (hnew : sc.deleted = false) (hw1 : sc.w1 = 0)
    (hw2 : sc.w2 = if sc.e.lits.size ≥ 2 then 1 else 0) :
    (db.pushBase sc).InvExcept db.clauses.size := by
  unfold ClauseDB.pushBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hrow x hx
    dsimp only at hrow ⊢
    have hxlt := h.watch_lt i ids hrow x hx
    rw [Array.size_push]
    omega
  · intro j scj hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = db.clauses.size
    · subst j
      rw [Array.getElem?_push, if_pos rfl] at hrow
      have hscj : scj = sc := (Option.some.inj hrow).symm
      subst scj
      constructor
      · rw [hw1]
        omega
      · rw [hw2]
        split <;> omega
    · rw [Array.getElem?_push, if_neg hji] at hrow
      exact h.pos_lt j scj hrow hlive hsz
  · intro j scj hjne hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = db.clauses.size
    · exact (hjne hji).elim
    · rw [Array.getElem?_push, if_neg hji] at hrow
      exact h.watches j scj hrow hlive hsz
  · change db.live + 1 = ({ db with clauses := db.clauses.push sc }).liveCount
    rw [ClauseDB.liveCount_push_live db sc hnew, h.live_eq]
  · intro x hx
    dsimp only at hx
    obtain ⟨sc0, hcl0, hdel0⟩ := h.free_deleted x hx
    have hxlt : x < db.clauses.size := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hcl0
      exact hlt
    refine ⟨sc0, ?_, hdel0⟩
    dsimp only
    rw [Array.getElem?_push, if_neg (by omega : x ≠ db.clauses.size)]
    exact hcl0
  · dsimp only
    exact h.free_nodup

/-! ### Watch-list membership helpers -/

/-- Membership in the `getD`-based watch list, in terms of the underlying
array lookup. -/
theorem ClauseDB.mem_watchList_iff (db : ClauseDB p T) (i x : Nat) :
    x ∈ db.watchList i ↔ ∃ ids, db.watch[i]? = some ids ∧ x ∈ ids := by
  unfold ClauseDB.watchList
  rw [Array.getD_eq_getD_getElem?]
  cases h : db.watch[i]? with
  | none => simp
  | some ids => simp [h]

/-- Overwriting a different watch row preserves membership. -/
theorem ClauseDB.watchesAt_set_other (db : ClauseDB p T) (j i id : Nat)
    (v : Array Nat) (hij : i ≠ j) (h : db.WatchesAt i id) :
    ({ db with watch := db.watch.set! j v }).WatchesAt i id := by
  unfold ClauseDB.WatchesAt ClauseDB.watchList at h ⊢
  dsimp only
  rw [array_getD_set!_ne (xs := db.watch) (i := j) (j := i) (v := v) (d := #[])
    (h := fun hji => hij hji.symm)]
  exact h

/-- Membership after appending to one watch row is either old membership or
the appended id. -/
theorem ClauseDB.watchesAt_set_push_old_or_eq (db : ClauseDB p T) (j id' i x : Nat)
    (h : ({ db with
      watch := db.watch.set! j ((db.watch.getD j #[]).push id') }).WatchesAt i x) :
    db.WatchesAt i x ∨ x = id' := by
  unfold ClauseDB.WatchesAt ClauseDB.watchList at h ⊢
  dsimp only at h ⊢
  rw [Array.getD_eq_getD_getElem?] at h ⊢
  rw [array_getElem?_set!] at h
  by_cases hij : j = i
  · subst i
    by_cases hlt : j < db.watch.size
    · simp [hlt, Array.mem_push] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · simp [hlt] at h ⊢
  · simp [hij] at h ⊢
    exact Or.inl h

/-- Membership in the result of `addWatchPair` is either old membership or
the newly added clause id. -/
theorem ClauseDB.addWatchPair_watchesAt_old_or_eq (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) (i x : Nat)
    (h : (db.addWatchPair id l0 l1).WatchesAt i x) :
    db.WatchesAt i x ∨ x = id := by
  unfold ClauseDB.addWatchPair at h
  dsimp only at h
  rcases ClauseDB.watchesAt_set_push_old_or_eq
    (db := { db.ensureWatch (max l0.idx l1.idx + 1) with
      watch := (db.ensureWatch (max l0.idx l1.idx + 1)).watch.set! l0.idx
        (((db.ensureWatch (max l0.idx l1.idx + 1)).watch.getD l0.idx #[]).push id) })
    l1.idx id i x h with h | h
  · rcases ClauseDB.watchesAt_set_push_old_or_eq
      (db := db.ensureWatch (max l0.idx l1.idx + 1)) l0.idx id i x h with h | h
    · left
      unfold ClauseDB.WatchesAt at h ⊢
      rwa [ClauseDB.ensureWatch_watchList] at h
    · exact Or.inr h
  · exact Or.inr h

/-- `addWatchPair` keeps every watch-list entry below `clauses.size`. -/
theorem ClauseDB.addWatchPair_watch_lt (db : ClauseDB p T) (id : Nat)
    (l0 l1 : PLit) (hid : id < db.clauses.size)
    (h : ∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
      ∀ x ∈ ids, x < db.clauses.size) :
    ∀ (i : Nat) (ids : Array Nat), (db.addWatchPair id l0 l1).watch[i]? = some ids →
      ∀ x ∈ ids, x < db.clauses.size := by
  intro i ids hrow x hx
  have hx' : (db.addWatchPair id l0 l1).WatchesAt i x := by
    unfold ClauseDB.WatchesAt
    rw [ClauseDB.mem_watchList_iff]
    exact ⟨ids, hrow, hx⟩
  rcases ClauseDB.addWatchPair_watchesAt_old_or_eq db id l0 l1 i x hx' with h' | rfl
  · unfold ClauseDB.WatchesAt at h'
    rw [ClauseDB.mem_watchList_iff] at h'
    obtain ⟨ids', hrow', hmem⟩ := h'
    exact h i ids' hrow' x hmem
  · exact hid

/-- `WatchedBy` is monotone in watch-list membership. -/
theorem ClauseDB.WatchedBy.mono {db db' : ClauseDB p T} {id : Nat}
    {sc : StoredClause p T} (h : db.WatchedBy id sc)
    (hmono : ∀ i x, db.WatchesAt i x → db'.WatchesAt i x) : db'.WatchedBy id sc :=
  ⟨fun q hq => hmono _ _ (h.1 q hq), fun q hq => hmono _ _ (h.2 q hq)⟩

/-- Installing a watch pair preserves `InvExcept`. -/
theorem ClauseDB.InvExcept.addWatchPair (db : ClauseDB p T) (except : Nat)
    (h : db.InvExcept except) (id : Nat) (l0 l1 : PLit)
    (hid : id < db.clauses.size) :
    (db.addWatchPair id l0 l1).InvExcept except := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hrow x hx
    have hxlt : x < db.clauses.size :=
      ClauseDB.addWatchPair_watch_lt db id l0 l1 hid h.1 i ids hrow x hx
    rwa [ClauseDB.addWatchPair_clauses]
  · intro j scj hrow hlive hsz
    rw [ClauseDB.addWatchPair_clauses] at hrow
    exact h.2.1 j scj hrow hlive hsz
  · intro j scj hjne hrow hlive hsz
    rw [ClauseDB.addWatchPair_clauses] at hrow
    exact ClauseDB.WatchedBy.mono (h.2.2.1 j scj hjne hrow hlive hsz)
      (fun i x hx => ClauseDB.addWatchPair_watchesAt db id l0 l1 i x hx)
  · have hlc : (db.addWatchPair id l0 l1).liveCount = db.liveCount := by
      unfold ClauseDB.liveCount ClauseDB.deletedCount
      rw [ClauseDB.addWatchPair_clauses]
    rw [ClauseDB.addWatchPair_live, hlc]
    exact h.2.2.2.1
  · intro x hx
    rw [ClauseDB.addWatchPair_free] at hx
    obtain ⟨sc0, hcl0, hdel0⟩ := h.2.2.2.2.1 x hx
    refine ⟨sc0, ?_, hdel0⟩
    rwa [ClauseDB.addWatchPair_clauses]
  · simpa [ClauseDB.addWatchPair_free] using h.2.2.2.2.2

/-! ### Adding a clause -/

/-- Installing the two watches of a size-≥2 clause. -/
theorem ClauseDB.installWatches_eq_addWatchPair (db : ClauseDB p T) (id : Nat)
    (e : EClause p T) (l0 l1 : PLit) (hge : 2 ≤ e.lits.size)
    (h0 : e.lits[0]? = some l0) (h1 : e.lits[1]? = some l1) :
    db.installWatches id e = db.addWatchPair id l0 l1 := by
  unfold ClauseDB.installWatches
  simp [hge, h0, h1]

/-- `installWatches` is the identity below size two. -/
theorem ClauseDB.installWatches_eq_self (db : ClauseDB p T) (id : Nat)
    (e : EClause p T) (hlt : ¬ 2 ≤ e.lits.size) :
    db.installWatches id e = db := by
  unfold ClauseDB.installWatches
  simp [hlt]

/-- Turning an `InvExcept` for a freshly installed slot into a full invariant
once its watch entries are installed. -/
theorem ClauseDB.installWatches_inv (db : ClauseDB p T) (id : Nat)
    (e : EClause p T) (sc : StoredClause p T) (h : db.InvExcept id)
    (hget : db.clauses[id]? = some sc) (he : sc.e = e)
    (hdel : sc.deleted = false) (hw1 : sc.w1 = 0)
    (hw2 : sc.w2 = if e.lits.size ≥ 2 then 1 else 0)
    (hid : id < db.clauses.size) :
    (db.installWatches id e).Inv := by
  by_cases hge : 2 ≤ e.lits.size
  · have h0 : ∃ l0, e.lits[0]? = some l0 := by
      have hlt : 0 < e.lits.size := by omega
      exact ⟨e.lits[0], by rw [Array.getElem?_eq_getElem hlt]⟩
    have h1 : ∃ l1, e.lits[1]? = some l1 := by
      have hlt : 1 < e.lits.size := by omega
      exact ⟨e.lits[1], by rw [Array.getElem?_eq_getElem hlt]⟩
    obtain ⟨l0, h0⟩ := h0
    obtain ⟨l1, h1⟩ := h1
    rw [ClauseDB.installWatches_eq_addWatchPair db id e l0 l1 hge h0 h1]
    apply ClauseDB.InvExcept.toInv _ id (ClauseDB.InvExcept.addWatchPair db id h id l0 l1 hid)
    intro scj hcl hlive hsz
    rw [ClauseDB.addWatchPair_clauses] at hcl
    have hscj : scj = sc := by
      rw [hget] at hcl
      exact (Option.some.inj hcl).symm
    subst scj
    apply ClauseDB.addWatchPair_watchedBy
    · rw [hw1, he]
      exact h0
    · rw [hw2, he]
      simpa [hge] using h1
  · rw [ClauseDB.installWatches_eq_self db id e hge]
    apply ClauseDB.InvExcept.toInv db id h
    intro scj hcl hlive hsz
    have hscj : scj = sc := by
      rw [hget] at hcl
      exact (Option.some.inj hcl).symm
    subst scj
    rw [he] at hsz
    exact (hge hsz).elim

/-- `add` preserves the clause-database invariant. -/
theorem ClauseDB.add_inv (db : ClauseDB p T) (e : EClause p T) (h : db.Inv) :
    (db.add e).1.Inv := by
  unfold ClauseDB.add
  dsimp only
  split
  · rename_i id hfree
    have hidmem : id ∈ db.free := Array.mem_of_back? hfree
    obtain ⟨scOld, hget, hdel⟩ := h.free_deleted id hidmem
    have hsize : id < db.clauses.size := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hget
      exact hlt
    have hExcept : (db.reuseBase id (ClauseDB.newStored e)).InvExcept id :=
      ClauseDB.invExcept_reuse db id scOld (ClauseDB.newStored e) h hget hdel
        rfl rfl rfl hfree
    refine ClauseDB.installWatches_inv (db.reuseBase id (ClauseDB.newStored e)) id e
      (ClauseDB.newStored e) hExcept ?_ rfl rfl rfl rfl ?_
    · unfold ClauseDB.reuseBase
      rw [array_getElem?_set!_self db.clauses id (ClauseDB.newStored e) hsize]
    · unfold ClauseDB.reuseBase
      rw [Array.size_set!]
      exact hsize
  · rename_i hfree
    have hExcept : (db.pushBase (ClauseDB.newStored e)).InvExcept db.clauses.size :=
      ClauseDB.invExcept_push db (ClauseDB.newStored e) h rfl rfl rfl
    refine ClauseDB.installWatches_inv (db.pushBase (ClauseDB.newStored e))
      db.clauses.size e (ClauseDB.newStored e) hExcept ?_ rfl rfl rfl rfl ?_
    · unfold ClauseDB.pushBase
      rw [Array.getElem?_push]
      simp
    · unfold ClauseDB.pushBase
      rw [Array.size_push]
      omega

/-- A live clause implies a positive `live` count. -/
theorem ClauseDB.Inv.live_pos_of_live (db : ClauseDB p T) (id : Nat)
    (sc : StoredClause p T) (h : db.Inv) (hget : db.clauses[id]? = some sc)
    (hdel : sc.deleted = false) : 0 < db.live := by
  have hsize : id < db.clauses.size := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hget
    exact hlt
  have hmem : sc ∈ db.clauses := by
    rw [Array.mem_iff_getElem?]
    exact ⟨id, hget⟩
  have hdc_lt : db.deletedCount < db.clauses.size := by
    rcases Nat.lt_or_ge db.deletedCount db.clauses.size with hlt | hge
    · exact hlt
    · have heq : db.deletedCount = db.clauses.size := Nat.le_antisymm Array.countP_le_size hge
      have heq' : db.clauses.countP (fun sc => sc.deleted) = db.clauses.size := by
        simpa [ClauseDB.deletedCount] using heq
      have hall := (Array.countP_eq_size (p := fun sc => sc.deleted)).mp heq' sc hmem
      simp [hdel] at hall
  rw [h.live_eq]
  unfold ClauseDB.liveCount
  omega

/-- Marking one live slot deleted preserves the invariant. -/
theorem ClauseDB.delete_live_inv (db : ClauseDB p T) (id : Nat)
    (sc : StoredClause p T) (h : db.Inv) (hget : db.clauses[id]? = some sc)
    (hdel : sc.deleted = false) :
    ({ db with clauses := db.clauses.set! id ({ sc with deleted := true }), free := db.free.push id, live := db.live - 1 }).Inv := by
  have hsize : id < db.clauses.size := by
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hget
    exact hlt
  have hidnot : id ∉ db.free := by
    intro hmem
    obtain ⟨sc0, hcl0, hdel0⟩ := h.free_deleted id hmem
    rw [hget] at hcl0
    have hsc0 : sc0 = sc := (Option.some.inj hcl0).symm
    subst sc0
    rw [hdel] at hdel0
    simp at hdel0
  let sc' : StoredClause p T := { sc with deleted := true }
  have hsc'_del : sc'.deleted = true := rfl
  have hsc'_w1 : sc'.w1 = sc.w1 := rfl
  have hsc'_w2 : sc'.w2 = sc.w2 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hrow x hx
    dsimp only at hrow ⊢
    have hxlt := h.watch_lt i ids hrow x hx
    rw [Array.size_set!]
    exact hxlt
  · intro j scj hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = id
    · subst j
      rw [array_getElem?_set!_self db.clauses id sc' hsize] at hrow
      have hscj : scj = sc' := (Option.some.inj hrow).symm
      subst scj
      simp [hsc'_del] at hlive
    · rw [array_getElem?_set!_ne db.clauses id j sc'
        (fun h => hji h.symm)] at hrow
      exact h.pos_lt j scj hrow hlive hsz
  · intro j scj hrow hlive hsz
    dsimp only at hrow
    by_cases hji : j = id
    · subst j
      rw [array_getElem?_set!_self db.clauses id sc' hsize] at hrow
      have hscj : scj = sc' := (Option.some.inj hrow).symm
      subst scj
      simp [hsc'_del] at hlive
    · rw [array_getElem?_set!_ne db.clauses id j sc'
        (fun h => hji h.symm)] at hrow
      exact h.watches j scj hrow hlive hsz
  · change db.live - 1 = ({ db with clauses := db.clauses.set! id sc' }).liveCount
    rw [ClauseDB.liveCount_set_deleted db id sc sc' hget hsize hdel hsc'_del]
    exact congrArg (fun n => n - 1) h.live_eq
  · intro x hx
    dsimp only at hx
    rw [Array.mem_push] at hx
    rcases hx with hx | hxid
    · obtain ⟨sc0, hcl0, hdel0⟩ := h.free_deleted x hx
      by_cases hxi : x = id
      · subst x
        rw [hget] at hcl0
        have hsc0 : sc0 = sc := (Option.some.inj hcl0).symm
        subst sc0
        rw [hdel] at hdel0
        simp at hdel0
      · refine ⟨sc0, ?_, hdel0⟩
        dsimp only
        rw [array_getElem?_set!_ne db.clauses id x sc'
          (fun h => hxi h.symm)]
        exact hcl0
    · subst x
      refine ⟨sc', ?_, hsc'_del⟩
      dsimp only
      rw [array_getElem?_set!_self db.clauses id sc' hsize]
  · dsimp only
    rw [Array.toList_push]
    refine (List.nodup_append).mpr ⟨h.free_nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    have ha' : a ∈ db.free := by
      simpa using ha
    exact fun hab => hidnot (hab ▸ ha')

/-- `delete` preserves the clause-database invariant. -/
theorem ClauseDB.delete_inv (db : ClauseDB p T) (id : Nat) (h : db.Inv) :
    (db.delete id).Inv := by
  unfold ClauseDB.delete
  split
  · rename_i sc hget
    by_cases hb : sc.deleted
    · simpa [hb] using h
    · have hdel : sc.deleted = false := by
        cases hd : sc.deleted
        · rfl
        · exact (hb hd).elim
      have hne : db.live ≠ 0 := Nat.ne_of_gt (ClauseDB.Inv.live_pos_of_live db id sc h hget hdel)
      simpa [hb, hne] using ClauseDB.delete_live_inv db id sc h hget hdel
  · exact h

/-! ## Unit propagation: unchanged database and result specifications -/

/-- A pruning list is sound when every entry names a literal occurrence of
a live stored clause.

The task statement writes `l ∈ sc.e.lits.map PLit.decode`; since `l` is a
`PLit` and the right-hand side is an array of `Literal`s, the type-correct
form is on the denotation `l.lit` (definitionally `PLit.decode l`). -/
def ClauseDB.PrunesOK (db : ClauseDB p T) (ps : Array (PLit × Nat)) : Prop :=
  ∀ l id, (l, id) ∈ ps →
    ∃ sc, db.clauses[id]? = some sc ∧ sc.deleted = false ∧
      l.lit ∈ sc.e.lits.map PLit.decode

/-- A conflict result names a live stored clause whose `e` is returned. -/
def ClauseDB.ConflictOK (db : ClauseDB p T) (c : EClause p T) (id : Nat) : Prop :=
  ∃ sc, db.clauses[id]? = some sc ∧ sc.deleted = false ∧ sc.e = c

/-- `unitsScan` never changes the database. -/
private theorem unitsScan_fst (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (db : ClauseDB p T) (fuel i : Nat)
    (prunes : Array (PLit × Nat)) :
    (unitsScan p T doms db fuel i prunes).1 = db := by
  induction fuel generalizing i prunes with
  | zero => rfl
  | succ fuel ih =>
      unfold unitsScan
      split
      · split
        · rename_i sc hget
          split
          · exact ih (i + 1) prunes
          · split
            · split
              · exact ih (i + 1) prunes
              · rfl
              · exact ih (i + 1) (prunes.push (_, i))
            · exact ih (i + 1) prunes
        · exact ih (i + 1) prunes
      · rfl

/-- Every conflict reported by `unitsScan` is a live stored clause. -/
private theorem unitsScan_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (db : ClauseDB p T) (fuel i : Nat)
    (prunes : Array (PLit × Nat)) {c : EClause p T} {id : Nat}
    (h : (unitsScan p T doms db fuel i prunes).2 = .conflict c id) :
    db.ConflictOK c id := by
  induction fuel generalizing i prunes with
  | zero => simp [unitsScan] at h
  | succ fuel ih =>
      unfold unitsScan at h
      split at h
      · split at h
        · rename_i sc hget
          split at h
          · exact ih (i + 1) prunes h
          · rename_i hcond
            split at h
            · rename_i l hl
              split at h
              · exact ih (i + 1) prunes h
              · rename_i hval
                have hcond' : ¬ ((sc.deleted || sc.e.lits.size != 1) = true) := by
                  simpa using hcond
                have hdel : sc.deleted = false := by
                  cases hd : sc.deleted with
                  | false => rfl
                  | true => exact (hcond' (by simp [hd])).elim
                simp only [WPropOut.conflict.injEq] at h
                obtain ⟨he, hi⟩ := h
                subst hi
                exact ⟨sc, hget, hdel, he⟩
              · exact ih (i + 1) (prunes.push (l, i)) h
            · exact ih (i + 1) prunes h
        · exact ih (i + 1) prunes h
      · simp [unitsScan] at h

/-- Every pruning reported by `unitsScan` is a literal occurrence of a live
stored clause, provided the incoming accumulator was already sound. -/
private theorem unitsScan_prunes (p : CompiledProblem DomConstraint) (T : LitTable)
    (doms : Array DomC) (db : ClauseDB p T) (fuel i : Nat)
    (prunes : Array (PLit × Nat)) {ps : Array (PLit × Nat)}
    (hpre : db.PrunesOK prunes)
    (h : (unitsScan p T doms db fuel i prunes).2 = .prune ps) :
    db.PrunesOK ps := by
  induction fuel generalizing i prunes with
  | zero =>
      have h' : unitsScan p T doms db 0 i prunes = (db, .prune prunes) := rfl
      rw [h'] at h
      simp only [WPropOut.prune.injEq] at h
      have hps : prunes = ps := h
      rw [← hps]
      exact hpre
  | succ fuel ih =>
      unfold unitsScan at h
      split at h
      · split at h
        · rename_i sc hget
          split at h
          · exact ih (i + 1) prunes hpre h
          · rename_i hcond
            split at h
            · rename_i l hl
              split at h
              · exact ih (i + 1) prunes hpre h
              · simp at h
              · have hcond' : ¬ ((sc.deleted || sc.e.lits.size != 1) = true) := by
                  simpa using hcond
                have hdel : sc.deleted = false := by
                  cases hd : sc.deleted with
                  | false => rfl
                  | true => exact (hcond' (by simp [hd])).elim
                have hpre' : db.PrunesOK (prunes.push (l, i)) := by
                  intro l' id' hmem
                  rw [Array.mem_push] at hmem
                  rcases hmem with hmem | ⟨rfl, rfl⟩
                  · exact hpre l' id' hmem
                  · refine ⟨sc, hget, hdel, ?_⟩
                    rw [Array.mem_map]
                    exact ⟨l, by rw [Array.mem_iff_getElem?]; exact ⟨0, hl⟩, rfl⟩
                exact ih (i + 1) _ hpre' h
            · exact ih (i + 1) prunes hpre h
        · exact ih (i + 1) prunes hpre h
      · have hps : prunes = ps := by simpa using h
        rw [← hps]
        exact hpre

/-- `ofPrunes` only hides the empty list. -/
theorem WPropOut.ofPrunes_prune {ps ps' : Array (PLit × Nat)}
    (h : WPropOut.ofPrunes (p := p) (T := T) ps = .prune ps') : ps' = ps := by
  unfold WPropOut.ofPrunes at h
  split at h
  · simp at h
  · simp only [WPropOut.prune.injEq] at h
    exact h.symm

/-- Shaping cannot turn a non-conflict into a conflict. -/
private theorem WPropOut.shape_conflict {o : WPropOut p T} {c : EClause p T} {id : Nat}
    (h : o.shape = .conflict c id) : o = .conflict c id := by
  unfold WPropOut.shape at h
  split at h
  · unfold WPropOut.ofPrunes at h
    split at h <;> simp at h
  · assumption

/-- Shaping only hides empty pruning lists. -/
private theorem WPropOut.shape_prune {o : WPropOut p T} {ps : Array (PLit × Nat)}
    (h : o.shape = .prune ps) : ∃ ps0, o = .prune ps0 ∧ ps = ps0 := by
  unfold WPropOut.shape at h
  split at h
  · unfold WPropOut.ofPrunes at h
    split at h
    · simp at h
    · simp only [WPropOut.prune.injEq] at h
      exact ⟨_, rfl, h.symm⟩
  · exact ⟨ps, h, rfl⟩

/-- `propagateUnits` never changes the database. -/
theorem ClauseDB.propagateUnits_fst (db : ClauseDB p T) (doms : Array DomC) :
    (db.propagateUnits p T doms).1 = db := by
  unfold ClauseDB.propagateUnits
  exact unitsScan_fst _ _ _ _ _ _ _

/-- `propagateUnits` preserves the clause-database invariant. -/
theorem ClauseDB.propagateUnits_inv (db : ClauseDB p T) (doms : Array DomC)
    (h : db.Inv) : (db.propagateUnits p T doms).1.Inv := by
  rw [ClauseDB.propagateUnits_fst]
  exact h

/-- A conflict from `propagateUnits` names a live stored clause. -/
theorem ClauseDB.propagateUnits_conflict (db : ClauseDB p T) (doms : Array DomC)
    {c : EClause p T} {id : Nat}
    (h : (db.propagateUnits p T doms).2 = .conflict c id) :
    db.ConflictOK c id := by
  unfold ClauseDB.propagateUnits at h
  dsimp only at h
  have h' : (unitsScan p T doms db db.clauses.size 0 #[]).2 = .conflict c id :=
    WPropOut.shape_conflict h
  exact unitsScan_conflict _ _ _ _ _ _ _ h'

/-- Every pruning from `propagateUnits` is a literal occurrence of a live
stored clause. -/
theorem ClauseDB.propagateUnits_prunes (db : ClauseDB p T) (doms : Array DomC)
    {ps : Array (PLit × Nat)}
    (h : (db.propagateUnits p T doms).2 = .prune ps) : db.PrunesOK ps := by
  unfold ClauseDB.propagateUnits at h
  dsimp only at h
  obtain ⟨ps0, hout, hps⟩ := WPropOut.shape_prune h
  have h' : (unitsScan p T doms db db.clauses.size 0 #[]).2 = .prune ps0 := hout
  have hres := unitsScan_prunes _ _ _ _ _ _ _
    (by intro l id hm; simp at hm) h'
  rw [hps]
  exact hres

/-! ## Empty-clause lookup -/

/-- A returned empty conflict is a live stored clause with no literals. -/
theorem ClauseDB.emptyConflict?_spec (db : ClauseDB p T) {c : EClause p T}
    (h : db.emptyConflict? = some c) :
    ∃ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc ∧
      sc.deleted = false ∧ sc.e.lits.size = 0 ∧ sc.e = c := by
  unfold ClauseDB.emptyConflict? at h
  rcases Array.findSome?_eq_some_iff.mp h with ⟨ys, a, zs, hsplit, hfa, -⟩
  have hfa' := hfa
  split at hfa'
  · simp at hfa'
  · rename_i hcond
    have hc : ¬ ((a.deleted || a.e.lits.size != 0) = true) := by
      simpa using hcond
    have hdel : a.deleted = false := by
      cases hd : a.deleted with
      | false => rfl
      | true => exact (hc (by simp [hd])).elim
    have hsz : a.e.lits.size = 0 := by
      cases hs : a.e.lits.size with
      | zero => rfl
      | succ n => exact (hc (by simp [hdel, hs])).elim
    have he : a.e = c := by simpa using hfa'
    refine ⟨ys.size, a, ?_, hdel, hsz, he⟩
    rw [hsplit, Array.getElem?_append]
    have hlt : ys.size < (ys.push a).size := by simp
    rw [if_pos hlt, Array.getElem?_push, if_pos rfl]

/-- The empty database has no empty conflict. -/
theorem ClauseDB.emptyConflict?_empty :
    (ClauseDB.empty (p := p) (T := T)).emptyConflict? = none := rfl

/-! ## Two-watched-literal propagation: preservation and provenance -/

/-- The part of a stored clause relevant to provenance: its carried clause
and its deletion flag.  Watch positions may change during propagation. -/
private def clauseMeta (db : ClauseDB p T) (id : Nat) : Option (EClause p T × Bool) :=
  (db.clauses[id]?).map (fun sc => (sc.e, sc.deleted))

/-- Rows other than `except` only grow. -/
private def RowsLe (db db' : ClauseDB p T) (except : Nat) : Prop :=
  ∀ (j : Nat), j ≠ except → ∀ x, x ∈ db.watchList j → x ∈ db'.watchList j

private theorem RowsLe.refl (db : ClauseDB p T) (except : Nat) : RowsLe db db except :=
  fun _ _ _ hx => hx

private theorem RowsLe.trans {db1 db2 db3 : ClauseDB p T} {except : Nat}
    (h1 : RowsLe db1 db2 except) (h2 : RowsLe db2 db3 except) :
    RowsLe db1 db3 except :=
  fun j hj x hx => h2 j hj x (h1 j hj x hx)

/-- Reading a watch row after writing row `j`. -/
private theorem watchList_set_other (db : ClauseDB p T) (j i : Nat) (v : Array Nat)
    (h : i ≠ j) :
    ({ db with watch := db.watch.set! j v }).watchList i = db.watchList i := by
  unfold ClauseDB.watchList
  dsimp only
  exact array_getD_set!_ne (xs := db.watch) (i := j) (j := i) (v := v) (d := #[])
    (h := fun hji => h hji.symm)

/-- Reading the written watch row. -/
private theorem watchList_set_self (db : ClauseDB p T) (j : Nat) (v : Array Nat)
    (h : j < db.watch.size) :
    ({ db with watch := db.watch.set! j v }).watchList j = v := by
  unfold ClauseDB.watchList
  dsimp only
  exact array_getD_set!_self (xs := db.watch) (i := j) (v := v) (d := #[]) h

/-- Rewriting one row away from `except` keeps all other rows monotone. -/
private theorem RowsLe.of_watch_set (db : ClauseDB p T) (j : Nat) (v : Array Nat)
    (except : Nat) (hej : except = j) :
    RowsLe db { db with watch := db.watch.set! j v } except := by
  intro i hi x hx
  have hij : i ≠ j := by
    rw [← hej]
    exact hi
  rw [watchList_set_other db j i v hij]
  exact hx

/-- `ensureWatch` keeps every existing row. -/
private theorem RowsLe.of_ensureWatch (db : ClauseDB p T) (n except : Nat) :
    RowsLe db (db.ensureWatch n) except := by
  intro i _ x hx
  rw [ClauseDB.ensureWatch_watchList]
  exact hx

/-- A member of an extract is a member of the source array. -/
private theorem mem_extract_subset {α : Type} {xs : Array α} {i j : Nat} {x : α}
    (h : x ∈ xs.extract i j) : x ∈ xs := by
  rw [Array.mem_extract_iff_getElem] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact Array.getElem_mem (by omega)

/-- Splitting the unvisited suffix at the next entry to visit. -/
private theorem mem_extract_succ {α : Type} [Inhabited α] {xs : Array α} {i : Nat}
    (hi : i < xs.size) {x : α} :
    x ∈ xs.extract i xs.size ↔ x = xs[i]! ∨ x ∈ xs.extract (i + 1) xs.size := by
  rw [Array.mem_extract_iff_getElem]
  constructor
  · rintro ⟨k, hk, hxk⟩
    rcases k with _ | k
    · left
      rw [getElem!_pos xs i hi]
      simpa using hxk.symm
    · right
      rw [Array.mem_extract_iff_getElem]
      refine ⟨k, by omega, ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using hxk
  · rintro (rfl | hx)
    · refine ⟨0, by omega, ?_⟩
      simp only [Nat.add_zero]
      exact (getElem!_pos xs i hi).symm
    · rw [Array.mem_extract_iff_getElem] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      refine ⟨k + 1, by omega, ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using hxk

/-- A clause position is backed by the already-visited survivors `kept` or by
the unvisited suffix of the entry row for `l.idx`, or by the current row for
any other index. -/
private def ScanPosOK (db : ClauseDB p T) (l : PLit) (olds : Array Nat) (i : Nat)
    (kept : Array Nat) (id : Nat) (sc : StoredClause p T) (pos : Nat) : Prop :=
  ∀ q, sc.e.lits[pos]? = some q →
    (q.idx = l.idx ∧ (id ∈ kept ∨ id ∈ olds.extract i olds.size)) ∨
      (q.idx ≠ l.idx ∧ id ∈ db.watchList q.idx)

/-- Every live clause of size at least two has both watched positions backed
by the visited survivors, the unvisited suffix of the `l.idx` row, or by the
current rows for the other indices. -/
private def ScanBacked (db : ClauseDB p T) (l : PLit) (olds : Array Nat) (i : Nat)
    (kept : Array Nat) : Prop :=
  ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size →
      ScanPosOK db l olds i kept id sc sc.w1 ∧
        ScanPosOK db l olds i kept id sc sc.w2

private theorem ScanPosOK.mono {db db' : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept kept' : Array Nat} {id : Nat}
    {sc : StoredClause p T} {pos : Nat}
    (hrows : RowsLe db db' l.idx) (hkept : ∀ x ∈ kept, x ∈ kept')
    (h : ScanPosOK db l olds i kept id sc pos) :
    ScanPosOK db' l olds i kept' id sc pos := by
  intro q hq
  rcases h q hq with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
  · refine Or.inl ⟨hidx, ?_⟩
    rcases hmem with hk | hs
    · exact Or.inl (hkept id hk)
    · exact Or.inr hs
  · exact Or.inr ⟨hne, hrows q.idx hne id hmem⟩

private theorem ScanBacked.mono {db db' : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept kept' : Array Nat}
    (hcl : ∀ (id : Nat), db'.clauses[id]? = db.clauses[id]?)
    (hrows : RowsLe db db' l.idx) (hkept : ∀ x ∈ kept, x ∈ kept')
    (h : ScanBacked db l olds i kept) : ScanBacked db' l olds i kept' := by
  intro id sc hget hdel hsz
  have hget' : db.clauses[id]? = some sc := by
    rw [← hcl]
    exact hget
  obtain ⟨h1, h2⟩ := h id sc hget' hdel hsz
  exact ⟨ScanPosOK.mono hrows hkept h1, ScanPosOK.mono hrows hkept h2⟩

/-- Advance the scan frontier when the entry at `i` survives (it is pushed into
`kept`): the suffix loses `olds[i]!`, which is now in `kept'`. -/
private theorem ScanPosOK.step {db db' : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept kept' : Array Nat} {id : Nat}
    {sc : StoredClause p T} {pos : Nat}
    (hi : i < olds.size) (hrows : RowsLe db db' l.idx)
    (hkept : ∀ x ∈ kept, x ∈ kept') (hnew : olds[i]! ∈ kept')
    (h : ScanPosOK db l olds i kept id sc pos) :
    ScanPosOK db' l olds (i + 1) kept' id sc pos := by
  intro q hq
  rcases h q hq with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
  · refine Or.inl ⟨hidx, ?_⟩
    rcases hmem with hk | hs
    · exact Or.inl (hkept id hk)
    · rw [mem_extract_succ hi] at hs
      rcases hs with heq | hs
      · exact Or.inl (heq ▸ hnew)
      · exact Or.inr hs
  · exact Or.inr ⟨hne, hrows q.idx hne id hmem⟩

/-- Advance the frontier for a clause whose id is not the current entry: its
backing cannot depend on the dropped entry `olds[i]!`. -/
private theorem ScanPosOK.step_ne {db db' : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept kept' : Array Nat} {id : Nat}
    {sc : StoredClause p T} {pos : Nat}
    (hi : i < olds.size) (hrows : RowsLe db db' l.idx)
    (hkept : ∀ x ∈ kept, x ∈ kept') (hne : id ≠ olds[i]!)
    (h : ScanPosOK db l olds i kept id sc pos) :
    ScanPosOK db' l olds (i + 1) kept' id sc pos := by
  intro q hq
  rcases h q hq with ⟨hidx, hmem⟩ | ⟨hne', hmem⟩
  · refine Or.inl ⟨hidx, ?_⟩
    rcases hmem with hk | hs
    · exact Or.inl (hkept id hk)
    · rw [mem_extract_succ hi] at hs
      rcases hs with heq | hs
      · exact (hne heq).elim
      · exact Or.inr hs
  · exact Or.inr ⟨hne', hrows q.idx hne' id hmem⟩

/-- Dropping the entry at `i` preserves backing when its clause is deleted or
no longer watches `l.idx`. -/
private theorem ScanPosOK.skip {db : ClauseDB p T} {l : PLit} {olds : Array Nat}
    {i : Nat} {kept : Array Nat} {id : Nat} {sc : StoredClause p T} {pos : Nat}
    (hi : i < olds.size)
    (hslot : ∀ sc, db.clauses[olds[i]!]? = some sc →
      sc.deleted = true ∨ ¬ ClauseWatches sc l ∨ sc.e.lits.size < 2)
    (hget : db.clauses[id]? = some sc) (hdel : sc.deleted = false)
    (hsz : 2 ≤ sc.e.lits.size)
    (hpos : pos = sc.w1 ∨ pos = sc.w2)
    (h : ScanPosOK db l olds i kept id sc pos) :
    ScanPosOK db l olds (i + 1) kept id sc pos := by
  intro q hq
  rcases h q hq with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
  · refine Or.inl ⟨hidx, ?_⟩
    rcases hmem with hk | hs
    · exact Or.inl hk
    · rw [mem_extract_succ hi] at hs
      rcases hs with heq | hs
      · have hget' : db.clauses[olds[i]!]? = some sc := heq ▸ hget
        have hcw : ClauseWatches sc l := by
          rcases hpos with rfl | rfl
          · exact Or.inl (by
              unfold ClauseWatches₁
              rw [hq]
              exact hidx)
          · exact Or.inr (by
              unfold ClauseWatches₂
              rw [hq]
              exact hidx)
        rcases hslot sc hget' with hdel' | hnw | hsmall
        · rw [hdel'] at hdel
          simp at hdel
        · exact (hnw hcw).elim
        · omega
      · exact Or.inr hs
  · exact Or.inr ⟨hne, hmem⟩

private theorem ScanBacked.step {db : ClauseDB p T} {l : PLit} {olds : Array Nat}
    {i : Nat} {kept kept' : Array Nat}
    (hi : i < olds.size) (hkept : ∀ x ∈ kept, x ∈ kept')
    (hnew : olds[i]! ∈ kept') (h : ScanBacked db l olds i kept) :
    ScanBacked db l olds (i + 1) kept' := by
  intro id sc hget hdel hsz
  obtain ⟨h1, h2⟩ := h id sc hget hdel hsz
  exact ⟨ScanPosOK.step hi (RowsLe.refl db l.idx) hkept hnew h1,
    ScanPosOK.step hi (RowsLe.refl db l.idx) hkept hnew h2⟩

private theorem ScanBacked.skip {db : ClauseDB p T} {l : PLit} {olds : Array Nat}
    {i : Nat} {kept : Array Nat}
    (hi : i < olds.size)
    (hslot : ∀ sc, db.clauses[olds[i]!]? = some sc →
      sc.deleted = true ∨ ¬ ClauseWatches sc l ∨ sc.e.lits.size < 2)
    (h : ScanBacked db l olds i kept) : ScanBacked db l olds (i + 1) kept := by
  intro id sc hget hdel hsz
  obtain ⟨h1, h2⟩ := h id sc hget hdel hsz
  exact ⟨ScanPosOK.skip hi hslot hget hdel hsz (Or.inl rfl) h1,
    ScanPosOK.skip hi hslot hget hdel hsz (Or.inr rfl) h2⟩

/-- Once the final row `l.idx` equals `kept` and the unvisited suffix is
empty (or already contained in `kept`), backing becomes the ordinary
two-watch membership invariant. -/
private theorem ScanBacked.watchedBy {db : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept : Array Nat}
    (h : ScanBacked db l olds i kept) (hrow : db.watchList l.idx = kept)
    (hsuf : ∀ x ∈ olds.extract i olds.size, x ∈ kept) :
    ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
      sc.deleted = false → 2 ≤ sc.e.lits.size → db.WatchedBy id sc := by
  intro id sc hget hdel hsz
  obtain ⟨h1, h2⟩ := h id sc hget hdel hsz
  constructor
  · intro q hq
    rcases h1 q hq with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
    · unfold ClauseDB.WatchesAt
      rw [hidx, hrow]
      rcases hmem with hk | hs
      · exact hk
      · exact hsuf id hs
    · exact hmem
  · intro q hq
    rcases h2 q hq with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
    · unfold ClauseDB.WatchesAt
      rw [hidx, hrow]
      rcases hmem with hk | hs
      · exact hk
      · exact hsuf id hs
    · exact hmem

/-- The scan state invariant.  `db0`/`olds` are the entry database and the
entry content of row `l.idx`; `i` is the scan frontier and `kept` the future
content of that row.  Clauses still watching `l.idx` are backed either by the
already-visited survivors in `kept` or by the unvisited suffix
`olds.extract i olds.size`. -/
private structure ScanInv (db0 : ClauseDB p T) (l : PLit) (olds : Array Nat)
    (i : Nat) (kept : Array Nat) (db : ClauseDB p T)
    (prunes : Array (PLit × Nat)) : Prop where
  watch_lt : ∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
    ∀ id ∈ ids, id < db.clauses.size
  pos_lt : ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    sc.deleted = false → 2 ≤ sc.e.lits.size →
      sc.w1 < sc.e.lits.size ∧ sc.w2 < sc.e.lits.size
  backed : ScanBacked db l olds i kept
  live_eq : db.live = db.liveCount
  free_deleted : ∀ id, id ∈ db.free →
    ∃ sc, db.clauses[id]? = some sc ∧ sc.deleted = true
  free_nodup : db.free.toList.Nodup
  kept_lt : ∀ id ∈ kept, id < db.clauses.size
  lidx_lt : l.idx < db.watch.size
  size_eq : db.clauses.size = db0.clauses.size
  live_eq0 : db.live = db0.live
  free_eq0 : db.free = db0.free
  meta_eq : ∀ (id : Nat), clauseMeta db id = clauseMeta db0 id
  prunes_ok : db0.PrunesOK prunes

/-- The initial scan state: no entry has been visited yet, so the whole entry
row is still the unvisited suffix. -/
private theorem ScanInv.base {db : ClauseDB p T} {l : PLit} {olds : Array Nat}
    {prunes : Array (PLit × Nat)}
    (h : db.Inv) (hrow : db.watchList l.idx = olds)
    (_holds : ∀ id ∈ olds, id < db.clauses.size)
    (hlidx : l.idx < db.watch.size)
    (hpr : db.PrunesOK prunes) : ScanInv db l olds 0 #[] db prunes := by
  refine ⟨h.watch_lt, h.pos_lt, ?_, h.live_eq, h.free_deleted, h.free_nodup,
    ?_, hlidx, rfl, rfl, rfl, ?_, hpr⟩
  · have hzero : olds.extract 0 olds.size = olds :=
      Array.extract_eq_self_of_le (Nat.le_refl _)
    intro id sc hget hdel hsz
    obtain ⟨h1, h2⟩ := h.watches id sc hget hdel hsz
    constructor
    · intro q hq
      have hm := h1 q hq
      by_cases hqidx : q.idx = l.idx
      · refine Or.inl ⟨hqidx, Or.inr ?_⟩
        rw [hzero]
        have hm' : db.WatchesAt l.idx id := by
          rw [hqidx] at hm
          exact hm
        simpa [ClauseDB.WatchesAt, hrow] using hm'
      · exact Or.inr ⟨hqidx, hm⟩
    · intro q hq
      have hm := h2 q hq
      by_cases hqidx : q.idx = l.idx
      · refine Or.inl ⟨hqidx, Or.inr ?_⟩
        rw [hzero]
        have hm' : db.WatchesAt l.idx id := by
          rw [hqidx] at hm
          exact hm
        simpa [ClauseDB.WatchesAt, hrow] using hm'
      · exact Or.inr ⟨hqidx, hm⟩
  · intro id hid
    simp at hid
  · intro id
    rfl

/-- Advancing the frontier after pushing the current entry into `kept`
preserves the scan invariant. -/
private theorem ScanInv.withKept {db0 : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept : Array Nat} {db : ClauseDB p T}
    {prunes : Array (PLit × Nat)}
    (hinv : ScanInv db0 l olds i kept db prunes) (kept' : Array Nat)
    (hi : i < olds.size) (hsub : ∀ x ∈ kept, x ∈ kept')
    (hnew : olds[i]! ∈ kept')
    (hlt : ∀ x ∈ kept', x < db.clauses.size) :
    ScanInv db0 l olds (i + 1) kept' db prunes :=
  { watch_lt := hinv.watch_lt
    pos_lt := hinv.pos_lt
    backed := ScanBacked.step hi hsub hnew hinv.backed
    live_eq := hinv.live_eq
    free_deleted := hinv.free_deleted
    free_nodup := hinv.free_nodup
    kept_lt := hlt
    lidx_lt := hinv.lidx_lt
    size_eq := hinv.size_eq
    live_eq0 := hinv.live_eq0
    free_eq0 := hinv.free_eq0
    meta_eq := hinv.meta_eq
    prunes_ok := hinv.prunes_ok }

/-- Advancing the frontier when the current entry is dropped (deleted slot or
stale watch) preserves the scan invariant. -/
private theorem ScanInv.skip {db0 : ClauseDB p T} {l : PLit} {olds : Array Nat}
    {i : Nat} {kept : Array Nat} {db : ClauseDB p T}
    {prunes : Array (PLit × Nat)}
    (hinv : ScanInv db0 l olds i kept db prunes)
    (hi : i < olds.size)
    (hslot : ∀ sc, db.clauses[olds[i]!]? = some sc →
      sc.deleted = true ∨ ¬ ClauseWatches sc l ∨ sc.e.lits.size < 2) :
    ScanInv db0 l olds (i + 1) kept db prunes :=
  { watch_lt := hinv.watch_lt
    pos_lt := hinv.pos_lt
    backed := ScanBacked.skip hi hslot hinv.backed
    live_eq := hinv.live_eq
    free_deleted := hinv.free_deleted
    free_nodup := hinv.free_nodup
    kept_lt := hinv.kept_lt
    lidx_lt := hinv.lidx_lt
    size_eq := hinv.size_eq
    live_eq0 := hinv.live_eq0
    free_eq0 := hinv.free_eq0
    meta_eq := hinv.meta_eq
    prunes_ok := hinv.prunes_ok }

/-- Extracting the watched literal from `ClauseWatches₁`. -/
private theorem ClauseWatches₁.some {sc : StoredClause p T} {l : PLit}
    (h : ClauseWatches₁ sc l) :
    ∃ q, sc.e.lits[sc.w1]? = some q ∧ q.idx = l.idx := by
  unfold ClauseWatches₁ at h
  split at h
  · rename_i q hq
    exact ⟨q, hq, h⟩
  · exact h.elim

/-- Extracting the watched literal from `ClauseWatches₂`. -/
private theorem ClauseWatches₂.some {sc : StoredClause p T} {l : PLit}
    (h : ClauseWatches₂ sc l) :
    ∃ q, sc.e.lits[sc.w2]? = some q ∧ q.idx = l.idx := by
  unfold ClauseWatches₂ at h
  split at h
  · rename_i q hq
    exact ⟨q, hq, h⟩
  · exact h.elim

/-- When the first watched literal is the propagated one, the other watched
position is the second one. -/
private theorem otherWatchedPos_eq_w2 {sc : StoredClause p T} {l : PLit}
    (h : ClauseWatches₁ sc l) : otherWatchedPos sc l = sc.w2 := by
  obtain ⟨q, hq, hqidx⟩ := ClauseWatches₁.some h
  unfold otherWatchedPos
  rw [hq]
  simp [hqidx]

/-- When the first watched literal is not the propagated one and is present,
the other watched position is the first one. -/
private theorem otherWatchedPos_eq_w1 {sc : StoredClause p T} {l : PLit}
    (h : ¬ ClauseWatches₁ sc l) (hq : sc.e.lits[sc.w1]? ≠ none) :
    otherWatchedPos sc l = sc.w1 := by
  unfold otherWatchedPos
  split
  · rename_i q hq'
    split
    · rename_i hqidx
      exact (h (by
        unfold ClauseWatches₁
        rw [hq']
        exact hqidx)).elim
    · rfl
  · rename_i hnone
    exact (hq hnone).elim

/-- `ensureWatch` preserves the watch-index bound. -/
private theorem watch_lt_ensureWatch {db : ClauseDB p T}
    (h : ∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
      ∀ id ∈ ids, id < db.clauses.size) (n : Nat) :
    ∀ (i : Nat) (ids : Array Nat), (db.ensureWatch n).watch[i]? = some ids →
      ∀ id ∈ ids, id < (db.ensureWatch n).clauses.size := by
  intro i ids hi id hid
  have hcl : (db.ensureWatch n).clauses = db.clauses := by
    unfold ClauseDB.ensureWatch
    split <;> rfl
  rw [hcl]
  unfold ClauseDB.ensureWatch at hi
  split at hi
  · rw [Array.getElem?_append] at hi
    by_cases hin : i < db.watch.size
    · rw [if_pos hin] at hi
      exact h i ids hi id hid
    · rw [if_neg hin] at hi
      rw [Array.getElem?_replicate] at hi
      split at hi
      · simp at hi
        subst hi
        simp at hid
      · simp at hi
  · exact h i ids hi id hid

/-- Recovering the entry clause behind a `clauseMeta` equality. -/
private theorem clauseMeta.back {db db0 : ClauseDB p T} {id : Nat}
    {sc : StoredClause p T}
    (hmeta : ∀ (id : Nat), clauseMeta db id = clauseMeta db0 id)
    (hget : db.clauses[id]? = some sc) :
    ∃ sc0, db0.clauses[id]? = some sc0 ∧ sc0.e = sc.e ∧ sc0.deleted = sc.deleted := by
  have hm := hmeta id
  unfold clauseMeta at hm
  rw [hget] at hm
  cases h0 : db0.clauses[id]? with
  | none => simp [h0] at hm
  | some sc0 =>
      simp only [h0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
      exact ⟨sc0, rfl, hm.1.symm, hm.2.symm⟩

/-- A `ConflictOK` result transported back along `clauseMeta`. -/
private theorem clauseMeta.conflictOK {db db0 : ClauseDB p T} {id : Nat}
    {sc : StoredClause p T}
    (hmeta : ∀ (id : Nat), clauseMeta db id = clauseMeta db0 id)
    (hget : db.clauses[id]? = some sc) (hdel : sc.deleted = false) :
    db0.ConflictOK sc.e id := by
  obtain ⟨sc0, h0, he, hd⟩ := clauseMeta.back hmeta hget
  exact ⟨sc0, h0, by rw [hd, hdel], he⟩

/-- Postcondition of one scan. -/
private structure ScanPost (db0 : ClauseDB p T) (db' : ClauseDB p T)
    (out : WPropOut p T) : Prop where
  inv : db'.Inv
  conflict : ∀ (c : EClause p T) (id : Nat), out = .conflict c id → db0.ConflictOK c id
  prune : ∀ ps, out = .prune ps → db0.PrunesOK ps
  meta_eq : ∀ (id : Nat), clauseMeta db' id = clauseMeta db0 id
  size_eq : db'.clauses.size = db0.clauses.size
  live_eq : db'.live = db0.live
  free_eq : db'.free = db0.free

/-- Terminal pruning branch: the row becomes `kept`. -/
private theorem ScanInv.final_prune {db0 : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept : Array Nat} {db : ClauseDB p T}
    {prunes : Array (PLit × Nat)}
    (hinv : ScanInv db0 l olds i kept db prunes) (hi : olds.size ≤ i) :
    ScanPost db0 { db with watch := db.watch.set! l.idx kept } (.prune prunes) := by
  have hrow : ({ db with watch := db.watch.set! l.idx kept }).watchList l.idx = kept :=
    watchList_set_self db l.idx kept hinv.lidx_lt
  have hempty : olds.extract i olds.size = #[] :=
    Array.extract_eq_empty_of_le (by simpa using hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i ids hi id hid
      by_cases hil : i = l.idx
      · subst i
        have hids : ids = kept := by
          have hs := array_getElem?_set!_self (xs := db.watch) (i := l.idx)
            (v := kept) (h := hinv.lidx_lt)
          rw [hs] at hi
          exact (Option.some.inj hi).symm
        subst ids
        exact hinv.kept_lt id hid
      · rw [array_getElem?_set!_ne (xs := db.watch) (i := l.idx) (j := i)
          (v := kept) (h := fun hli => hil hli.symm)] at hi
        exact hinv.watch_lt i ids hi id hid
    · exact hinv.pos_lt
    · intro id sc hget hdel hsz
      have hbacked' : ScanBacked ({ db with watch := db.watch.set! l.idx kept })
          l olds i kept :=
        ScanBacked.mono (db := db) (db' := { db with watch := db.watch.set! l.idx kept })
          (fun _ => rfl) (RowsLe.of_watch_set db l.idx kept l.idx rfl)
          (fun x hx => hx) hinv.backed
      exact ScanBacked.watchedBy hbacked' hrow
        (fun x hx => by rw [hempty] at hx; simp at hx) id sc hget hdel hsz
    · exact hinv.live_eq
    · intro id hid
      exact hinv.free_deleted id hid
    · exact hinv.free_nodup
  · intro c id h
    simp at h
  · intro ps h
    simp only [WPropOut.prune.injEq] at h
    subst h
    exact hinv.prunes_ok
  · intro id
    exact hinv.meta_eq id
  · exact hinv.size_eq
  · exact hinv.live_eq0
  · exact hinv.free_eq0

/-- Conflict branch: the row becomes `(kept.push id) ++ olds.extract (i+1)`. -/
private theorem ScanInv.conflict_post {db0 : ClauseDB p T} {l : PLit}
    {olds : Array Nat} {i : Nat} {kept : Array Nat} {db : ClauseDB p T}
    {prunes : Array (PLit × Nat)}
    (hinv : ScanInv db0 l olds i kept db prunes)
    (holds : ∀ x ∈ olds, x < db0.clauses.size)
    (hi : i < olds.size) {sc : StoredClause p T}
    (hget : db.clauses[olds[i]!]? = some sc) (hdel : sc.deleted = false)
    (hid_lt : olds[i]! < db.clauses.size) :
    ScanPost db0
      { db with watch :=
          db.watch.set! l.idx ((kept.push olds[i]!) ++ olds.extract (i + 1) olds.size) }
      (.conflict sc.e olds[i]!) := by
  let nw := (kept.push olds[i]!) ++ olds.extract (i + 1) olds.size
  have hrow : ({ db with watch := db.watch.set! l.idx nw }).watchList l.idx = nw :=
    watchList_set_self db l.idx _ hinv.lidx_lt
  have hsub : ∀ x ∈ kept, x ∈ nw := by
    intro x hx
    exact Array.mem_append.mpr (Or.inl (Array.mem_push.mpr (Or.inl hx)))
  have hkeep : olds[i]! ∈ nw :=
    Array.mem_append.mpr (Or.inl (Array.mem_push.mpr (Or.inr rfl)))
  have hrows : RowsLe db { db with watch := db.watch.set! l.idx nw } l.idx :=
    RowsLe.of_watch_set db l.idx _ l.idx rfl
  have hbacked0 : ScanBacked db l olds (i + 1) nw :=
    ScanBacked.step hi hsub hkeep hinv.backed
  have hbacked : ScanBacked { db with watch := db.watch.set! l.idx nw }
      l olds (i + 1) nw :=
    ScanBacked.mono (db := db)
      (db' := { db with watch := db.watch.set! l.idx nw })
      (fun _ => rfl) hrows (fun x hx => hx) hbacked0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' ids hi' x hx
      by_cases hil : i' = l.idx
      · subst i'
        have hids : ids = nw := by
          have hs := array_getElem?_set!_self (xs := db.watch) (i := l.idx)
            (v := nw) (h := hinv.lidx_lt)
          rw [hs] at hi'
          exact (Option.some.inj hi').symm
        subst ids
        rw [Array.mem_append] at hx
        rcases hx with hx | hx
        · rw [Array.mem_push] at hx
          rcases hx with hx | rfl
          · exact hinv.kept_lt x hx
          · exact hid_lt
        · exact hinv.size_eq.symm ▸ holds x (mem_extract_subset hx)
      · rw [array_getElem?_set!_ne (xs := db.watch) (i := l.idx) (j := i')
          (v := nw) (h := fun hli => hil hli.symm)] at hi'
        exact hinv.watch_lt i' ids hi' x hx
    · exact hinv.pos_lt
    · intro id' sc' hget' hdel' hsz'
      exact ScanBacked.watchedBy hbacked hrow
        (fun x hx => Array.mem_append.mpr (Or.inr hx)) id' sc' hget' hdel' hsz'
    · exact hinv.live_eq
    · intro id' hid'
      exact hinv.free_deleted id' hid'
    · exact hinv.free_nodup
  · intro c id' h
    simp only [WPropOut.conflict.injEq] at h
    obtain ⟨he, hi'⟩ := h
    subst hi'
    have hc := clauseMeta.conflictOK hinv.meta_eq hget hdel
    rwa [he] at hc
  · intro ps h
    simp at h
  · intro id'
    exact hinv.meta_eq id'
  · exact hinv.size_eq
  · exact hinv.live_eq0
  · exact hinv.free_eq0

/-- Appending an id to one watch row keeps every row monotone. -/
private theorem RowsLe.of_watch_push (db : ClauseDB p T) (j id' except : Nat) :
    RowsLe db { db with watch := db.watch.set! j ((db.watch.getD j #[]).push id') }
      except := by
  intro i _ x hx
  exact ClauseDB.watchesAt_push db j id' i x hx

/-- `ensureWatch` never shrinks the watch array. -/
private theorem ensureWatch_watch_size_le (db : ClauseDB p T) (n : Nat) :
    db.watch.size ≤ (db.ensureWatch n).watch.size := by
  unfold ClauseDB.ensureWatch
  split <;> rename_i h
  · rw [Array.size_append, Array.size_replicate]
    omega
  · omega

/-- Observing the clause array through `ensureWatch`. -/
private theorem ensureWatch_clauses (db : ClauseDB p T) (n : Nat) :
    (db.ensureWatch n).clauses = db.clauses := by
  unfold ClauseDB.ensureWatch
  split <;> rfl

/-- `ensureWatch` leaves the live count alone. -/
private theorem ensureWatch_live (db : ClauseDB p T) (n : Nat) :
    (db.ensureWatch n).live = db.live := by
  unfold ClauseDB.ensureWatch
  split <;> rfl

/-- `ensureWatch` leaves the free list alone. -/
private theorem ensureWatch_free (db : ClauseDB p T) (n : Nat) :
    (db.ensureWatch n).free = db.free := by
  unfold ClauseDB.ensureWatch
  split <;> rfl

/-- The `!` projection of an in-bounds index is a member. -/
private theorem getElem!_mem {α : Type} [Inhabited α] {xs : Array α} {i : Nat}
    (h : i < xs.size) : xs[i]! ∈ xs := by
  apply Array.mem_of_getElem?
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- `scanFind` only returns in-bounds positions. -/
private theorem scanFind_some_lt (doms : Array DomC) (lits : Array PLit) (w1 w2 : Nat) :
    ∀ (fuel j k : Nat), scanFind doms lits w1 w2 fuel j = some k → k < lits.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro j k h
      simp [scanFind] at h
  | succ fuel ih =>
      intro j k h
      unfold scanFind at h
      split at h
      · rename_i hlt
        split at h
        · simp at h
        · split at h
          · exact ih (j + 1) k h
          · split at h
            · rename_i q hq
              split at h
              · exact ih (j + 1) k h
              · simp only [Option.some.injEq] at h
                subst h
                exact hlt
            · exact ih (j + 1) k h
      · simp at h

/-- A successful replacement search can only happen in a clause of size at
least two (unit clauses are not watched). -/
private theorem scanFind_some_size (doms : Array DomC) (lits : Array PLit)
    (w1 w2 : Nat) :
    ∀ (fuel j k : Nat), scanFind doms lits w1 w2 fuel j = some k → 2 ≤ lits.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro j k h
      simp [scanFind] at h
  | succ fuel ih =>
      intro j k h
      unfold scanFind at h
      split at h
      · split at h
        · simp at h
        · rename_i hge
          split at h
          · exact ih (j + 1) k h
          · split at h
            · rename_i q hq
              split at h
              · exact ih (j + 1) k h
              · simp only [Option.some.injEq] at h
                subst h
                omega
            · exact ih (j + 1) k h
      · simp at h

/-- Watch-entry validity after moving a watch: grow the table, then push the
clause id into the new watch row. -/
private theorem watch_lt_ensureWatch_push {db : ClauseDB p T}
    (h : ∀ (i : Nat) (ids : Array Nat), db.watch[i]? = some ids →
      ∀ id ∈ ids, id < db.clauses.size)
    (q id : Nat) (hid : id < db.clauses.size) :
    let db2 := db.ensureWatch (q + 1)
    let db3 := { db2 with watch := db2.watch.set! q ((db2.watch.getD q #[]).push id) }
    ∀ (i : Nat) (ids : Array Nat), db3.watch[i]? = some ids →
      ∀ x ∈ ids, x < db3.clauses.size := by
  intro db2 db3 i ids hi x hx
  have hdb2cl : db2.clauses = db.clauses := by
    dsimp only [db2]
    rw [ensureWatch_clauses]
  have hdb3cl : db3.clauses = db.clauses := by
    dsimp only [db3]
    rw [hdb2cl]
  rw [hdb3cl]
  have hdb2wl : ∀ (i : Nat) (ids : Array Nat), db2.watch[i]? = some ids →
      ∀ x ∈ ids, x < db.clauses.size := by
    intro i ids hi x hx
    have hlt := watch_lt_ensureWatch h (q + 1) i ids hi x hx
    rwa [hdb2cl] at hlt
  have hqlt : q < db2.watch.size := by
    dsimp only [db2]
    have hge := ClauseDB.ensureWatch_size_ge db (q + 1)
    omega
  dsimp only [db3] at hi
  by_cases hiq : i = q
  · subst i
    rw [array_getElem?_set!_self (xs := db2.watch) (i := q)
      (v := (db2.watch.getD q #[]).push id) (h := hqlt)] at hi
    have hids : ids = (db2.watch.getD q #[]).push id := (Option.some.inj hi).symm
    subst ids
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · cases hrow : db2.watch[q]? with
      | none =>
          rw [Array.getD_eq_getD_getElem?, hrow] at hx
          simp at hx
      | some row =>
          rw [Array.getD_eq_getD_getElem?, hrow] at hx
          simp only [Option.getD_some] at hx
          exact hdb2wl q row hrow x hx
    · exact hid
  · rw [array_getElem?_set!_ne (xs := db2.watch) (i := q) (j := i)
      (v := (db2.watch.getD q #[]).push id) (h := fun hqi => hiq hqi.symm)] at hi
    exact hdb2wl i ids hi x hx

/-- One scan step: invariant preservation and provenance. -/
private theorem scanWatches_post
    (p : CompiledProblem DomConstraint) (T : LitTable) (doms : Array DomC)
    (l : PLit) (db0 : ClauseDB p T) (olds : Array Nat)
    (_hrow : db0.watchList l.idx = olds)
    (holds : ∀ id ∈ olds, id < db0.clauses.size)
    (_hlidx : l.idx < db0.watch.size) :
    ∀ (fuel i : Nat) (kept : Array Nat) (prunes : Array (PLit × Nat))
      (db : ClauseDB p T), ScanInv db0 l olds i kept db prunes →
      i + fuel = olds.size →
      ScanPost db0 (scanWatches p T doms l olds fuel i kept prunes db).1
        (scanWatches p T doms l olds fuel i kept prunes db).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro i kept prunes db hinv hif
      exact ScanInv.final_prune hinv (by omega)
  | succ fuel ih =>
      intro i kept prunes db hinv hif
      unfold scanWatches
      dsimp only
      split
      · -- i < olds.size
        rename_i hi
        split
        · -- no clause in this slot
          rename_i hnone
          have hslot : ∀ sc, db.clauses[olds[i]!]? = some sc →
              sc.deleted = true ∨ ¬ ClauseWatches sc l ∨ sc.e.lits.size < 2 := by
            intro sc hsc
            rw [hnone] at hsc
            cases hsc
          exact ih (i + 1) kept prunes db (ScanInv.skip hinv hi hslot) (by omega)
        · rename_i sc hget
          split
          · -- deleted
            rename_i hdelcond
            have hslot : ∀ sc', db.clauses[olds[i]!]? = some sc' →
                sc'.deleted = true ∨ ¬ ClauseWatches sc' l ∨ sc'.e.lits.size < 2 := by
              intro sc' hsc
              rw [hget] at hsc
              have hsc' : sc' = sc := (Option.some.inj hsc).symm
              subst hsc'
              exact Or.inl hdelcond
            exact ih (i + 1) kept prunes db (ScanInv.skip hinv hi hslot) (by omega)
          · -- live clause
            rename_i hdelcond
            have hdel : sc.deleted = false := by
              cases hd : sc.deleted with
              | false => rfl
              | true => exact (hdelcond (by simp [hd])).elim
            have hidlt : olds[i]! < db.clauses.size := by
              rcases Array.getElem?_eq_some_iff.mp hget with ⟨h, _⟩
              exact h
            have hsub : ∀ x ∈ kept, x ∈ kept.push olds[i]! :=
              fun x hx => Array.mem_push.mpr (Or.inl hx)
            have hpush_lt : ∀ x ∈ kept.push olds[i]!, x < db.clauses.size := by
              intro x hx
              rw [Array.mem_push] at hx
              rcases hx with hx | rfl
              · exact hinv.kept_lt x hx
              · exact hidlt
            split
            · -- clause watches l
              split
              · -- other watched position out of range
                rename_i hothernone
                have hslot : ∀ sc', db.clauses[olds[i]!]? = some sc' →
                    sc'.deleted = true ∨ ¬ ClauseWatches sc' l ∨
                      sc'.e.lits.size < 2 := by
                  intro sc' hsc
                  rw [hget] at hsc
                  have hsc' : sc' = sc := (Option.some.inj hsc).symm
                  rw [hsc']
                  by_cases hsz : 2 ≤ sc.e.lits.size
                  · exfalso
                    obtain ⟨hw1, hw2⟩ := hinv.pos_lt olds[i]! sc hget hdel hsz
                    have hsome1 : sc.e.lits[sc.w1]? ≠ none := by
                      rw [Array.getElem?_eq_getElem hw1]
                      simp
                    have hsome2 : sc.e.lits[sc.w2]? ≠ none := by
                      rw [Array.getElem?_eq_getElem hw2]
                      simp
                    have hpos : otherWatchedPos sc l = sc.w1 ∨
                        otherWatchedPos sc l = sc.w2 := by
                      unfold otherWatchedPos
                      split
                      · split
                        · right; rfl
                        · left; rfl
                      · right; rfl
                    rcases hpos with hp | hp
                    · rw [hp] at hothernone
                      exact hsome1 hothernone
                    · rw [hp] at hothernone
                      exact hsome2 hothernone
                  · exact Or.inr (Or.inr (by omega))
                exact ih (i + 1) kept prunes db (ScanInv.skip hinv hi hslot) (by omega)
              · rename_i other hother
                split
                · -- other is true: keep watching
                  have hnew : olds[i]! ∈ kept.push olds[i]! :=
                    Array.mem_push.mpr (Or.inr rfl)
                  have hinv' : ScanInv db0 l olds (i + 1) (kept.push olds[i]!) db prunes :=
                    hinv.withKept _ hi hsub hnew hpush_lt
                  exact ih (i + 1) _ prunes db hinv' (by omega)
                · -- other is not true
                  split
                  · -- replacement found
                    rename_i j hfind
                    split
                    · -- replacement position carries a literal
                      rename_i q hq
                      let sc' : StoredClause p T :=
                        if ClauseWatches₁ sc l then { sc with w1 := j }
                        else { sc with w2 := j }
                      let db1 : ClauseDB p T :=
                        { db with clauses := db.clauses.set! olds[i]! sc' }
                      let db2 : ClauseDB p T := db1.ensureWatch (q.idx + 1)
                      let db3 : ClauseDB p T :=
                        { db2 with
                          watch := db2.watch.set! q.idx
                            ((db2.watch.getD q.idx #[]).push olds[i]!) }
                      let kept' : Array Nat :=
                        if q.idx = l.idx ∨ other.idx = l.idx then
                          kept.push olds[i]!
                        else kept
                      change ScanPost db0
                        (scanWatches p T doms l olds fuel (i + 1) kept'
                          prunes db3).1
                        (scanWatches p T doms l olds fuel (i + 1) kept'
                          prunes db3).2
                      have hjlt : j < sc.e.lits.size :=
                        scanFind_some_lt doms sc.e.lits sc.w1 sc.w2 _ 0 j hfind
                      have hcl3 : db3.clauses = db.clauses.set! olds[i]! sc' := by
                        dsimp only [db3, db2]
                        rw [ensureWatch_clauses]
                      have hget3 : db3.clauses[olds[i]!]? = some sc' := by
                        rw [hcl3, array_getElem?_set!]
                        simp [hidlt]
                      have hqlt : q.idx < db2.watch.size := by
                        dsimp only [db2]
                        have hge := ClauseDB.ensureWatch_size_ge db1 (q.idx + 1)
                        omega
                      have hrows1 : RowsLe db db2 l.idx := by
                        intro i' _ x hx
                        rw [show db2.watchList i' = db.watchList i' from by
                          rw [ClauseDB.ensureWatch_watchList]
                          rfl]
                        exact hx
                      have hrows2 : RowsLe db2 db3 l.idx :=
                        RowsLe.of_watch_push db2 q.idx olds[i]! l.idx
                      have hrows : RowsLe db db3 l.idx := RowsLe.trans hrows1 hrows2
                      have hsize2 : 2 ≤ sc.e.lits.size :=
                        scanFind_some_size doms sc.e.lits sc.w1 sc.w2 _
                          0 j hfind
                      obtain ⟨hb1, hb2⟩ := hinv.backed olds[i]! sc hget hdel hsize2
                      have hsub' : ∀ x ∈ kept, x ∈ kept' := by
                        intro x hx
                        dsimp only [kept']
                        by_cases hcond : q.idx = l.idx ∨ other.idx = l.idx
                        · rw [if_pos hcond]
                          exact Array.mem_push.mpr (Or.inl hx)
                        · rw [if_neg hcond]
                          exact hx
                      have hsub_push : ∀ x ∈ kept', x ∈ kept.push olds[i]! := by
                        intro x hx
                        dsimp only [kept'] at hx
                        by_cases hcond : q.idx = l.idx ∨ other.idx = l.idx
                        · rw [if_pos hcond] at hx
                          exact hx
                        · rw [if_neg hcond] at hx
                          exact Array.mem_push.mpr (Or.inl hx)
                      have hkeep' : q.idx = l.idx ∨ other.idx = l.idx →
                          olds[i]! ∈ kept' := by
                        intro hcond
                        dsimp only [kept']
                        rw [if_pos hcond]
                        exact Array.mem_push.mpr (Or.inr rfl)
                      have hconv : ∀ (pos : Nat),
                          (∀ q', sc.e.lits[pos]? = some q' →
                            otherWatchedPos sc l = pos) →
                          ScanPosOK db l olds i kept olds[i]! sc pos →
                          ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc pos := by
                        intro pos hposEq hposq q' hq'
                        rcases hposq q' hq' with ⟨hidx, hmem⟩ | ⟨hne, hmem⟩
                        · refine Or.inl ⟨hidx, ?_⟩
                          rcases hmem with hk | hs
                          · exact Or.inl (hsub' olds[i]! hk)
                          · rw [mem_extract_succ hi] at hs
                            rcases hs with _ | hs
                            · have hop := hposEq q' hq'
                              rw [hop] at hother
                              have hqeq : q' = other :=
                                Option.some.inj (hq'.symm.trans hother)
                              exact Or.inl (hkeep' (Or.inr (by
                                simpa [hqeq] using hidx)))
                            · exact Or.inr hs
                        · exact Or.inr ⟨hne, hrows q'.idx hne olds[i]! hmem⟩
                      have hmoved : ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w1 ∧
                          ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w2 := by
                        by_cases hcw : ClauseWatches₁ sc l
                        · have hsc' : sc' = { sc with w1 := j } := by
                            dsimp only [sc']
                            rw [if_pos hcw]
                          have hpos1 : ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w1 := by
                            intro q' hq'
                            have hq'' : sc.e.lits[j]? = some q' := by
                              simpa [hsc'] using hq'
                            rw [hq] at hq''
                            have hq'e : q' = q := (Option.some.inj hq'').symm
                            subst q'
                            by_cases hqidx : q.idx = l.idx
                            · exact Or.inl ⟨hqidx, Or.inl (hkeep' (Or.inl hqidx))⟩
                            · exact Or.inr ⟨hqidx,
                                ClauseDB.watchesAt_set_push_self db2 q.idx olds[i]! hqlt⟩
                          have hpos2 : ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w2 := by
                            simpa [ScanPosOK, hsc'] using
                              hconv sc.w2 (fun _ _ => otherWatchedPos_eq_w2 hcw) hb2
                          exact ⟨hpos1, hpos2⟩
                        · have hsc' : sc' = { sc with w2 := j } := by
                            dsimp only [sc']
                            rw [if_neg hcw]
                          have hpos1 : ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w1 := by
                            simpa [ScanPosOK, hsc'] using
                              hconv sc.w1
                                (fun q' hq' => otherWatchedPos_eq_w1 hcw (by
                                  rw [hq']; simp)) hb1
                          have hpos2 : ScanPosOK db3 l olds (i + 1) kept' olds[i]! sc' sc'.w2 := by
                            intro q' hq'
                            have hq'' : sc.e.lits[j]? = some q' := by
                              simpa [hsc'] using hq'
                            rw [hq] at hq''
                            have hq'e : q' = q := (Option.some.inj hq'').symm
                            subst q'
                            by_cases hqidx : q.idx = l.idx
                            · exact Or.inl ⟨hqidx, Or.inl (hkeep' (Or.inl hqidx))⟩
                            · exact Or.inr ⟨hqidx,
                                ClauseDB.watchesAt_set_push_self db2 q.idx olds[i]! hqlt⟩
                          exact ⟨hpos1, hpos2⟩
                      have hinv3 : ScanInv db0 l olds (i + 1) kept' db3 prunes := by
                        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · -- watch_lt
                          have hwl1 : ∀ (i' : Nat) (ids : Array Nat), db1.watch[i']? = some ids →
                              ∀ x ∈ ids, x < db1.clauses.size := by
                            intro i' ids hiw x hx
                            have hlt := hinv.watch_lt i' ids hiw x hx
                            rw [show db1.clauses.size = db.clauses.size from by
                              dsimp only [db1]
                              rw [Array.size_set!]]
                            exact hlt
                          have hidlt1 : olds[i]! < db1.clauses.size := by
                            dsimp only [db1]
                            rw [Array.size_set!]
                            exact hidlt
                          exact watch_lt_ensureWatch_push hwl1 q.idx olds[i]! hidlt1
                        · -- pos_lt
                          intro id' scj hgetj hdelj hszj
                          by_cases hid' : id' = olds[i]!
                          · subst id'
                            rw [hcl3, array_getElem?_set!_self (xs := db.clauses)
                              (i := olds[i]!) (v := sc') (h := hidlt)] at hgetj
                            have hscj : scj = sc' := (Option.some.inj hgetj).symm
                            subst scj
                            by_cases hcw : ClauseWatches₁ sc l
                            · have hsz : 2 ≤ sc.e.lits.size := by
                                simpa [sc', hcw] using hszj
                              obtain ⟨h1, h2⟩ := hinv.pos_lt _ sc hget hdel hsz
                              have hsc' : sc' = { sc with w1 := j } := by
                                dsimp only [sc']
                                rw [if_pos hcw]
                              rw [hsc']
                              exact ⟨by simpa using hjlt, by simpa using h2⟩
                            · have hsz : 2 ≤ sc.e.lits.size := by
                                simpa [sc', hcw] using hszj
                              obtain ⟨h1, h2⟩ := hinv.pos_lt _ sc hget hdel hsz
                              have hsc' : sc' = { sc with w2 := j } := by
                                dsimp only [sc']
                                rw [if_neg hcw]
                              rw [hsc']
                              exact ⟨by simpa using h1, by simpa using hjlt⟩
                          · rw [hcl3, array_getElem?_set!_ne (xs := db.clauses) (i := olds[i]!)
                              (j := id') (v := sc') (h := fun h => hid' h.symm)] at hgetj
                            exact hinv.pos_lt id' scj hgetj hdelj hszj
                        · -- backed
                          intro id' scj hgetj hdelj hszj
                          by_cases hid' : id' = olds[i]!
                          · subst id'
                            rw [hcl3, array_getElem?_set!_self (xs := db.clauses)
                              (i := olds[i]!) (v := sc') (h := hidlt)] at hgetj
                            have hscj : scj = sc' := (Option.some.inj hgetj).symm
                            subst scj
                            exact hmoved
                          · have hgetdb : db.clauses[id']? = some scj := by
                              rw [hcl3, array_getElem?_set!_ne (xs := db.clauses)
                                (i := olds[i]!) (j := id') (v := sc')
                                (h := fun h => hid' h.symm)] at hgetj
                              exact hgetj
                            obtain ⟨h1, h2⟩ := hinv.backed id' scj hgetdb hdelj hszj
                            exact ⟨ScanPosOK.step_ne hi hrows hsub' hid' h1,
                              ScanPosOK.step_ne hi hrows hsub' hid' h2⟩
                        · -- live_eq
                          have hlive3 : db3.live = db.live := by
                            dsimp only [db3, db2]
                            rw [ensureWatch_live]
                          rw [hlive3]
                          have hdc : db3.deletedCount = db.deletedCount := by
                            unfold ClauseDB.deletedCount
                            rw [hcl3]
                            exact ClauseDB.deletedCount_set_same db _ sc sc' hget hidlt
                              (by by_cases hcw : ClauseWatches₁ sc l <;> simp [sc', hcw])
                          have hsz3 : db3.clauses.size = db.clauses.size := by
                            rw [hcl3, Array.size_set!]
                          unfold ClauseDB.liveCount
                          rw [hsz3, hdc]
                          exact hinv.live_eq
                        · -- free_deleted
                          intro x hx
                          have hfree3 : db3.free = db.free := by
                            dsimp only [db3, db2]
                            rw [ensureWatch_free]
                          rw [hfree3] at hx
                          obtain ⟨sc0, hcl0, hdel0⟩ := hinv.free_deleted x hx
                          by_cases hxid : x = olds[i]!
                          · subst x
                            rw [hget] at hcl0
                            have hsc0 : sc0 = sc := (Option.some.inj hcl0).symm
                            subst sc0
                            rw [hdel] at hdel0
                            simp at hdel0
                          · refine ⟨sc0, ?_, hdel0⟩
                            rw [hcl3, array_getElem?_set!_ne (xs := db.clauses)
                              (i := olds[i]!) (j := x) (v := sc')
                              (h := fun h => hxid h.symm)]
                            exact hcl0
                        · -- free_nodup
                          have hfree3 : db3.free = db.free := by
                            dsimp only [db3, db2]
                            rw [ensureWatch_free]
                          rw [hfree3]
                          exact hinv.free_nodup
                        · -- kept_lt
                          intro x hx
                          rw [show db3.clauses.size = db.clauses.size from by
                            rw [hcl3, Array.size_set!]]
                          exact hpush_lt x (hsub_push x hx)
                        · -- lidx_lt
                          have hle : db.watch.size ≤ db3.watch.size := by
                            have h1 : db.watch.size ≤ db2.watch.size := by
                              have h := ensureWatch_watch_size_le db1 (q.idx + 1)
                              dsimp only [db2]
                              exact h
                            rw [show db3.watch.size = db2.watch.size from Array.size_set! _ _ _]
                            exact h1
                          exact Nat.lt_of_lt_of_le hinv.lidx_lt hle
                        · -- size_eq
                          rw [hcl3, Array.size_set!]
                          exact hinv.size_eq
                        · -- live_eq0
                          have hlive3 : db3.live = db.live := by
                            dsimp only [db3, db2]
                            rw [ensureWatch_live]
                          rw [hlive3]
                          exact hinv.live_eq0
                        · -- free_eq0
                          have hfree3 : db3.free = db.free := by
                            dsimp only [db3, db2]
                            rw [ensureWatch_free]
                          rw [hfree3]
                          exact hinv.free_eq0
                        · -- meta_eq
                          intro k
                          by_cases hk : k = olds[i]!
                          · subst k
                            have hmd : clauseMeta db olds[i]! = some (sc.e, sc.deleted) := by
                              unfold clauseMeta
                              rw [hget]
                              rfl
                            have hm3 : clauseMeta db3 olds[i]! = some (sc'.e, sc'.deleted) := by
                              unfold clauseMeta
                              rw [hget3]
                              rfl
                            rw [hm3, ← hinv.meta_eq olds[i]!, hmd]
                            by_cases hcw : ClauseWatches₁ sc l <;> simp [sc', hcw]
                          · have hkread : db3.clauses[k]? = db.clauses[k]? := by
                              rw [hcl3, array_getElem?_set!_ne (xs := db.clauses)
                                (i := olds[i]!) (j := k) (v := sc')
                                (h := fun h => hk h.symm)]
                            unfold clauseMeta
                            rw [hkread]
                            exact hinv.meta_eq k
                        · -- prunes_ok
                          exact hinv.prunes_ok
                      exact ih (i + 1) kept' prunes db3 hinv3 (by omega)
                    · -- replacement position is out of range
                      rename_i hnonej
                      exfalso
                      have hjlt : j < sc.e.lits.size :=
                        scanFind_some_lt doms sc.e.lits sc.w1 sc.w2 _ 0 j hfind
                      have hsome : sc.e.lits[j]? ≠ none := by
                        rw [Array.getElem?_eq_getElem hjlt]
                        simp
                      exact hsome hnonej
                  · -- no replacement
                    split
                    · -- other is false: conflict
                      exact ScanInv.conflict_post hinv holds hi hget hdel hidlt
                    · -- other is unknown: prune
                      have hnew : db0.PrunesOK (prunes.push (other, olds[i]!)) := by
                        intro l' id' hmem
                        rw [Array.mem_push] at hmem
                        rcases hmem with hmem | ⟨rfl, rfl⟩
                        · exact hinv.prunes_ok l' id' hmem
                        · obtain ⟨sc0, hget0, he0, hdel0⟩ :=
                            clauseMeta.back hinv.meta_eq hget
                          refine ⟨sc0, hget0, ?_, ?_⟩
                          · rw [hdel0, hdel]
                          · rw [he0, Array.mem_map]
                            exact ⟨other, Array.mem_of_getElem? hother, rfl⟩
                      have hkeepmem : olds[i]! ∈ kept.push olds[i]! :=
                        Array.mem_push.mpr (Or.inr rfl)
                      have hinv' : ScanInv db0 l olds (i + 1) (kept.push olds[i]!) db
                          (prunes.push (other, olds[i]!)) :=
                        { hinv.withKept _ hi hsub hkeepmem hpush_lt with prunes_ok := hnew }
                      exact ih (i + 1) _ _ db hinv' (by omega)
            · -- clause does not watch l: stale entry
              rename_i hnw
              have hslot : ∀ sc', db.clauses[olds[i]!]? = some sc' →
                  sc'.deleted = true ∨ ¬ ClauseWatches sc' l ∨
                    sc'.e.lits.size < 2 := by
                intro sc' hsc
                rw [hget] at hsc
                have hsc' : sc' = sc := (Option.some.inj hsc).symm
                subst hsc'
                exact Or.inr (Or.inl hnw)
              exact ih (i + 1) kept prunes db (ScanInv.skip hinv hi hslot) (by omega)
      · -- scan finished
        exact ScanInv.final_prune hinv (by omega)

/-- Overwriting a slot by a clause with the same carried clause and deletion
flag leaves every `clauseMeta` observation unchanged. -/
private theorem clauseMeta_set_same {db : ClauseDB p T} {id : Nat}
    {sc sc' : StoredClause p T}
    (hget : db.clauses[id]? = some sc)
    (he : sc'.e = sc.e) (hd : sc'.deleted = sc.deleted) :
    ∀ k, clauseMeta ({ db with clauses := db.clauses.set! id sc' }) k =
      clauseMeta db k := by
  have hsize : id < db.clauses.size := by
    rcases Array.getElem?_eq_some_iff.mp hget with ⟨h, _⟩
    exact h
  intro k
  by_cases hk : k = id
  · subst k
    unfold clauseMeta
    rw [array_getElem?_set!_self (xs := db.clauses) (i := id) (v := sc') (h := hsize)]
    rw [hget]
    simp [he, hd]
  · unfold clauseMeta
    rw [array_getElem?_set!_ne (xs := db.clauses) (i := id) (j := k) (v := sc')
      (h := fun h => hk h.symm)]

/-- The provenance fragment of the scan invariant: clause metadata and the
soundness of the accumulated prunings. -/
private structure ScanProv (db0 : ClauseDB p T) (db : ClauseDB p T)
    (prunes : Array (PLit × Nat)) : Prop where
  meta_eq : ∀ (id : Nat), clauseMeta db id = clauseMeta db0 id
  prunes_ok : db0.PrunesOK prunes
  size_eq : db.clauses.size = db0.clauses.size
  live_eq : db.live = db0.live
  free_eq : db.free = db0.free

/-- Provenance postcondition of one scan. -/
private structure ScanProvPost (db0 : ClauseDB p T) (db' : ClauseDB p T)
    (out : WPropOut p T) : Prop where
  meta_eq : ∀ (id : Nat), clauseMeta db' id = clauseMeta db0 id
  conflict : ∀ (c : EClause p T) (id : Nat), out = .conflict c id →
    db0.ConflictOK c id
  prune : ∀ ps, out = .prune ps → db0.PrunesOK ps
  size_eq : db'.clauses.size = db0.clauses.size
  live_eq : db'.live = db0.live
  free_eq : db'.free = db0.free

/-- One scan step, provenance only (no invariant assumptions). -/
private theorem scanWatches_prov
    (p : CompiledProblem DomConstraint) (T : LitTable) (doms : Array DomC)
    (l : PLit) (db0 : ClauseDB p T) (olds : Array Nat)
    (_hrow : db0.watchList l.idx = olds) :
    ∀ (fuel i : Nat) (kept : Array Nat) (prunes : Array (PLit × Nat))
      (db : ClauseDB p T), ScanProv db0 db prunes →
      ScanProvPost db0 (scanWatches p T doms l olds fuel i kept prunes db).1
        (scanWatches p T doms l olds fuel i kept prunes db).2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro i kept prunes db hprov
      have hred : scanWatches p T doms l olds 0 i kept prunes db =
          ({ db with watch := db.watch.set! l.idx kept }, .prune prunes) := rfl
      rw [hred]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro id
        exact hprov.meta_eq id
      · intro c id hout
        simp at hout
      · intro ps hout
        simp only [WPropOut.prune.injEq] at hout
        subst hout
        exact hprov.prunes_ok
      · exact hprov.size_eq
      · exact hprov.live_eq
      · exact hprov.free_eq
  | succ fuel ih =>
      intro i kept prunes db hprov
      unfold scanWatches
      dsimp only
      split
      · -- i < olds.size
        rename_i hi
        split
        · -- no clause in this slot
          exact ih (i + 1) kept prunes db hprov
        · rename_i sc hget
          split
          · -- deleted
            exact ih (i + 1) kept prunes db hprov
          · -- live clause
            rename_i hdelcond
            have hdel : sc.deleted = false := by
              cases hd : sc.deleted with
              | false => rfl
              | true => exact (hdelcond (by simp [hd])).elim
            split
            · -- clause watches l
              split
              · -- other watched position out of range
                exact ih (i + 1) kept prunes db hprov
              · rename_i other hother
                split
                · -- other is true: keep watching
                  exact ih (i + 1) (kept.push olds[i]!) prunes db hprov
                · -- other is not true
                  split
                  · -- replacement found
                    rename_i j hfind
                    split
                    · -- replacement position carries a literal
                      rename_i q hq
                      let sc' : StoredClause p T :=
                        if ClauseWatches₁ sc l then { sc with w1 := j }
                        else { sc with w2 := j }
                      let db1 : ClauseDB p T :=
                        { db with clauses := db.clauses.set! olds[i]! sc' }
                      let db2 : ClauseDB p T := db1.ensureWatch (q.idx + 1)
                      let db3 : ClauseDB p T :=
                        { db2 with
                          watch := db2.watch.set! q.idx
                            ((db2.watch.getD q.idx #[]).push olds[i]!) }
                      let kept' : Array Nat :=
                        if q.idx = l.idx ∨ other.idx = l.idx then
                          kept.push olds[i]!
                        else kept
                      change ScanProvPost db0
                        (scanWatches p T doms l olds fuel (i + 1) kept'
                          prunes db3).1
                        (scanWatches p T doms l olds fuel (i + 1) kept'
                          prunes db3).2
                      have hsc'e : sc'.e = sc.e := by
                        by_cases hcw : ClauseWatches₁ sc l <;> simp [sc', hcw]
                      have hsc'd : sc'.deleted = sc.deleted := by
                        by_cases hcw : ClauseWatches₁ sc l <;> simp [sc', hcw]
                      have hmeta3 : ∀ k, clauseMeta db3 k = clauseMeta db k := by
                        intro k
                        have hcl3 : db3.clauses = db.clauses.set! olds[i]! sc' := by
                          dsimp only [db3, db2]
                          rw [ensureWatch_clauses]
                        calc clauseMeta db3 k
                            = clauseMeta ({ db with clauses := db.clauses.set! olds[i]! sc' }) k := by
                              unfold clauseMeta
                              rw [hcl3]
                          _ = clauseMeta db k := clauseMeta_set_same hget hsc'e hsc'd k
                      have hsz3 : db3.clauses.size = db.clauses.size := by
                        dsimp only [db3, db2]
                        rw [ensureWatch_clauses, Array.size_set!]
                      have hlive3 : db3.live = db.live := by
                        dsimp only [db3, db2]
                        rw [ensureWatch_live]
                      have hfree3 : db3.free = db.free := by
                        dsimp only [db3, db2]
                        rw [ensureWatch_free]
                      have hprov3 : ScanProv db0 db3 prunes :=
                        ⟨fun k => (hmeta3 k).trans (hprov.meta_eq k), hprov.prunes_ok,
                          hsz3.trans hprov.size_eq, hlive3.trans hprov.live_eq,
                          hfree3.trans hprov.free_eq⟩
                      exact ih (i + 1) kept' prunes db3 hprov3
                    · -- replacement position out of range
                      exact ih (i + 1) kept prunes db hprov
                  · -- no replacement
                    split
                    · -- other is false: conflict
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                      · intro k
                        exact hprov.meta_eq k
                      · intro c id' hout
                        simp only [WPropOut.conflict.injEq] at hout
                        obtain ⟨he, hi⟩ := hout
                        subst hi
                        have hconf : db0.ConflictOK sc.e olds[i]! := by
                          obtain ⟨sc0, hget0, he0, hdel0⟩ :=
                            clauseMeta.back hprov.meta_eq hget
                          exact ⟨sc0, hget0, by rw [hdel0, hdel], he0⟩
                        rw [← he]
                        exact hconf
                      · intro ps hout
                        simp at hout
                      · exact hprov.size_eq
                      · exact hprov.live_eq
                      · exact hprov.free_eq
                    · -- other is unknown: prune
                      have hnew : db0.PrunesOK (prunes.push (other, olds[i]!)) := by
                        intro l' id' hmem
                        rw [Array.mem_push] at hmem
                        rcases hmem with hmem | ⟨rfl, rfl⟩
                        · exact hprov.prunes_ok l' id' hmem
                        · obtain ⟨sc0, hget0, he0, hdel0⟩ :=
                            clauseMeta.back hprov.meta_eq hget
                          refine ⟨sc0, hget0, ?_, ?_⟩
                          · rw [hdel0, hdel]
                          · rw [he0, Array.mem_map]
                            exact ⟨other, Array.mem_of_getElem? hother, rfl⟩
                      have hprov' : ScanProv db0 db (prunes.push (other, olds[i]!)) :=
                        ⟨hprov.meta_eq, hnew, hprov.size_eq, hprov.live_eq, hprov.free_eq⟩
                      exact ih (i + 1) _ _ db hprov'
            · -- clause does not watch l: stale entry
              exact ih (i + 1) kept prunes db hprov
      · -- scan finished
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro id
          exact hprov.meta_eq id
        · intro c id hout
          simp at hout
        · intro ps hout
          simp only [WPropOut.prune.injEq] at hout
          subst hout
          exact hprov.prunes_ok
        · exact hprov.size_eq
        · exact hprov.live_eq
        · exact hprov.free_eq

/-- Computation form of `propagateLiteral`: the scan followed by output
shaping. -/
private theorem propagateLiteral_eq (db : ClauseDB p T) (doms : Array DomC) (l : PLit) :
    db.propagateLiteral p T doms l =
      (let r := propagateScan p T db doms l; (r.1, r.2.shape)) := rfl

/-- `ensureWatch` preserves the clause-database invariant. -/
theorem ClauseDB.ensureWatch_inv (db : ClauseDB p T) (n : Nat) (h : db.Inv) :
    (db.ensureWatch n).Inv := by
  have hcl := ensureWatch_clauses db n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi x hx
    have hlt : x < db.clauses.size := by
      unfold ClauseDB.ensureWatch at hi
      split at hi
      · rw [Array.getElem?_append] at hi
        by_cases hin : i < db.watch.size
        · rw [if_pos hin] at hi
          exact h.watch_lt i ids hi x hx
        · rw [if_neg hin] at hi
          rw [Array.getElem?_replicate] at hi
          split at hi
          · have hids : ids = #[] := (Option.some.inj hi).symm
            subst ids
            simp at hx
          · simp at hi
      · exact h.watch_lt i ids hi x hx
    rwa [hcl]
  · intro id sc hget hdel hsz
    rw [hcl] at hget
    exact h.pos_lt id sc hget hdel hsz
  · intro id sc hget hdel hsz
    rw [hcl] at hget
    obtain ⟨h1, h2⟩ := h.watches id sc hget hdel hsz
    exact ⟨fun q hq => ClauseDB.watchesAt_ensureWatch db n q.idx id (h1 q hq),
      fun q hq => ClauseDB.watchesAt_ensureWatch db n q.idx id (h2 q hq)⟩
  · simpa [ClauseDB.liveCount, ClauseDB.deletedCount, ensureWatch_live,
      ensureWatch_clauses] using h.live_eq
  · rw [ensureWatch_free]
    intro id hid
    obtain ⟨sc, hget, hdel⟩ := h.free_deleted id hid
    exact ⟨sc, by rw [hcl]; exact hget, hdel⟩
  · rw [ensureWatch_free]
    exact h.free_nodup

/-- The full scan postcondition for a `propagateLiteral` run on an invariant
database. -/
private theorem propagateLiteral_scanPost (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) (hinv : db.Inv) :
    ScanPost (db.ensureWatch (l.idx + 1)) (propagateScan p T db doms l).1
      (propagateScan p T db doms l).2 := by
  unfold propagateScan
  dsimp only
  have hdb0 : (db.ensureWatch (l.idx + 1)).Inv :=
    ClauseDB.ensureWatch_inv db (l.idx + 1) hinv
  have hlidx : l.idx < (db.ensureWatch (l.idx + 1)).watch.size := by
    have hge := ClauseDB.ensureWatch_size_ge db (l.idx + 1)
    omega
  have holds : ∀ id ∈ (db.ensureWatch (l.idx + 1)).watchList l.idx,
      id < (db.ensureWatch (l.idx + 1)).clauses.size := by
    intro id hid
    obtain ⟨ids, hi, hmem⟩ :=
      (ClauseDB.mem_watchList_iff (db.ensureWatch (l.idx + 1)) l.idx id).mp hid
    exact hdb0.watch_lt l.idx ids hi id hmem
  exact scanWatches_post p T doms l (db.ensureWatch (l.idx + 1))
    ((db.ensureWatch (l.idx + 1)).watchList l.idx) rfl holds hlidx
    ((db.ensureWatch (l.idx + 1)).watchList l.idx).size 0 #[] #[]
    (db.ensureWatch (l.idx + 1))
    (ScanInv.base hdb0 rfl holds hlidx (by intro l' id' hm; simp at hm))
    (by simp)

/-- The provenance postcondition for a `propagateLiteral` run (no invariant
needed). -/
private theorem propagateLiteral_scanProv (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) :
    ScanProvPost (db.ensureWatch (l.idx + 1)) (propagateScan p T db doms l).1
      (propagateScan p T db doms l).2 := by
  unfold propagateScan
  dsimp only
  have hprov : ScanProv (db.ensureWatch (l.idx + 1))
      (db.ensureWatch (l.idx + 1)) #[] :=
    ⟨fun _ => rfl, by intro l' id' hm; simp at hm, rfl, rfl, rfl⟩
  exact scanWatches_prov p T doms l (db.ensureWatch (l.idx + 1))
    ((db.ensureWatch (l.idx + 1)).watchList l.idx) rfl
    ((db.ensureWatch (l.idx + 1)).watchList l.idx).size 0 #[] #[]
    (db.ensureWatch (l.idx + 1)) hprov

/-- Two-watched-literal propagation preserves the clause-database invariant. -/
theorem ClauseDB.propagateLiteral_inv (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) (h : db.Inv) : (db.propagateLiteral p T doms l).1.Inv := by
  have h' := (propagateLiteral_scanPost db doms l h).inv
  simpa [ClauseDB.propagateLiteral] using h'

/-- A conflict reported by `propagateLiteral` names a live stored clause whose
carried clause is returned. -/
theorem ClauseDB.propagateLiteral_conflict (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) {c : EClause p T} {id : Nat}
    (h : (db.propagateLiteral p T doms l).2 = .conflict c id) :
    db.ConflictOK c id := by
  have h' : (propagateScan p T db doms l).2.shape = .conflict c id := by
    simpa [ClauseDB.propagateLiteral] using h
  have hc := (propagateLiteral_scanProv db doms l).conflict c id
    (WPropOut.shape_conflict h')
  simpa [ClauseDB.ConflictOK, ensureWatch_clauses] using hc

/-- Every pruning reported by `propagateLiteral` is a literal occurrence of a
live stored clause. -/
theorem ClauseDB.propagateLiteral_prunes (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) {ps : Array (PLit × Nat)}
    (h : (db.propagateLiteral p T doms l).2 = .prune ps) :
    db.PrunesOK ps := by
  have h' : (propagateScan p T db doms l).2.shape = .prune ps := by
    simpa [ClauseDB.propagateLiteral] using h
  obtain ⟨ps0, hout, hps⟩ := WPropOut.shape_prune h'
  have hp := (propagateLiteral_scanProv db doms l).prune ps0 hout
  rw [hps]
  simpa [ClauseDB.PrunesOK, ensureWatch_clauses] using hp

/-- Transport a clause-metadata equality to the carried clauses. -/
private theorem clauseMeta.e_eq {db db' : ClauseDB p T}
    (h : ∀ id, clauseMeta db' id = clauseMeta db id) (id : Nat) :
    (db'.clauses[id]?).map (fun sc : StoredClause p T => sc.e) =
      (db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) := by
  have h' := congrArg (Option.map (fun q : EClause p T × Bool => q.1)) (h id)
  simpa [clauseMeta, Option.map_map, Function.comp_def] using h'

/-- Transport a clause-metadata equality to the deletion flags. -/
private theorem clauseMeta.deleted_eq {db db' : ClauseDB p T}
    (h : ∀ id, clauseMeta db' id = clauseMeta db id) (id : Nat) :
    (db'.clauses[id]?).map (fun sc : StoredClause p T => sc.deleted) =
      (db.clauses[id]?).map (fun sc : StoredClause p T => sc.deleted) := by
  have h' := congrArg (Option.map (fun q : EClause p T × Bool => q.2)) (h id)
  simpa [clauseMeta, Option.map_map, Function.comp_def] using h'

/-- Propagation never changes the carried clauses: the `e` component is
pointwise preserved. -/
theorem ClauseDB.propagateLiteral_clauses_e (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) :
    ∀ (id : Nat), ((db.propagateLiteral p T doms l).1.clauses[id]?).map
        (fun sc : StoredClause p T => sc.e) =
      (db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) := by
  intro id
  have hmeta := (propagateLiteral_scanProv db doms l).meta_eq
  have h1 := clauseMeta.e_eq hmeta id
  rw [ensureWatch_clauses db (l.idx + 1)] at h1
  simpa [ClauseDB.propagateLiteral] using h1

/-- Propagation never changes the deletion flags. -/
theorem ClauseDB.propagateLiteral_clauses_deleted (db : ClauseDB p T)
    (doms : Array DomC) (l : PLit) :
    ∀ (id : Nat), ((db.propagateLiteral p T doms l).1.clauses[id]?).map
        (fun sc : StoredClause p T => sc.deleted) =
      (db.clauses[id]?).map (fun sc : StoredClause p T => sc.deleted) := by
  intro id
  have hmeta := (propagateLiteral_scanProv db doms l).meta_eq
  have h1 := clauseMeta.deleted_eq hmeta id
  rw [ensureWatch_clauses db (l.idx + 1)] at h1
  simpa [ClauseDB.propagateLiteral] using h1

/-- Propagation never changes the number of clause slots. -/
theorem ClauseDB.propagateLiteral_clauses_size (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) : (db.propagateLiteral p T doms l).1.clauses.size = db.clauses.size := by
  have h := (propagateLiteral_scanProv db doms l).size_eq
  simpa [ClauseDB.propagateLiteral, ensureWatch_clauses] using h

/-- Propagation never changes the live count. -/
theorem ClauseDB.propagateLiteral_live (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) : (db.propagateLiteral p T doms l).1.live = db.live := by
  have h := (propagateLiteral_scanProv db doms l).live_eq
  simpa [ClauseDB.propagateLiteral, ensureWatch_live] using h

/-- Propagation never changes the free list. -/
theorem ClauseDB.propagateLiteral_free (db : ClauseDB p T) (doms : Array DomC)
    (l : PLit) : (db.propagateLiteral p T doms l).1.free = db.free := by
  have h := (propagateLiteral_scanProv db doms l).free_eq
  simpa [ClauseDB.propagateLiteral, ensureWatch_free] using h

end LeanFzn.Engine
