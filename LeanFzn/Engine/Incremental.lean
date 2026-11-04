/-
File: LeanFzn/Engine/Incremental.lean

N11b: incremental Core.  Clause databases and engine seeds are carried
across objective-bound rounds of branch and bound.

Two transports are provided:

* `ClauseDB.rebase` changes the *problem* of a database from `p` to a
  stronger `q` (same box, stronger acceptance), mapping every stored
  clause's entailment proof through `Entailed_mono`.  This is the step the
  optimizer performs when it adds `spec.improveBound v`.

* `ClauseDB.retype` changes the *literal table* parameter of a database
  without changing any stored data.  `LitTable.decode` reads the
  denotation carried by each packed literal, so the table argument is
  semantically inert; the reindexing is needed only because `EngineState`
  fixes the table parameter while its `table` field grows.

`CoreSeed` bundles a carried database with its literal table and a
`seeded` flag: `false` is the first round (the entry must install the
problem's seed clauses), `true` is a later round (the database already
contains them).  `coreSolveSeed` mirrors `coreSolveFull`, starting either
from `addSeedClauses` or from the carried database, and returns the
terminal database together with the terminal table so watch indices stay
aligned across rounds.

DAG: LeanFzn.Engine.Search -> this file -> Integration.CoreSeed.
No proof holes, no custom axioms.
-/
import LeanFzn.Engine.Search

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

namespace LeanFzn.Engine

/-! ## Reindexing the literal table -/

/-- Change the literal-table parameter of a clause database without
changing any stored data.  `LitTable.decode` is independent of the table
(the denotation is carried by each `PLit`), so every entailment proof is
valid at the new table argument. -/
def ClauseDB.retype {p : CompiledProblem DomConstraint} {T T' : LitTable}
    (db : ClauseDB p T) : ClauseDB p T' :=
  { clauses := db.clauses.map fun sc =>
      { e := { lits := sc.e.lits, ent := sc.e.ent }
        w1 := sc.w1
        w2 := sc.w2
        deleted := sc.deleted
        lbd := sc.lbd }
    watch := db.watch
    free := db.free
    live := db.live }

@[simp] theorem ClauseDB.retype_clauses_size {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) :
    (db.retype (T' := T')).clauses.size = db.clauses.size := by
  simp [ClauseDB.retype]

@[simp] theorem ClauseDB.retype_live {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) :
    (db.retype (T' := T')).live = db.live := rfl

@[simp] theorem ClauseDB.retype_watch {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) :
    (db.retype (T' := T')).watch = db.watch := rfl

@[simp] theorem ClauseDB.retype_free {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) :
    (db.retype (T' := T')).free = db.free := rfl

/-! ## Rebasing a database on a stronger problem -/

/-- Transport a clause database from `p` to a stronger problem `q`: the box
is unchanged and every assignment accepted by `q` is accepted by `p`, so
every stored clause's entailment proof transfers by `Entailed_mono`.
`lits`, the watches, the free list and `live` are unchanged. -/
def ClauseDB.rebase {p q : CompiledProblem DomConstraint} {T : LitTable}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) : ClauseDB q T :=
  { clauses := db.clauses.map fun sc =>
      { e := { lits := sc.e.lits, ent := Entailed_mono hdoms hacc sc.e.ent }
        w1 := sc.w1
        w2 := sc.w2
        deleted := sc.deleted
        lbd := sc.lbd }
    watch := db.watch
    free := db.free
    live := db.live }

@[simp] theorem ClauseDB.rebase_clauses_size {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) :
    (db.rebase hdoms hacc).clauses.size = db.clauses.size := by
  simp [ClauseDB.rebase]

@[simp] theorem ClauseDB.rebase_live {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) :
    (db.rebase hdoms hacc).live = db.live := rfl

@[simp] theorem ClauseDB.rebase_watch {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) :
    (db.rebase hdoms hacc).watch = db.watch := rfl

@[simp] theorem ClauseDB.rebase_free {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) :
    (db.rebase hdoms hacc).free = db.free := rfl

/-! ## The carried Core seed -/

/-- A Core engine seed carried between objective-bound rounds.  `T` is the
literal table the database's watch indices refer to; `seeded` records
whether the problem's seed clauses have already been installed in `db`. -/
structure CoreSeed (p : CompiledProblem DomConstraint) where
  /-- The literal intern table shared by the carried database. -/
  T : LitTable
  /-- The carried clause database, entailed at this round's problem. -/
  db : ClauseDB p T
  /-- `false` on the first round (the entry installs the seed clauses),
      `true` once the database already contains them. -/
  seeded : Bool

namespace CoreSeed

/-- The first round's seed: empty database, empty table, unseeded. -/
def initial (p : CompiledProblem DomConstraint) : CoreSeed p :=
  { T := {}, db := {}, seeded := false }

/-- Transport a seed to a stronger problem with the same box. -/
def rebase {p q : CompiledProblem DomConstraint}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (s : CoreSeed p) : CoreSeed q :=
  { T := s.T, db := s.db.rebase hdoms hacc, seeded := s.seeded }

@[simp] theorem rebase_T {p q : CompiledProblem DomConstraint}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (s : CoreSeed p) : (s.rebase hdoms hacc).T = s.T := rfl

@[simp] theorem rebase_db_live {p q : CompiledProblem DomConstraint}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (s : CoreSeed p) : (s.rebase hdoms hacc).db.live = s.db.live := rfl

@[simp] theorem rebase_seeded {p q : CompiledProblem DomConstraint}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (s : CoreSeed p) : (s.rebase hdoms hacc).seeded = s.seeded := rfl

@[simp] theorem initial_seeded (p : CompiledProblem DomConstraint) :
    (initial p).seeded = false := rfl

@[simp] theorem initial_live (p : CompiledProblem DomConstraint) :
    (initial p).db.live = 0 := rfl

end CoreSeed

/-! ## The seeded entry -/

/-- Package a terminal engine state as the next round's seed, reindexing the
database from the entry's table parameter to the grown `st.table`. -/
def coreSolveSeedFinish {p : CompiledProblem DomConstraint} {T : LitTable}
    (st : EngineState p T) (r : CoreResult) :
    CoreResult × EngineStats × CoreSeed p :=
  (r, st.stats, { T := st.table, db := st.db.retype, seeded := true })

/-- The verdict component of a finished seeded solve. -/
@[simp] theorem coreSolveSeedFinish_fst {p : CompiledProblem DomConstraint}
    {T : LitTable} (st : EngineState p T) (r : CoreResult) :
    (coreSolveSeedFinish st r).1 = r := rfl

/-- The common tail of the seeded entry: empty-clause check, root unit
propagation, and the CDCL loop.  This is the exact tail of `coreSolveFull`
with the state threaded back out. -/
def coreSolveSeedTail (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) (s : CoreSeed p) (st : EngineState p s.T) :
    CoreResult × EngineStats × CoreSeed p :=
  let prio := annotPrioArray p
  let orders := configOrders p o
  match st.db.emptyConflict? with
  | some _ => coreSolveSeedFinish st .unsat
  | none =>
      let (db, out) := st.db.propagateUnits p s.T st.doms
      match out with
      | .none =>
          let st := { st with db := db }
          let (r, st) := search p s.T st.doms o prio orders st #[] fuel
          coreSolveSeedFinish st r
      | .prune ps =>
          let st := { st with db := db }
          let (r, st) := search p s.T st.doms o prio orders st
            (pushClausePrunes #[] ps) fuel
          coreSolveSeedFinish st r
      | .conflict ec _ =>
          let a := analyze p s.T st.doms st ec fuel
          let st := { st with db := db }
          if !a.ok then coreSolveSeedFinish st .gaveUp
          else
            match a.learned with
            | none => coreSolveSeedFinish st .gaveUp
            | some lc =>
                if lc.lits.isEmpty then coreSolveSeedFinish st .unsat
                else coreSolveSeedFinish st .gaveUp

/-- The seeded entry.  It mirrors `coreSolveFull`, except that the carried
literal table is used instead of the empty table and, when `s.seeded = true`,
the carried database replaces the freshly initialised one (it already
contains the problem's seed clauses).  The returned seed carries the
terminal table and database for the next objective-bound round. -/
def coreSolveSeed (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) (s : CoreSeed p) :
    CoreResult × EngineStats × CoreSeed p :=
  match initState p s.T with
  | none => (.gaveUp, { gaveUp := 1 }, s)
  | some st0 =>
      if s.seeded then
        coreSolveSeedTail p o fuel s { st0 with db := s.db }
      else
        match addSeedClauses p s.T st0 with
        | (st, some _) =>
            -- An entailed empty seed clause is a root refutation.
            let st := { st with
              stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
            (.unsat, st.stats,
              { T := st.table, db := st.db.retype, seeded := true })
        | (st, none) => coreSolveSeedTail p o fuel s st

/-! ## Soundness of the seeded entry -/

/-- Every `.sat` result of the common tail is a box member accepted by the
problem. -/
theorem coreSolveSeedTail_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p}
    {st : EngineState p s.T} {a : List Value}
    (h : (coreSolveSeedTail p o fuel s st).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveSeedTail at h
  dsimp only at h
  split at h
  · simp [coreSolveSeedFinish_fst] at h
  · split at h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_sat p _ _ _ _ _ _ _ _ _ h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_sat p _ _ _ _ _ _ _ _ _ h
    · split at h
      · simp [coreSolveSeedFinish_fst] at h
      · split at h
        · simp [coreSolveSeedFinish_fst] at h
        · split at h
          · simp [coreSolveSeedFinish_fst] at h
          · simp [coreSolveSeedFinish_fst] at h

/-- Every `.unsat` result of the common tail excludes every accepted
assignment: the three sources are an empty stored clause, an empty clause
learned by root propagation analysis, and the CDCL loop's empty learned
clause. -/
theorem coreSolveSeedTail_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p}
    {st : EngineState p s.T}
    (h : (coreSolveSeedTail p o fuel s st).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveSeedTail at h
  dsimp only at h
  split at h
  · rename_i hempty
    exact entailed_nil_unsat (emptyConflict_entailed hempty)
  · split at h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_unsat p _ _ _ _ _ _ _ _ h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_unsat p _ _ _ _ _ _ _ _ h
    · split at h
      · simp [coreSolveSeedFinish_fst] at h
      · split at h
        · simp [coreSolveSeedFinish_fst] at h
        · split at h
          · rename_i hok x lc hlearned hemp
            exact entailed_nil_unsat
              (analyze_empty_unsat (by simpa using hok) hlearned
                (by simpa using hemp))
          · simp [coreSolveSeedFinish_fst] at h

/-- Every `.sat` result of the seeded entry is a box member accepted by the
problem. -/
theorem coreSolveSeed_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p} {a : List Value}
    (h : (coreSolveSeed p o fuel s).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveSeed at h
  split at h
  · simp at h
  · split at h
    · exact coreSolveSeedTail_sat h
    · split at h
      · simp at h
      · exact coreSolveSeedTail_sat h

/-- Every `.unsat` result of the seeded entry excludes every accepted
assignment. -/
theorem coreSolveSeed_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p}
    (h : (coreSolveSeed p o fuel s).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveSeed at h
  split at h
  · simp at h
  · split at h
    · exact coreSolveSeedTail_unsat h
    · split at h
      · rename_i hseed
        exact entailed_nil_unsat (addSeedClauses_empty_entailed hseed)
      · exact coreSolveSeedTail_unsat h

end LeanFzn.Engine
