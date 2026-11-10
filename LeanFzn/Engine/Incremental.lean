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

/-! ## Invariant transport for retyping and rebasing -/

/-- Pointwise slot lookup after `retype`. -/
theorem ClauseDB.retype_clauses_getElem? {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) (id : Nat) :
    (db.retype (T' := T')).clauses[id]? =
      (db.clauses[id]?).map (fun sc : StoredClause p T =>
        { e := { lits := sc.e.lits, ent := sc.e.ent }
          w1 := sc.w1
          w2 := sc.w2
          deleted := sc.deleted
          lbd := sc.lbd }) := by
  simp [ClauseDB.retype]

/-- `retype` preserves the structural clause-database invariant. -/
theorem ClauseDB.retype_inv {p : CompiledProblem DomConstraint}
    {T T' : LitTable} (db : ClauseDB p T) (h : db.Inv) :
    (db.retype (T' := T')).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi id hid
    have hi' : db.watch[i]? = some ids := by simpa [ClauseDB.retype] using hi
    have hlt := h.watch_lt i ids hi' id hid
    simpa [ClauseDB.retype] using hlt
  · intro id sc hget hdel hsize
    rw [ClauseDB.retype_clauses_getElem?] at hget
    cases h0 : db.clauses[id]? with
    | none => rw [h0] at hget; simp at hget
    | some sc0 =>
        rw [h0, Option.map_some] at hget
        have hsc := Option.some.inj hget
        subst hsc
        have hdel0 : sc0.deleted = false := by simpa using hdel
        have hsz0 : 2 ≤ sc0.e.lits.size := by simpa using hsize
        simpa using h.pos_lt id sc0 h0 hdel0 hsz0
  · intro id sc hget hdel hsize
    rw [ClauseDB.retype_clauses_getElem?] at hget
    cases h0 : db.clauses[id]? with
    | none => rw [h0] at hget; simp at hget
    | some sc0 =>
        rw [h0, Option.map_some] at hget
        have hsc := Option.some.inj hget
        subst hsc
        have hdel0 : sc0.deleted = false := by simpa using hdel
        have hsz0 : 2 ≤ sc0.e.lits.size := by simpa using hsize
        simpa [ClauseDB.WatchedBy, ClauseDB.WatchesAt, ClauseDB.watchList]
          using h.watches id sc0 h0 hdel0 hsz0
  · simpa [ClauseDB.retype, ClauseDB.liveCount, ClauseDB.deletedCount,
      Function.comp_def] using h.live_eq
  · intro id hid
    obtain ⟨sc, hget, hdel⟩ := h.free_deleted id hid
    refine ⟨{ e := { lits := sc.e.lits, ent := sc.e.ent }
              w1 := sc.w1, w2 := sc.w2, deleted := sc.deleted,
              lbd := sc.lbd }, ?_, ?_⟩
    · rw [ClauseDB.retype_clauses_getElem?, hget]
      rfl
    · simpa using hdel
  · simpa [ClauseDB.retype] using h.free_nodup

/-- `retype` preserves literal well-formedness. -/
theorem ClauseDB.LitsWF.retype {p : CompiledProblem DomConstraint}
    {S : LitTable} {T T' : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) : (db.retype (T' := T')).LitsWF S := by
  intro id sc hget l hl
  rw [ClauseDB.retype_clauses_getElem?] at hget
  cases h0 : db.clauses[id]? with
  | none => rw [h0] at hget; simp at hget
  | some sc0 =>
      rw [h0, Option.map_some] at hget
      have hsc := Option.some.inj hget
      subst hsc
      exact h id sc0 h0 l (by simpa using hl)

/-- Pointwise slot lookup after `rebase`. -/
theorem ClauseDB.rebase_clauses_getElem? {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) (id : Nat) :
    (db.rebase hdoms hacc).clauses[id]? =
      (db.clauses[id]?).map (fun sc : StoredClause p T =>
        { e := { lits := sc.e.lits, ent := Entailed_mono hdoms hacc sc.e.ent }
          w1 := sc.w1
          w2 := sc.w2
          deleted := sc.deleted
          lbd := sc.lbd }) := by
  simp [ClauseDB.rebase]

/-- `rebase` preserves the structural clause-database invariant: only the
erased entailment proofs change. -/
theorem ClauseDB.rebase_inv {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (db : ClauseDB p T) (h : db.Inv) :
    (db.rebase hdoms hacc).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi id hid
    have hi' : db.watch[i]? = some ids := by simpa [ClauseDB.rebase] using hi
    have hlt := h.watch_lt i ids hi' id hid
    simpa [ClauseDB.rebase] using hlt
  · intro id sc hget hdel hsize
    rw [ClauseDB.rebase_clauses_getElem?] at hget
    cases h0 : db.clauses[id]? with
    | none => rw [h0] at hget; simp at hget
    | some sc0 =>
        rw [h0, Option.map_some] at hget
        have hsc := Option.some.inj hget
        subst hsc
        have hdel0 : sc0.deleted = false := by simpa using hdel
        have hsz0 : 2 ≤ sc0.e.lits.size := by simpa using hsize
        simpa using h.pos_lt id sc0 h0 hdel0 hsz0
  · intro id sc hget hdel hsize
    rw [ClauseDB.rebase_clauses_getElem?] at hget
    cases h0 : db.clauses[id]? with
    | none => rw [h0] at hget; simp at hget
    | some sc0 =>
        rw [h0, Option.map_some] at hget
        have hsc := Option.some.inj hget
        subst hsc
        have hdel0 : sc0.deleted = false := by simpa using hdel
        have hsz0 : 2 ≤ sc0.e.lits.size := by simpa using hsize
        simpa [ClauseDB.WatchedBy, ClauseDB.WatchesAt, ClauseDB.watchList]
          using h.watches id sc0 h0 hdel0 hsz0
  · simpa [ClauseDB.rebase, ClauseDB.liveCount, ClauseDB.deletedCount,
      Function.comp_def] using h.live_eq
  · intro id hid
    obtain ⟨sc, hget, hdel⟩ := h.free_deleted id hid
    refine ⟨{ e := { lits := sc.e.lits, ent := Entailed_mono hdoms hacc sc.e.ent }
              w1 := sc.w1, w2 := sc.w2, deleted := sc.deleted,
              lbd := sc.lbd }, ?_, ?_⟩
    · rw [ClauseDB.rebase_clauses_getElem?, hget]
      rfl
    · simpa using hdel
  · simpa [ClauseDB.rebase] using h.free_nodup

/-- `rebase` preserves literal well-formedness. -/
theorem ClauseDB.LitsWF.rebase {p q : CompiledProblem DomConstraint}
    {T : LitTable} (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    {S : LitTable} {db : ClauseDB p T} (h : db.LitsWF S) :
    (db.rebase hdoms hacc).LitsWF S := by
  intro id sc hget l hl
  rw [ClauseDB.rebase_clauses_getElem?] at hget
  cases h0 : db.clauses[id]? with
  | none => rw [h0] at hget; simp at hget
  | some sc0 =>
      rw [h0, Option.map_some] at hget
      have hsc := Option.some.inj hget
      subst hsc
      exact h id sc0 h0 l (by simpa using hl)

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
  /-- Proof-only: the carried table is well formed.  Used to rebuild the
  root invariant of the seeded entry. -/
  table_inv : T.Inv
  /-- Proof-only: the carried clause database satisfies its structural
  invariant. -/
  db_inv : db.Inv
  /-- Proof-only: every carried clause literal is interned in `T`. -/
  lits_wf : db.LitsWF T

namespace CoreSeed

/-- The first round's seed: empty database, empty table, unseeded. -/
def initial (p : CompiledProblem DomConstraint) : CoreSeed p :=
  { T := {}, db := {}, seeded := false
    table_inv := LitTable.inv_empty
    db_inv := ClauseDB.inv_empty
    lits_wf := by
      intro id sc hget l hl
      simp [ClauseDB.empty] at hget }

/-- Transport a seed to a stronger problem with the same box. -/
def rebase {p q : CompiledProblem DomConstraint}
    (hdoms : q.domains = p.domains)
    (hacc : ∀ b, accepts q b = true → accepts p b = true)
    (s : CoreSeed p) : CoreSeed q :=
  { T := s.T, db := s.db.rebase hdoms hacc, seeded := s.seeded
    table_inv := s.table_inv
    db_inv := ClauseDB.rebase_inv hdoms hacc s.db s.db_inv
    lits_wf := ClauseDB.LitsWF.rebase hdoms hacc s.lits_wf }

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
database from the entry's table parameter to the grown `st.table`.  The three
proof arguments are the terminal state's root-invariant projections. -/
def coreSolveSeedFinish {p : CompiledProblem DomConstraint} {T : LitTable}
    (st : EngineState p T) (r : CoreResult) (hT : st.table.Inv)
    (hdb : st.db.Inv) (hlits : st.db.LitsWF st.table) :
    CoreResult × EngineStats × CoreSeed p :=
  (r, st.stats, { T := st.table, db := st.db.retype, seeded := true
                  table_inv := hT
                  db_inv := ClauseDB.retype_inv st.db hdb
                  lits_wf := ClauseDB.LitsWF.retype hlits })

/-- The verdict component of a finished seeded solve. -/
@[simp] theorem coreSolveSeedFinish_fst {p : CompiledProblem DomConstraint}
    {T : LitTable} (st : EngineState p T) (r : CoreResult) (hT : st.table.Inv)
    (hdb : st.db.Inv) (hlits : st.db.LitsWF st.table) :
    (coreSolveSeedFinish st r hT hdb hlits).1 = r := rfl

/-- The common tail of the seeded entry: empty-clause check, root unit
propagation, and the CDCL loop.  This is the exact tail of `coreSolveFull`
with the state threaded back out.  `RootInv`/`PropsSound` are proof-only. -/
def coreSolveSeedTail (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (fuel : Nat) (s : CoreSeed p) (st : EngineState p s.T)
    (hroot : RootInv p s.T st.doms st)
    (hprops : PropsSound p s.T st.props) :
    CoreResult × EngineStats × CoreSeed p :=
  let prio := annotPrioArray p
  let orders := configOrders p o
  match st.db.emptyConflict? with
  | some _ =>
      coreSolveSeedFinish st .unsat hroot.table_inv hroot.db_inv hroot.lits_wf
  | none =>
      let pu := st.db.propagateUnits p s.T st.doms
      let st2 : EngineState p s.T := { st with db := pu.1 }
      have hroot2 : RootInv p s.T st2.doms st2 := by
        simpa only [st2, pu] using propagateUnits_rootInv hroot
      have hprops2 : PropsSound p s.T st2.props := hprops
      match hout : pu.2 with
      | .none =>
          let hp : PendingRoot p st2 #[] := by
            intro h0 item hit
            simp at hit
          let out := search p s.T st.doms o prio orders st2 #[] hroot2 hp hprops2 fuel
          coreSolveSeedFinish out.res.2 out.res.1 out.hroot.table_inv out.hroot.db_inv
            out.hroot.lits_wf
      | .prune ps =>
          have hp : PendingRoot p st2 (pushClausePrunes #[] ps) :=
            pushClausePrunes_pendingRoot_of_entailed
              (by intro h0 item hit; simp at hit)
              (fun h0 q id hq =>
                ClauseDB.propagateUnits_prunes_entailed st.db st.doms hout q id hq)
          let out := search p s.T st.doms o prio orders st2
            (pushClausePrunes #[] ps) hroot2 hp hprops2 fuel
          coreSolveSeedFinish out.res.2 out.res.1 out.hroot.table_inv out.hroot.db_inv
            out.hroot.lits_wf
      | .conflict ec _ =>
          let a := analyze p s.T st.doms st hroot.conv hroot.hist.1 hroot ec fuel
          if !a.ok then
            coreSolveSeedFinish st2 .gaveUp hroot2.table_inv hroot2.db_inv hroot2.lits_wf
          else
            match a.learned with
            | none =>
                coreSolveSeedFinish st2 .gaveUp hroot2.table_inv hroot2.db_inv
                  hroot2.lits_wf
            | some lc =>
                if lc.lits.isEmpty then
                  coreSolveSeedFinish st2 .unsat hroot2.table_inv hroot2.db_inv
                    hroot2.lits_wf
                else
                  coreSolveSeedFinish st2 .gaveUp hroot2.table_inv hroot2.db_inv
                    hroot2.lits_wf

/-- The seeded entry.  It mirrors `coreSolveFullWith`: the saved phases are
seeded from the previous round's incumbent, the carried literal table is used
instead of the empty table and, when `s.seeded = true`, the carried database
replaces the freshly initialised one (it already contains the problem's seed
clauses).  The returned seed carries the terminal table and database for the
next objective-bound round. -/
def coreSolveSeed (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) (s : CoreSeed p) :
    CoreResult × EngineStats × CoreSeed p :=
  match hinit : initState p s.T with
  | none => (.gaveUp, { gaveUp := 1 }, s)
  | some st0 =>
      let stSeed := seedPhases st0 prev
      have hroot0 : RootInv p s.T st0.doms st0 :=
        initState_rootInv hinit s.table_inv
      have hrootSeed : RootInv p s.T stSeed.doms stSeed :=
        (seedPhases_rootInv hroot0 prev).init_congr (seedPhases_doms st0 prev)
      have hprops0 : PropsSound p s.T stSeed.props :=
        (initState_propsSound hinit).congr (seedPhases_props st0 prev)
      have hstT : stSeed.table = s.T := by
        rw [seedPhases_table]
        exact initState_table hinit
      if s.seeded then
        have hlits : ClauseDB.LitsWF stSeed.table s.db := by
          rw [hstT]
          exact s.lits_wf
        have hrootDb : RootInv p s.T stSeed.doms { stSeed with db := s.db } :=
          dbUpdate_rootInv hrootSeed s.db s.db_inv hlits
        coreSolveSeedTail p o fuel s { stSeed with db := s.db } hrootDb hprops0
      else
        match hseed : addSeedClauses p s.T stSeed with
        | (st, some _) =>
            -- An entailed empty seed clause is a root refutation.
            have hst : st = (addSeedClauses p s.T stSeed).1 := by rw [hseed]
            have hroot1 : RootInv p s.T st.doms st := by
              rw [hst]
              exact (addSeedClauses_fst_rootInv hrootSeed).init_congr
                (addSeedClauses_fst_doms p s.T stSeed)
            let st := { st with
              stats := { st.stats with conflicts := st.stats.conflicts + 1 } }
            (.unsat, st.stats,
              { T := st.table, db := st.db.retype, seeded := true
                table_inv := hroot1.table_inv
                db_inv := ClauseDB.retype_inv st.db hroot1.db_inv
                lits_wf := ClauseDB.LitsWF.retype hroot1.lits_wf })
        | (st, none) =>
            have hst : st = (addSeedClauses p s.T stSeed).1 := by rw [hseed]
            have hroot1 : RootInv p s.T st.doms st := by
              rw [hst]
              exact (addSeedClauses_fst_rootInv hrootSeed).init_congr
                (addSeedClauses_fst_doms p s.T stSeed)
            have hprops1 : PropsSound p s.T st.props := by
              rw [hst]
              exact hprops0.congr (addSeedClauses_fst_props p s.T stSeed)
            coreSolveSeedTail p o fuel s st hroot1 hprops1

theorem coreSolveSeedTail_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p}
    {st : EngineState p s.T}
    {hroot : RootInv p s.T st.doms st}
    {hprops : PropsSound p s.T st.props} {a : List Value}
    (h : (coreSolveSeedTail p o fuel s st hroot hprops).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveSeedTail at h
  dsimp only at h
  split at h
  · simp [coreSolveSeedFinish_fst] at h
  · split at h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_sat p s.T st.doms o _ _ _ _ _ _ _ _ _ h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_sat p s.T st.doms o _ _ _ _ _ _ _ _ _ h
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
    {hroot : RootInv p s.T st.doms st}
    {hprops : PropsSound p s.T st.props}
    (h : (coreSolveSeedTail p o fuel s st hroot hprops).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveSeedTail at h
  dsimp only at h
  split at h
  · rename_i hempty
    exact entailed_nil_unsat (emptyConflict_entailed hempty)
  · split at h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_unsat p s.T st.doms o _ _ _ _ _ _ _ _ h
    · simp only [coreSolveSeedFinish_fst] at h
      exact search_unsat p s.T st.doms o _ _ _ _ _ _ _ _ h
    · split at h
      · simp [coreSolveSeedFinish_fst] at h
      · split at h
        · simp [coreSolveSeedFinish_fst] at h
        · split at h
          · rename_i hok x lc hlearned hemp
            exact entailed_nil_unsat
              (analyze_empty_unsat hroot.conv hroot.hist.1 hroot
                (by simpa using hok) hlearned (by simpa using hemp))
          · simp [coreSolveSeedFinish_fst] at h

/-- Every `.sat` result of the seeded entry is a box member accepted by the
problem. -/
theorem coreSolveSeed_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {fuel : Nat} {s : CoreSeed p} {a : List Value}
    {prev : Option (List Value)}
    (h : (coreSolveSeed p o prev fuel s).1 = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveSeed at h
  dsimp only at h
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
    {prev : Option (List Value)}
    (h : (coreSolveSeed p o prev fuel s).1 = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveSeed at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · exact coreSolveSeedTail_unsat h
    · split at h
      · rename_i hseed
        exact entailed_nil_unsat (addSeedClauses_empty_entailed hseed)
      · exact coreSolveSeedTail_unsat h

end LeanFzn.Engine
