/-
File: LeanFzn/Engine/Types.lean

Purpose:
  The frozen vocabulary of Core, the array-based, mutable, event-driven
  LCG engine.  This module contains only types and total, proof-free
  definitions (the N0 design freeze).  All soundness statements live in
  the later `LeanFzn.Engine.*` modules and are stated against `EClause`.

Architecture: see code-structure.md; actual types and imports are authoritative.

Dependencies:
  - LeanFzn.Compiler.Compile: `CompiledProblem`, `DomConstraint`,
    `accepts`.
  - LeanFzn.Solver.Core.Enumerate: `allAssigns`.
  - LeanFzn.Solver.Propagation.Operations: `Literal`, `Clause`,
    `Clause.SatisfiedBy`.

DAG:
  LeanFzn.Compiler.* -> LeanFzn.Engine.Types ->
  LeanFzn.Engine.{Lit,Dom,Trail,Clauses,Prop,Queue,Analyze,Search}
-/

import LeanFzn.Compiler.Compile
import LeanFzn.Solver.Core.Enumerate
import LeanFzn.Solver.Propagation.Operations
import Std.Data.HashMap.Lemmas

open LeanFzn
open LeanFzn.Compiler
open LeanFzn.Semantics
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Packed literals and the literal table -/

/-- A packed literal.

`idx` is the dense index used by watched-literal lists; `lit` is the
literal it denotes.  Carrying the denotation on the pack makes
`EClause` stable under append-only growth of the intern table: a clause
built when the table had `n` entries keeps its meaning after more
literals are interned.  `LitTable.WF` records the runtime tie between
`idx` and `lit`; it is a representation invariant, not a soundness
obligation (the proof is about `lit`). -/
structure PLit where
  idx : Nat
  lit : Literal
  deriving Repr, DecidableEq, BEq, Hashable

/-- The decoding carried by a packed literal. -/
def PLit.decode (l : PLit) : Literal := l.lit

/-- Per-problem literal intern table.  `lits[i]` is the literal assigned
index `i`; `lookup` is the deduplication cache used by `intern` (N2).
The table is append-only: existing indices never change meaning. -/
structure LitTable where
  lits : Array Literal := #[]
  lookup : Std.HashMap Literal Nat := ∅
  /-- Negation-index cache (D3): `neg[i] = j + 1` records that literal index
  `j` carries the negation of literal index `i`; `0` means "not cached yet".
  Every fresh literal pushes a `0`, so `neg.size = lits.size`.  The cache is
  filled by `internNeg` (called from `insertPending`) and is only a lookup
  hint: `lits` and `lookup` remain authoritative. -/
  neg : Array Nat := #[]

/-- The literal denoted by a packed literal.  Decoding reads the
denotation carried by `PLit` (see the `PLit` docstring), so this is
independent of the current table contents; the `LitTable` argument is
kept in the frozen signature and documents the intern context. -/
def LitTable.decode (_T : LitTable) (l : PLit) : Literal := l.lit

/-- Decode a packed clause. -/
def LitTable.decodeClause (T : LitTable) (lits : Array PLit) : Clause :=
  lits.toList.map (T.decode ·)

/-- Runtime well-formedness of a packed literal in a table. -/
def LitTable.WF (T : LitTable) (l : PLit) : Prop :=
  T.lits[l.idx]? = some l.lit

/-! ## Domains -/

/-- Compact domain representation used by Core.

* `bool bits`: bit 0 denotes `.bool false`, bit 1 `.bool true`; `bits = 0`
  is the empty domain.
* `bounds lo hi`: the integer interval `[lo, hi]`; empty when `hi < lo`.
* `bitset lo words`: little-endian words, bit `64*w + k` of `words[w]`
  denotes `.int (lo + 64*w + k)`; no set bit means empty.
* `boundsHoles lo hi holes`: `[lo, hi]` minus the sorted, strictly
  increasing holes (all inside the interval).
* `sparse values`: the sorted, strictly increasing listed integers.  This
  represents wide sparse enumerations without allocating storage
  proportional to their span.

N3 owns the operations and the denotation lemma against the compiled
`Dom`; this module freezes only the representation. -/
inductive DomC where
  | bool (bits : UInt8)
  | bounds (lo hi : Int)
  | bitset (lo : Int) (words : Array UInt64)
  | boundsHoles (lo hi : Int) (holes : Array Int)
  | sparse (values : Array Int)
  deriving Repr, DecidableEq, BEq, Inhabited

/-! ## Trail -/

/-- Where the explanation of a trail entry lives.

* `decision`: the entry is a decision literal.
* `learned id`: the reason is clause slot `id` of the `ClauseDB`.
* `reason id`: the reason is entry `id` of the transient reason store
  (`EngineState.reasons`), used by propagator explanations.

Every non-decision reason resolves to an `EClause`, so the entailment
invariant covers decisions' successors uniformly. -/
inductive ReasonRef where
  | decision
  | learned (id : Nat)
  | reason (id : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One undo-trail entry: the literal that was set, the decision level,
its explanation, the slot it changed, and the previous domain (the undo
image; no soundness obligation). -/
structure Entry where
  lit : PLit
  level : Nat
  reason : ReasonRef
  slot : Slot
  prev : DomC
  deriving Repr

/-! ## Events and propagators -/

/-- Domain-change event kinds.  A propagator subscribes to one or more
`(slot, kind)` pairs.  The order is the flattening order used by
`EngineState.subs` (`slot * 3 + EventKind.toNat`). -/
inductive EventKind where
  | fix
  | bounds
  | domain
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Flattening index of an event kind. -/
def EventKind.toNat : EventKind → Nat
  | .fix => 0
  | .bounds => 1
  | .domain => 2

/-- Stable propagator identifier (an index into `EngineState.props`). -/
abbrev PropId := Nat

/-- The read-only view a propagator gets: current domains and decision
level.  Domain access is `Array.getD`, O(1); the view is a snapshot value
and cannot mutate the engine. -/
structure EngineView where
  doms : Array DomC
  level : Nat

/-! ## Entailment and proof-carrying clauses -/

/-- A clause is entailed by a compiled problem when every accepted
assignment in the problem's box satisfies it.  This is the single
soundness notion of Core. -/
def Entailed (p : CompiledProblem DomConstraint) (c : Clause) : Prop :=
  ∀ b ∈ allAssigns p.domains, accepts p b = true → c.SatisfiedBy b

/-- A runtime clause.  `lits` is the packed clause used by watches and
propagation; `ent` proves that its decoding is entailed by the problem.
The proof field is erased at runtime.  This is the only structure that
carries a soundness obligation. -/
structure EClause (p : CompiledProblem DomConstraint) (T : LitTable) where
  lits : Array PLit
  ent : Entailed p (T.decodeClause lits)

/-- Result of running one propagator. -/
inductive PropOut (p : CompiledProblem DomConstraint) (T : LitTable) where
  /-- No domain change. -/
  | fix
  /-- A batch of literal prunings, each with its entailed reason. -/
  | prune (ps : Array (PLit × EClause p T))
  /-- An entailed conflict clause. -/
  | conflict (c : EClause p T)

/-- Propagator interface v2.  `vars` lists the slots read by `run`;
`events` lists the `(slot, kind)` subscriptions.  `run` reads domains via
the `EngineView` only. -/
structure PropV2 (p : CompiledProblem DomConstraint) (T : LitTable) where
  vars : Array Slot
  events : Array (Slot × EventKind)
  run : EngineView → PropOut p T

/-! ## Clauses, database and watches -/

/-- One stored clause plus its two watched positions.  `deleted` marks a
lazily deleted slot reusable by the free list. -/
structure StoredClause (p : CompiledProblem DomConstraint) (T : LitTable) where
  e : EClause p T
  w1 : Nat
  w2 : Nat
  deleted : Bool := false
  /-- Literal-block distance of a learned clause: the number of distinct
  decision levels among its literals at learning time.  Original and seed
  clauses carry `0`.  N13 uses it only to choose deletion candidates; no
  soundness argument reads it. -/
  lbd : Nat := 0
  /-- Set when the clause propagates or conflicts, i.e. when it participates
  in conflict analysis.  Reduction protects recently used clauses for one
  interval and clears the flag after each pass.  Policy data only. -/
  used : Bool := false

/-- Two-watched-literal clause database.

`clauses` is the slot array (holes are `deleted`); `watch[i]` is the list
of clause ids currently watching packed literal index `i`; `free` lists
reusable deleted slots; `live` is the number of non-deleted clauses.
Watch preservation is proved in Engine.Clauses. -/
structure ClauseDB (p : CompiledProblem DomConstraint) (T : LitTable) where
  clauses : Array (StoredClause p T) := #[]
  watch : Array (Array Nat) := #[]
  free : Array Nat := #[]
  live : Nat := 0

/-- Every literal of every stored clause is well-formed in the live intern
table.  Representation invariant used by the root clause-prune contract: the
watch index of a clause literal identifies its denotation.  It is proof-only;
no executable code reads it. -/
def ClauseDB.LitsWF (S : LitTable) (db : ClauseDB p T) : Prop :=
  ∀ (id : Nat) (sc : StoredClause p T), db.clauses[id]? = some sc →
    ∀ l ∈ sc.e.lits.toList, S.WF l

/-! ## Engine state and counters -/

/-- `--stats` counters.  `wall` is measured by the driver, not stored
here.  `propagations` counts applied literal prunings (unit clause
propagations included), matching the kernel's per-implied-literal
counter. -/
structure EngineStats where
  decisions : Nat := 0
  propagations : Nat := 0
  conflicts : Nat := 0
  /-- Deepest decision level reached.  Diagnostic policy/statistics only;
  no verdict or soundness proof reads it. -/
  maxLevel : Nat := 0
  learned : Nat := 0
  gaveUp : Nat := 0
  /-- Diagnostic cause of the first give-up.  This is a policy/statistics
  field only: no decision or theorem reads it. -/
  gaveUpCause : String := ""
  /-- Diagnostic totals for learned-clause minimization: the size of the
  item clause before minimization and the size of the stored clause after.
  Policy/statistics only; no soundness argument reads them. -/
  learnedLitsBefore : Nat := 0
  learnedLitsAfter : Nat := 0
  learnedUnits : Nat := 0
  /-- Number of clause-database reduction runs.  Diagnostic policy data. -/
  reductions : Nat := 0
  /-- Live clauses retired by reduction.  Diagnostic policy data. -/
  reducedClauses : Nat := 0
  /-- Transient reason slots reclaimed by suffix trimming.  Diagnostic
  policy data; no verdict reads it. -/
  reasonsTrimmed : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Add the counters of two engine runs.  The first nonempty give-up cause is
kept: this is a diagnostic policy field only, never a verdict input. -/
def EngineStats.add (a b : EngineStats) : EngineStats :=
  { decisions := a.decisions + b.decisions
    propagations := a.propagations + b.propagations
    conflicts := a.conflicts + b.conflicts
    maxLevel := max a.maxLevel b.maxLevel
    learned := a.learned + b.learned
    gaveUp := a.gaveUp + b.gaveUp
    gaveUpCause := if a.gaveUpCause.isEmpty then b.gaveUpCause else a.gaveUpCause
    learnedLitsBefore := a.learnedLitsBefore + b.learnedLitsBefore
    learnedLitsAfter := a.learnedLitsAfter + b.learnedLitsAfter
    learnedUnits := a.learnedUnits + b.learnedUnits
    reductions := a.reductions + b.reductions
    reducedClauses := a.reducedClauses + b.reducedClauses
    reasonsTrimmed := a.reasonsTrimmed + b.reasonsTrimmed }

/-- The complete mutable engine state.  `p` and `T` are fixed for the
lifetime of a `coreSolve` call; `table` is the live append-only intern
table.  The state is threaded linearly: no operation copies `doms` or
`trail`. -/
structure EngineState (p : CompiledProblem DomConstraint) (T : LitTable) where
  /-- Live append-only literal intern table. -/
  table : LitTable
  /-- Current domain of every slot. -/
  doms : Array DomC
  /-- Undo trail, oldest first. -/
  trail : Array Entry
  /-- `levelStart[k]` is the first trail index of decision level `k`. -/
  levelStart : Array Nat
  /-- Current decision level. -/
  level : Nat
  /-- Per-slot trail positions of domain changes (oldest first). -/
  changeIndex : Array (Array Nat)
  /-- Watched clause database. -/
  db : ClauseDB p T
  /-- Transient propagator reasons (append-only between restarts). -/
  reasons : Array (EClause p T)
  /-- Cached per-level reason bound.  `reasonCap[k]` is the largest `.reason`
  id (plus one) named by trail entries through level `k`, so the current bound
  is `reasonCap[level]` instead of a whole-trail fold.  The empty array means
  "no cache": `reasonBound` then falls back to the fold, which keeps test and
  other hand-built states correct.  Runtime states maintain the cache through
  `trailPush`, `newLevel` and `backjump`; `TrailInv.reasonCap_exact` records
  the agreement with the fold. -/
  reasonCap : Array Nat := #[]
  /-- Registered propagators. -/
  props : Array (PropV2 p T)
  /-- Subscription lists indexed by `slot * 3 + EventKind.toNat`. -/
  subs : Array (Array PropId)
  /-- Pending high-priority propagator ids (clauses and binary). -/
  queueHigh : Array PropId
  /-- Pending low-priority propagator ids (global constraints). -/
  queueLow : Array PropId
  /-- `inQueue[p] = 0` absent, `1` high priority, `2` low priority. -/
  inQueue : ByteArray
  /-- VSIDS-style activity per slot, stored unboxed in a `FloatArray`. -/
  activity : FloatArray
  /-- Current bump increment.  The increment grows geometrically instead of
  decaying every stored score; `1 / activityDecay` per analysed conflict. -/
  activityInc : Float := 1.0
  /-- Activity max-heap of slot indices. -/
  activityHeap : Array Slot
  /-- Saved phase per slot. -/
  phases : Array Value
  /-- Restart counter. -/
  restarts : Nat
  /-- Value of `stats.conflicts` at the last restart.  Restart scheduling
  compares the conflicts since this point with the next sequence term. -/
  lastRestartConflict : Nat := 0
  /-- Next `stats.learned` count at which N13 clause-database reduction
  runs; the schedule doubles it after each reduction. -/
  nextReduce : Nat := 2000
  /-- Conflict-weighted degree per slot (P5.2).  A policy score only: it is
  read by `selectSlot` under `--var=wdeg` and never feeds a verdict.  It is
  initialised to `doms.size` zeroes and grows only through conflict
  explanations; it is not trailed, so a backjump keeps the guidance. -/
  slotWeight : Array Nat := #[]
  /-- Counters. -/
  stats : EngineStats

/-! ## Verdicts -/

/-- Core's verdict. `gaveUp` makes no claim; the public API reports unknown
or incomplete optimization without a fallback. -/
inductive CoreResult where
  | sat (a : List Value)
  | unsat
  | gaveUp
  deriving Repr

end LeanFzn.Engine
