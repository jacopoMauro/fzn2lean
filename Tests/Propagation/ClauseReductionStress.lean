/-
File: Tests/Propagation/ClauseReductionStress.lean

Purpose (PLAN.md §7 L1 acceptance, "deletion/relearn stress tests"):

  A PURE, self-contained stress driver for the certified deletion policy
  of `LeanFzn/Solver/Propagation/ClauseReduction.lean`. No runtime state
  is touched; the driver generates interleavings of

    * history-novel pool insertions (the L0 §5.4 re-keyed guard),
    * eligible deletions, including the refused re-insertion of a
      deleted — still certified — clause (the relearning path),
    * deterministic batch reductions (`reduce`),

  with a small LCG, and checks after EVERY step:

    - every active clause stays in the certificate (`ActiveInHistory`)
      and every live reason stays active (`LockedReasons`);
    - flow conservation `activeLength + deletes = inserts + initial`;
    - the countdown never increases, strictly decreases on each admitted
      insertion, and the active length strictly decreases on each
      deletion/reduction that drops a clause (the §7 payments);
    - after a reduction no eligible clause remains (`reduce_no_eligible`);
    - admitted insertions never exceed the pool size.

  The computable invariant mirrors `activeInHistoryB`/`lockedB` are tied
  to the formal lifecycle predicates by proved `iff` lemmas
  (`activeInHistoryB_iff`, `lockedB_iff`), so the driver checks the
  formal invariants rather than a re-implementation. The long run uses
  `#guard` (evaluated at elaboration, silent on success); a short
  12-step prefix is additionally proved `ok` in the kernel
  (`by decide`), so the driver itself is checked, not only evaluated.

  Why a model and not the wired runtime: the seven wiring prerequisites
  of `ClauseReduction.lean` (history-keyed guards, pool membership,
  watch reset-on-delete, coverage instantiation, next-bound transport,
  `SchedulerConfig.history`/`lifecycle` fields, six-tuple rank instance)
  require editing the scheduler modules, which is out of this task's
  file ownership. The driver exercises the policy and the progress
  payments on generated sequences here; the wired acceptance run
  (Gperf, bounded memory) waits for that integration.
-/

import LeanFzn.Legacy.Solver.Propagation.ClauseReduction

set_option autoImplicit false

namespace Tests.Propagation.ClauseReductionStress

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.ClauseLifecycle
open LeanFzn.Solver.Propagation.ClauseLifecycle.Lifecycle
open LeanFzn.Solver.Propagation.ClauseReduction

/-! ## §1 The tiny clause universe -/

def lit (s : Nat) (b : Bool) : Literal := { atom := .boolEq s b, positive := true }

def c0 : Clause := [lit 0 true]
def c1 : Clause := [lit 1 true]
def c2 : Clause := [lit 0 true, lit 1 true]
def c3 : Clause := [lit 2 true]
def c4 : Clause := [lit 0 true, lit 2 true]
def c5 : Clause := [lit 1 true, lit 2 true]
def c6 : Clause := [lit 3 true, lit 4 true]
def c7 : Clause := [lit 4 true, lit 6 true]
def c8 : Clause := [lit 5 true, lit 6 true]

/-- The fixed pool; with the identity projection the membership test is
exact. `c2`, `c5`, `c7`, `c8` are the only deletable members. -/
def pool : List Clause := [c0, c1, c2, c3, c4, c5, c6, c7, c8]

/-- A live reason locking `c4` against every deletion. -/
def trail : List TrailEntry :=
  [{ literal := lit 9 true, level := 0, reason := some { clause := c4 } }]

/-- The conservative policy on this universe: `c0` kept, `c6` a retained
witness, `c4` a live reason, `c0`/`c1`/`c3` normalized units; only `c2`,
`c5`, `c7`, `c8` are eligible. -/
def P : Policy :=
  { f := fun c => c, pool := pool, keep := [c0], witnesses := [c6] }

/-- The full lifecycle the concrete instances below quantify over (all
clauses except the pool-only witness `c6`). -/
def fullLc : Lifecycle := replay [c0, c1, c2, c3, c4, c5] empty

/-! ## §2 Computable invariant mirrors (tied to the formal predicates) -/

def activeInHistoryB (lc : Lifecycle) : Bool :=
  lc.active.all lc.history.contains

def lockedB (tr : List TrailEntry) (lc : Lifecycle) : Bool :=
  (liveReasons tr).all lc.active.contains

/-- Computable canonical-presence test (the driver's history guard). -/
def canonSeenB (f : Clause → Clause) (lc : Lifecycle) (c : Clause) : Bool :=
  (lc.history.map f).contains (f c)

theorem activeInHistoryB_iff (lc : Lifecycle) :
    activeInHistoryB lc = true ↔ ActiveInHistory lc := by
  simp [activeInHistoryB, ActiveInHistory, List.all_eq_true]

theorem lockedB_iff (tr : List TrailEntry) (lc : Lifecycle) :
    lockedB tr lc = true ↔ LockedReasons lc tr := by
  simp [lockedB, LockedReasons, List.all_eq_true]

theorem canonSeenB_iff (f : Clause → Clause) (lc : Lifecycle) (c : Clause) :
    canonSeenB f lc c = true ↔ CanonSeenWith f lc c := by
  simp [canonSeenB, CanonSeenWith]

/-! ## §3 The driver -/

/-- A small LCG (mod 2^31, positive). -/
def next (n : Nat) : Nat :=
  (n * 1103515245 + 12345) % 2147483648

structure DState where
  lc : Lifecycle
  seed : Nat
  inserts : Nat
  deletes : Nat
  fallbacks : Nat
  reduces : Nat
  /-- clauses this driver ever deleted (single deletion or reduction
  drop); a refused re-insertion of one of them is the relearning path -/
  deleted : List Clause
  /-- fallbacks whose clause had been deleted earlier (the
  delete-then-relearn interleavings) -/
  relearns : Nat
  ok : Bool

/-- The initially replayed clauses: `c4` is the live reason and must be
active for `LockedReasons` to hold from the start; the pool stays larger
so the insert path keeps firing. -/
def ops : List Clause := [c0, c1, c4]

def initState : DState :=
  { lc := replay ops empty,
    seed := 20251018, inserts := 0, deletes := 0, fallbacks := 0,
    reduces := 0, deleted := [], relearns := 0, ok := true }

/-- The initial active length (the replay is outside the counter flow). -/
def initialActive : Nat := 3

/-- Batch reduction; dropped clauses are counted as deletions so the flow
conservation check stays exact. -/
def doReduce (st : DState) : DState :=
  let lc' := reduce P trail st.lc
  let dropped := st.lc.active.filter (fun c => !(retain P trail c))
  { st with
    lc := lc'
    deletes := st.deletes + (st.lc.active.length - lc'.active.length)
    deleted := dropped ++ st.deleted
    reduces := st.reduces + 1 }

/-- One generated operation: insert (with the re-keyed history guard,
refusals counted as fallbacks — and as relearnings when the clause had
been deleted before), single eligible deletion, or reduction. -/
def step (st : DState) : DState :=
  let r := next st.seed
  let st := { st with seed := r }
  match r % 3 with
  | 0 =>
      let c := pool.getD ((r / 3) % pool.length) c0
      if canonSeenB P.f st.lc c then
        { st with
          fallbacks := st.fallbacks + 1
          relearns := st.relearns + (if st.deleted.contains c then 1 else 0) }
      else
        { st with lc := insert c st.lc, inserts := st.inserts + 1 }
  | 1 =>
      match st.lc.active.find? (fun c => !(retain P trail c)) with
      | some c =>
          { st with
            lc := delete c st.lc
            deletes := st.deletes + 1
            deleted := c :: st.deleted }
      | none => st
  | _ => doReduce st

/-- The per-step checks (documented invariants above). -/
def checkStep (st st' : DState) : Bool :=
  activeInHistoryB st'.lc &&
  lockedB trail st'.lc &&
  (st'.lc.active.length + st'.deletes == st'.inserts + initialActive) &&
  (st'.inserts ≤ pool.length) &&
  (st'.relearns ≤ st'.fallbacks) &&
  (absentCount P.f st'.lc.history pool ≤ absentCount P.f st.lc.history pool) &&
  (!(st'.inserts > st.inserts) ||
    (absentCount P.f st'.lc.history pool < absentCount P.f st.lc.history pool &&
      st'.lc.history.length == st.lc.history.length + 1)) &&
  (!(st'.deletes > st.deletes) || st'.lc.active.length < st.lc.active.length) &&
  (!(st'.reduces > st.reduces) || st'.lc.active.all (retain P trail))

/-- The instrumented fold: every step's checks are accumulated into
`ok`. -/
def runF : Nat → DState → DState
  | 0, st => st
  | n + 1, st =>
      let st' := step st
      runF n { st' with ok := st'.ok && checkStep st st' }

def final : DState := runF 400 initState

/-- The 12-step prefix is checked in the kernel (the driver itself, not
only its evaluation). -/
example : (runF 12 initState).ok = true := by decide

#guard final.ok
#guard decide (final.inserts > 0)
#guard decide (final.deletes > 0)
#guard decide (final.fallbacks > 0)
#guard decide (final.reduces > 0)
#guard decide (final.relearns > 0)
-- summary evidence: (inserts, deletes, fallbacks, relearns, reduces, ok)
#eval (final.inserts, final.deletes, final.fallbacks, final.relearns,
  final.reduces, final.ok)

/-! ## §4 Concrete obligation instances -/

/-- Membership for a concrete list, through the computable `contains`
(avoids relying on a `Decidable` membership instance). -/
theorem mem_contains {α : Type} [BEq α] [LawfulBEq α] {a : α} {l : List α}
    (h : l.contains a = true) : a ∈ l :=
  List.contains_iff_mem.mp h

/-- The live reason `c4` is never eligible: the retention rule's live
reason arm fires. -/
example : ¬ Eligible P trail fullLc c4 :=
  fun h => h.2 (retain_of_mem_liveReasons (mem_contains (by decide)))

/-- A normalized unit clause (`c1`) is never eligible. -/
example : ¬ Eligible P trail fullLc c1 :=
  fun h => h.2 (retain_of_isUnit ((isUnit_iff c1).mp (by decide)))

/-- A kept (original/seed) clause (`c0`) is never eligible. -/
example : ¬ Eligible P trail fullLc c0 :=
  fun h => h.2 (retain_of_mem_keep (mem_contains (by decide)))

/-- A retained witness (`c6`) is never eligible. -/
example : ¬ Eligible P trail (insert c6 fullLc) c6 :=
  fun h => h.2 (retain_of_mem_witnesses (mem_contains (by decide)))

/-- `c2` IS eligible (the deletion policy is non-trivial on this
universe). -/
example : Eligible P trail fullLc c2 :=
  ⟨mem_contains (by decide), (retain_eq_false_iff P trail c2).mp (by decide)⟩

/-- The relearning refusal, concretely: `c2` deleted stays certified, so
re-deriving it is not an admissible insertion. -/
example : ¬ GuardHistoryNovel P.f (delete c2 fullLc) c2 :=
  fun hnov =>
    hnov (canonSeenWith_delete P.f c2 fullLc
      ((canonSeenB_iff P.f fullLc c2).mp (by decide)))

/-- Removing the only lock (the trail is empty, so `c4` is no longer a
live reason) makes `c4` eligible: retention is arm-driven, not
clause-intrinsic. -/
example : Eligible P [] fullLc c4 :=
  ⟨mem_contains (by decide), (retain_eq_false_iff P [] c4).mp (by decide)⟩

end Tests.Propagation.ClauseReductionStress
