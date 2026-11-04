/-
File: LeanFzn/Solver/Propagation/ClauseReduction.lean

Purpose (PLAN.md §7 task L1 — certified learned-clause reduction):

  The MODULE-ONLY certified deletion policy on top of the frozen L0
  lifecycle vocabulary (`ClauseLifecycle.lean`):

  * §1 normalized unit clauses (the `UnitDB`/`UnitLearned` shape);
  * §2 the deterministic retention policy `Policy`/`Retain`/`retain`:
    the conservative core retains caller-protected clauses (`keep`:
    originals, optimization seeds), retained progress witnesses
    (`witnesses`: the pre-`history`-re-keying protection; may be empty
    once the L0 §5.4 re-keying is wired), every live reason
    (`liveReasons`), and every normalized unit clause. Score-guided
    selection (length/activity/decision-level diversity) is a leaf: it
    may order the eligible candidates but never changes `Retain`, so no
    soundness argument reads a score;
  * §3 proof-carrying single deletion `deleteEligible` and its laws:
    live reason availability, certificate invariance, database
    entailment, and the `activeLength` payment;
  * §4 the deterministic batch reduction `reduce` (drop every eligible
    active clause) with its laws, including the fixpoint property
    `reduce_no_eligible` and the strict `activeLength` decrease;
  * §5 watch integrity (positional identity): deletion invalidates an
    aligned `ClauseWatch` (`not_watchOK_delete`), the reset state is
    never an accepted index (`not_watchOK_reset`), and reset-then-scan
    re-establishes `WatchOK` on the post-deletion database — the exact
    L0 wiring route (`ClauseWatch.reset` + `establish_WatchOK`);
  * §6 coverage: under an entailed database the exclusion disjunct is
    vacuous on leaf solutions, so deleting a clause cannot lose a leaf
    solution — the deletion transport of `CoversRemainingLeaves` is
    re-proved here in its frame-only form (`covers_delete`,
    `covers_reduce`, `covers_frame_only_of_entailed`);
  * §7 preserved well-founded progress despite relearning: the history
    countdown (`absentCount`, the local twin of `P3.absentCountMap` read
    at `history`) strictly decreases on every admissible insertion and
    is untouched by deletion; deletion strictly decreases `activeLength`;
    the two-component lex measure is well-founded (`lexLt_wf`) and no
    infinite policy run exists (`step_no_infinite`). The relearning
    interaction is stated exactly: a deleted clause remains in the
    certificate (`relearn_after_delete_not_admissible`), so re-deriving
    it is NOT an admissible insertion and the runtime must take the
    certified chronological fallback (the missing piece is the L0 §5.4
    guard re-keying at the insertion sites, listed in the module docs
    below);
  * §8 optimization reuse: the next-bound entailment condition
    (`NextBoundEntailed`) with its provable transport
    (`nextBoundEntailed_of_leaf_mono`: tightened bounds only) and the
    exact missing pieces recorded.

  Honest scope. This module wires NOTHING: it separates the policy, the
  operations and the obligations as definitions and theorems over
  `Lifecycle`, so the runtime modules (`SchedulerState.lean`,
  `SchedulerStep*.lean`, `ClauseWatch` consumption sites) can later
  instantiate them without any proof re-invention. The obligations that
  remain at the integration site (each stated as an explicit hypothesis
  or `Prop`-def here):

    1. the history-keyed guards: `learnedRepeats`, `recordedAnalysis`,
       `explainedDeductionOf`, `terminalResultOf` and the
       `Propagation/Pruning.lean` `db.contains` freshness filters must
       read `history` instead of the active database (L0 §5.4). The
       module's `Step.insert` is exactly the shape they must produce;
       `relearn_after_delete_not_admissible` shows why the active key is
       unsound for the countdown;
    2. the pool membership of every inserted clause's canonical form
       (`Step.insert`'s `hp`/`hcanon`; unconditionally available for the
       real analyses via `canonicalSortedWith_mem_sortedClausePoolWith`
       — recorded, not reproved);
    3. the watch reset-on-delete (`WatchDeleteCompatible`) at every
       deletion site;
    4. the coverage re-proof at the runtime site: the abstract
       `CoversWith` transport proved here, instantiated with
       `CoversRemainingLeaves`, `OriginalLeaves` and `FrameCovers`;
    5. the next-bound leaf subset `hsub` (monotone tightening) and the
       per-round seed entailment for §8.

  DAG check (acyclicity): imports `ClauseLifecycle` (which imports only
  `BranchState`) and `ClauseWatch` (which imports `DbScanIndex`,
  `ValueEquality`). Neither imports this module, and no module imports
  it; the new module sits at the same layer as `RestartProto.lean` and
  is unimported by the runtime.

  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no proof escapes.
-/

import LeanFzn.Legacy.Solver.Propagation.ClauseLifecycle
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch

set_option autoImplicit false

namespace LeanFzn.Solver.Propagation.ClauseReduction
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.ClauseLifecycle
open LeanFzn.Solver.Propagation.ClauseLifecycle.Lifecycle

/-! ## §1 Normalized unit clauses

The retention rule protects unit clauses; the predicate is the exact
`UnitDB`/`UnitLearned` shape (`∃ q, c = [q] ∧ q = q.norm`), with a
computable twin for the deterministic policy. -/

/-- A normalized unit clause (the shape `ExplainedPropagation.UnitDB` and
`DomExplained.UnitLearned` quantify over; restated locally so the import
cone stays at L0/W1). -/
def IsUnit (c : Clause) : Prop := ∃ q : Literal, c = [q] ∧ q = q.norm

/-- The computable unit test used by the deterministic policy. -/
def isUnit (c : Clause) : Bool :=
  match c with
  | [q] => q == q.norm
  | _ => false

theorem isUnit_iff (c : Clause) : isUnit c = true ↔ IsUnit c := by
  cases c with
  | nil => simp [isUnit, IsUnit]
  | cons q cs =>
    cases cs with
    | nil =>
      simp only [isUnit, IsUnit, List.singleton_inj]
      constructor
      · intro h
        exact ⟨q, by simp, beq_iff_eq.mp h⟩
      · rintro ⟨q', hq', hq'n⟩
        subst hq'
        simpa [beq_iff_eq] using hq'n
    | cons q' cs' =>
      simp [isUnit, IsUnit]

theorem isUnit_eq_false_iff (c : Clause) : isUnit c = false ↔ ¬ IsUnit c := by
  rw [Bool.eq_false_iff, ne_eq, isUnit_iff]

/-! ## §2 The deterministic retention policy

`Policy` carries only data: the canonical projection `f` and fixed pool
`pool` of the progress countdown (§7), the caller keep list `keep`
(originals, optimization seeds, round-critical clauses) and the retained
progress witnesses `witnesses` (the active-keyed protection; empty under
the L0 §5.4 re-keying). `Retain` is the conservative rule; `retain` is
its computable twin. Eligible deletions are exactly the non-retained
active clauses (§3); scores are not part of `Retain`, so they cannot
affect soundness. -/

/-- The L1 deletion-policy data. -/
structure Policy where
  /-- the canonical projection used by the progress countdown -/
  f : Clause → Clause
  /-- the fixed progress pool (canonical-image members are the rank's
  countdown domain) -/
  pool : List Clause
  /-- caller keep list: original clauses, optimization seeds, and other
  round-critical clauses that must stay active -/
  keep : List Clause
  /-- retained progress witnesses (the conservative pre-`history`
  protection; may be `[]` once the §5.4 re-keying is wired) -/
  witnesses : List Clause

/-- The conservative policy of PLAN §7 L1: retain the originals
(`keep`), the retained progress witnesses (`witnesses`), every live
reason and every normalized unit clause. -/
def Policy.conservative (f : Clause → Clause) (pool keep witnesses : List Clause) :
    Policy :=
  { f := f, pool := pool, keep := keep, witnesses := witnesses }

/-- The conservative retention rule (§2). A retained clause may never be
deleted; `retain` computes the same predicate. -/
def Retain (P : Policy) (trail : List TrailEntry) (c : Clause) : Prop :=
  c ∈ P.keep ∨ c ∈ P.witnesses ∨ c ∈ liveReasons trail ∨ IsUnit c

/-- The deterministic retention test. -/
def retain (P : Policy) (trail : List TrailEntry) (c : Clause) : Bool :=
  P.keep.contains c || P.witnesses.contains c || (liveReasons trail).contains c || isUnit c

theorem retain_eq_true_iff (P : Policy) (trail : List TrailEntry) (c : Clause) :
    retain P trail c = true ↔ Retain P trail c := by
  simp only [retain, Retain, List.contains_iff_mem, isUnit_iff, Bool.or_eq_true, or_assoc]

theorem retain_eq_false_iff (P : Policy) (trail : List TrailEntry) (c : Clause) :
    retain P trail c = false ↔ ¬ Retain P trail c := by
  rw [Bool.eq_false_iff, ne_eq, retain_eq_true_iff]

theorem retain_of_mem_keep {P : Policy} {trail : List TrailEntry} {c : Clause}
    (h : c ∈ P.keep) : Retain P trail c :=
  Or.inl h

theorem retain_of_mem_witnesses {P : Policy} {trail : List TrailEntry} {c : Clause}
    (h : c ∈ P.witnesses) : Retain P trail c :=
  Or.inr (Or.inl h)

theorem retain_of_mem_liveReasons {P : Policy} {trail : List TrailEntry} {c : Clause}
    (h : c ∈ liveReasons trail) : Retain P trail c :=
  Or.inr (Or.inr (Or.inl h))

theorem retain_of_isUnit {P : Policy} {trail : List TrailEntry} {c : Clause}
    (h : IsUnit c) : Retain P trail c :=
  Or.inr (Or.inr (Or.inr h))

/-! ## §3 Proof-carrying deletion

`Eligible` is the deletion predicate the policy yields; `deleteEligible`
performs one deletion and carries the eligibility proof (which is what
every soundness law below consumes). -/

/-- The deletion predicate of the deterministic policy: an eligible clause
is active and not retained. -/
def Eligible (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) (c : Clause) : Prop :=
  c ∈ lc.active ∧ ¬ Retain P trail c

theorem eligible_active {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) : c ∈ lc.active :=
  h.1

theorem eligible_not_retain {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) : ¬ Retain P trail c :=
  h.2

theorem eligible_not_mem_keep {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) : c ∉ P.keep :=
  fun hk => h.2 (retain_of_mem_keep hk)

theorem eligible_not_mem_witnesses {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) : c ∉ P.witnesses :=
  fun hw => h.2 (retain_of_mem_witnesses hw)

theorem eligible_not_mem_liveReasons {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) : c ∉ liveReasons trail :=
  fun hr => h.2 (retain_of_mem_liveReasons hr)

theorem eligible_not_isUnit {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) : ¬ IsUnit c :=
  fun hu => h.2 (retain_of_isUnit hu)

/-- A score assignment (clause length, activity, decision-level
diversity). Scores are a LEAF: they may re-rank or sub-select the
candidate list, never change `Retain`/`Eligible`, so no soundness or
transport argument reads them. -/
abbrev Score := Clause → Nat

/-- The eligible candidates in database order (the deterministic
enumeration of what the policy permits to delete). -/
def Candidates (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) : List Clause :=
  lc.active.filter fun c => !(retain P trail c)

/-- The candidates are exactly the eligible clauses. -/
theorem mem_candidates_iff (P : Policy) (trail : List TrailEntry) (lc : Lifecycle)
    (c : Clause) : c ∈ Candidates P trail lc ↔ Eligible P trail lc c := by
  rw [Candidates, List.mem_filter]
  constructor
  · rintro ⟨hc, hnot⟩
    exact ⟨hc, (retain_eq_false_iff P trail c).mp ((Bool.not_eq_true' _).mp hnot)⟩
  · rintro ⟨hc, hnr⟩
    exact ⟨hc, (Bool.not_eq_true' (retain P trail c)).mpr
      ((retain_eq_false_iff P trail c).mpr hnr)⟩

/-- **THE SCORE LEAF**: every candidate is eligible, so a score-guided
selection among the candidates deletes only eligible clauses — the score
picks which permitted clauses die, the eligibility and the deletion laws
above carry the soundness. -/
theorem candidates_eligible {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : c ∈ Candidates P trail lc) : Eligible P trail lc c :=
  (mem_candidates_iff P trail lc c).mp h

/-- Delete one eligible clause. Proof-carrying: the eligibility proof is
the only premise the deletion laws need, and it is erased at runtime. -/
def deleteEligible (P : Policy) (trail : List TrailEntry) (lc : Lifecycle)
    (c : Clause) (_h : Eligible P trail lc c) : Lifecycle :=
  delete c lc

theorem deleteEligible_history (P : Policy) (trail : List TrailEntry) (lc : Lifecycle)
    (c : Clause) (h : Eligible P trail lc c) :
    (deleteEligible P trail lc c h).history = lc.history :=
  rfl

/-- Every surviving clause is still active (the deletion only shrinks the
left side). -/
theorem deleteEligible_active_subset {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) {d : Clause}
    (hd : d ∈ (deleteEligible P trail lc c h).active) : d ∈ lc.active :=
  List.mem_of_mem_erase hd

/-- **THE DELETION PAYMENT**: an eligible deletion strictly decreases the
active length (component 2 of the §7 measure; L0's
`Lifecycle.activeLength_delete_lt`). -/
theorem deleteEligible_activeLength_lt {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) :
    (deleteEligible P trail lc c h).active.length < lc.active.length :=
  activeLength_delete_lt h.1

/-- Deletion leaves the certificate alone (L0's `historyGrowth_delete` at
the operation). -/
theorem deleteEligible_historyGrowth {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) :
    HistoryGrowth lc (deleteEligible P trail lc c h) :=
  historyGrowth_delete c lc

/-- **CERTIFICATE INVARIANCE**: every consumed progress witness survives
the deletion (L0's `canonSeenWith_delete`, exported at the operation). -/
theorem deleteEligible_canonSeenWith {g : Clause → Clause} {P : Policy}
    {trail : List TrailEntry} {lc : Lifecycle} {c : Clause}
    (h : Eligible P trail lc c) {q : Clause} (hseen : CanonSeenWith g lc q) :
    CanonSeenWith g (deleteEligible P trail lc c h) q :=
  canonSeenWith_delete g c lc hseen

/-- **LIVE REASON AVAILABILITY** (PLAN §7 L1 obligation): an eligible
deletion keeps every live reason of the policy's trail active, because
live reasons are retained by the policy. -/
theorem deleteEligible_lockedReasons {P : Policy} {trail : List TrailEntry}
    {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c)
    (hl : LockedReasons lc trail) :
    LockedReasons (deleteEligible P trail lc c h) trail := by
  have hc : c ∉ liveReasons trail := fun hr => h.2 (retain_of_mem_liveReasons hr)
  exact lockedReasons_delete hl hc

/-- **DATABASE ENTAILMENT** (PLAN §7 L1 obligation): the well-formed
lifecycle survives an eligible deletion, so the active database stays
entailed by seed + certificate (L0's unconditional `wellFormed_delete`). -/
theorem deleteEligible_wellFormed {leaf : Assignment → Bool} {seed : List Clause}
    {P : Policy} {trail : List TrailEntry} {lc : Lifecycle} {c : Clause}
    (hw : WellFormed leaf seed lc) (h : Eligible P trail lc c) :
    WellFormed leaf seed (deleteEligible P trail lc c h) :=
  wellFormed_delete hw c

/-! ## §4 The deterministic batch reduction

`reduce` drops exactly the eligible clauses in list order: deterministic
(no score is read), a one-shot fixpoint (`reduce_no_eligible`), and
idempotent. Its laws mirror §3 at the batch level. -/

/-- The deterministic batch reduction: keep the retained active clauses
in order, drop the rest; the certificate is untouched. -/
def reduce (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) : Lifecycle :=
  { lc with active := lc.active.filter (retain P trail) }

theorem reduce_history (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) :
    (reduce P trail lc).history = lc.history :=
  rfl

theorem mem_reduce_active_iff (P : Policy) (trail : List TrailEntry) (lc : Lifecycle)
    (c : Clause) :
    c ∈ (reduce P trail lc).active ↔ c ∈ lc.active ∧ Retain P trail c := by
  show c ∈ lc.active.filter (retain P trail) ↔ c ∈ lc.active ∧ Retain P trail c
  rw [List.mem_filter, retain_eq_true_iff]

theorem reduce_active_subset {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : c ∈ (reduce P trail lc).active) : c ∈ lc.active :=
  ((mem_reduce_active_iff P trail lc c).mp h).1

/-- `reduce` deletes exactly the candidates: the batch law is the
deletion of the score-leaf's enumeration. -/
theorem mem_candidates_iff_mem_active_and_not_reduce (P : Policy)
    (trail : List TrailEntry) (lc : Lifecycle) (c : Clause) :
    c ∈ Candidates P trail lc ↔ c ∈ lc.active ∧ c ∉ (reduce P trail lc).active := by
  rw [mem_candidates_iff, mem_reduce_active_iff]
  constructor
  · rintro ⟨ha, hnr⟩
    exact ⟨ha, fun hred => hnr hred.2⟩
  · rintro ⟨ha, hred⟩
    exact ⟨ha, fun hr => hred ⟨ha, hr⟩⟩

/-- Every surviving active clause is retained (what the fixpoint law and
the coverage/entailment transports read). -/
theorem reduce_retained {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : c ∈ (reduce P trail lc).active) : Retain P trail c :=
  ((mem_reduce_active_iff P trail lc c).mp h).2

/-- **THE POLICY FIXPOINT**: after `reduce` no active clause is eligible;
a second reduction deletes nothing (the policy is a deterministic
one-shot reduction). -/
theorem reduce_no_eligible (P : Policy) (trail : List TrailEntry) (lc : Lifecycle)
    (c : Clause) : ¬ Eligible P trail (reduce P trail lc) c :=
  fun h => h.2 (reduce_retained h.1)

theorem reduce_idem (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) :
    reduce P trail (reduce P trail lc) = reduce P trail lc := by
  unfold reduce
  rw [List.filter_filter]
  simp only [Bool.and_self]

theorem reduce_activeLength_le (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) :
    (reduce P trail lc).active.length ≤ lc.active.length :=
  List.length_filter_le _ _

private theorem filter_false_length_lt {l : List Clause} {p : Clause → Bool}
    (h : ∃ c ∈ l, p c = false) : (l.filter p).length < l.length := by
  induction l with
  | nil => rcases h with ⟨c, hc, _⟩; cases hc
  | cons a as ih =>
      rw [List.filter_cons]
      by_cases ha : p a = true
      · rw [if_pos ha]
        simp only [List.length_cons]
        have hex : ∃ c ∈ as, p c = false := by
          rcases h with ⟨c, hc, hpc⟩
          rcases List.mem_cons.mp hc with rfl | hc'
          · rw [hpc] at ha
            exact absurd ha (by simp)
          · exact ⟨c, hc', hpc⟩
        have := ih hex
        omega
      · rw [if_neg ha]
        have := List.length_filter_le p as
        simp only [List.length_cons]
        omega

/-- **THE DELETION PAYMENT, BATCH FORM**: a nonempty eligible set makes
`reduce` strictly shrink the active length. -/
theorem reduce_activeLength_lt {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) :
    (reduce P trail lc).active.length < lc.active.length :=
  filter_false_length_lt ⟨c, h.1, (retain_eq_false_iff P trail c).mpr h.2⟩

theorem reduce_historyGrowth (P : Policy) (trail : List TrailEntry) (lc : Lifecycle) :
    HistoryGrowth lc (reduce P trail lc) :=
  historyGrowth_refl lc

/-- **LIVE REASON AVAILABILITY, BATCH FORM**: reduction keeps every live
reason active. -/
theorem reduce_lockedReasons {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    (hl : LockedReasons lc trail) : LockedReasons (reduce P trail lc) trail :=
  fun c hc =>
    (mem_reduce_active_iff P trail lc c).mpr ⟨hl c hc, retain_of_mem_liveReasons hc⟩

/-- **DATABASE ENTAILMENT, BATCH FORM**: reduction preserves the
well-formed lifecycle (hence active entailment via
`wellFormed_active_entailed`). -/
theorem reduce_wellFormed {leaf : Assignment → Bool} {seed : List Clause} {P : Policy}
    {trail : List TrailEntry} {lc : Lifecycle} (hw : WellFormed leaf seed lc) :
    WellFormed leaf seed (reduce P trail lc) :=
  ⟨fun c hc => hw.1 c (reduce_active_subset hc), hw.2⟩

/-! ## §5 Watch integrity (positional identity)

The W1 watch index `ClauseWatch` is positionally aligned with the scanned
database (`WatchOK`'s `w.entries.length = db.length` conjunct and the
`WatchEntriesOK` alignment). Deletion therefore cannot be done in place:
already-aligned entries no longer match the post-deletion list. The
proved facts are exactly the L0 wiring route: the old `WatchOK` index
fails after a deletion (`not_watchOK_delete`), the reset state is not an
accepted index (`not_watchOK_reset`), a reset index forces the establish
pass (`scanDatabaseWatch_of_compatible`), and the establish pass returns
a fresh `WatchOK` index at the post-deletion database
(`scanDatabaseWatch_of_compatible_snd_watchOK`). -/

private theorem erase_length_lt_of_mem {c : Clause} {l : List Clause} (h : c ∈ l) :
    (l.erase c).length < l.length := by
  have h1 : (l.erase c).length = l.length - 1 := List.length_erase_of_mem h
  have h2 : 0 < l.length := List.length_pos_of_mem h
  omega

/-- **DELETION BREAKS POSITIONAL ALIGNMENT**: a `WatchOK` index aligned
with the pre-deletion database cannot be aligned with the post-deletion
database — its entries keep the old length. -/
theorem not_watchOK_delete {f : BranchFrame} {lc : Lifecycle} {w : ClauseWatch}
    (h : WatchOK f lc.active w) {c : Clause} (hc : c ∈ lc.active) :
    ¬ WatchOK f (delete c lc).active w := by
  intro h'
  have hlen : w.entries.length = lc.active.length := h.2.2.1
  have hlen' : w.entries.length = (delete c lc).active.length := h'.2.2.1
  rw [hlen, delete_active] at hlen'
  have hlt : (lc.active.erase c).length < lc.active.length := erase_length_lt_of_mem hc
  omega

/-- **THE RESET IS STALE BY CONSTRUCTION**: `WatchOK` demands freshness,
and `ClauseWatch.reset` has `fresh = false`, so the fast pass can never
accept a reset index. -/
theorem not_watchOK_reset (f : BranchFrame) (db : List Clause) :
    ¬ WatchOK f db ClauseWatch.reset := by
  intro h
  have hf : ClauseWatch.reset.fresh = true := h.1
  rw [ClauseWatch.reset_fresh] at hf
  exact Bool.noConfusion hf

/-- The deletion-site update of the watch index: reset (no positional
surgery). -/
def watchResetOnDelete (_w : ClauseWatch) : ClauseWatch :=
  ClauseWatch.reset

theorem watchResetOnDelete_eq (w : ClauseWatch) :
    watchResetOnDelete w = ClauseWatch.reset :=
  rfl

/-- A deletion-compatible index state: freshness off, so the next scan
runs the establish pass. `watchResetOnDelete` meets it. -/
def WatchDeleteCompatible (w : ClauseWatch) : Prop :=
  w.fresh = false

theorem watchResetOnDelete_compatible (w : ClauseWatch) :
    WatchDeleteCompatible (watchResetOnDelete w) :=
  rfl

theorem watchDeleteCompatible_reset : WatchDeleteCompatible ClauseWatch.reset :=
  rfl

/-- **THE COMPATIBILITY ROUTE**: any deletion-compatible index takes the
establish pass on the next scan, i.e. the post-deletion database is fully
re-indexed (there is no accepted stale-position path). -/
theorem scanDatabaseWatch_of_compatible {w : ClauseWatch} (h : WatchDeleteCompatible w)
    (original : List Clause) (f : BranchFrame) (db : List Clause) :
    scanDatabaseWatch original f w db = establish original f db := by
  unfold scanDatabaseWatch
  split
  · rename_i hguard
    rw [h] at hguard
    simp_all
  · rfl

/-- **WATCH INTEGRITY, RE-ESTABLISHED**: a deletion-compatible index yields
a fresh `WatchOK` index at the scanned database via the establish pass. -/
theorem scanDatabaseWatch_of_compatible_snd_watchOK {w : ClauseWatch}
    (h : WatchDeleteCompatible w) (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    WatchOK f db (scanDatabaseWatch original f w db).2 := by
  rw [scanDatabaseWatch_of_compatible h]
  exact establish_WatchOK original f db

/-- The reset index forces the establish pass (instance of
`scanDatabaseWatch_of_compatible`). -/
theorem scanDatabaseWatch_reset (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    scanDatabaseWatch original f ClauseWatch.reset db = establish original f db :=
  scanDatabaseWatch_of_compatible watchDeleteCompatible_reset original f db

/-- **THE ASSEMBLED DELETE ROUTE**: after a deletion, reset-then-scan
re-establishes `WatchOK` at the post-deletion database. This is the exact
L0 wiring prerequisite (`ClauseWatch.reset` + `establish_WatchOK`), proved
at the deletion site rather than assumed. -/
theorem scanDatabaseWatch_reset_after_delete_watchOK (original : List Clause)
    (f : BranchFrame) (lc : Lifecycle) (c : Clause) :
    WatchOK f (delete c lc).active
      (scanDatabaseWatch original f ClauseWatch.reset (delete c lc).active).2 :=
  scanDatabaseWatch_of_compatible_snd_watchOK watchDeleteCompatible_reset original f _

/-- The stale-pre-deletion-index guard fails on the post-deletion
database: the lengths differ, so the fast pass cannot fire even before an
explicit reset. -/
theorem scanDatabaseWatch_delete_guard_false {f : BranchFrame} {lc : Lifecycle}
    {w : ClauseWatch} (h : WatchOK f lc.active w) {c : Clause} (hc : c ∈ lc.active) :
    (w.fresh && (w.entries.length == (delete c lc).active.length)) = false := by
  have hlen : w.entries.length = lc.active.length := h.2.2.1
  have hlt : (lc.active.erase c).length < lc.active.length := erase_length_lt_of_mem hc
  have hbeq : (w.entries.length == (delete c lc).active.length) = false := by
    rw [delete_active, Bool.eq_false_iff, ne_eq, beq_iff_eq]
    intro heq
    rw [hlen] at heq
    omega
  rw [hbeq]
  simp

/-- A still-aligned pre-deletion `WatchOK` index is rejected by the length
guard on the post-deletion database: the scan takes the establish pass.
(The runtime policy still resets on deletion — `WatchDeleteCompatible` —
because a delete followed by an insert before the next scan could
otherwise restore the length and hide the structural change.) -/
theorem scanDatabaseWatch_delete_of_watchOK {f : BranchFrame} {lc : Lifecycle}
    {w : ClauseWatch} (h : WatchOK f lc.active w) {c : Clause} (hc : c ∈ lc.active)
    (original : List Clause) :
    scanDatabaseWatch original f w (delete c lc).active
      = establish original f (delete c lc).active := by
  unfold scanDatabaseWatch
  split
  · rename_i hguard
    rw [scanDatabaseWatch_delete_guard_false h hc] at hguard
    exact Bool.noConfusion hguard
  · rfl

/-! ## §6 Coverage

The runtime coverage predicate is `CoversRemainingLeaves leaf orig pending
db` (`UIP/SchedulerState.lean`): every original leaf solution is covered
by a remaining frame or excluded by an active clause. On the certified
route the database is entailed (`LearnedEntailed`), so the exclusion
disjunct is VACUOUS on leaf solutions (L0 audit §3, `entailed_db_never_
excludes` in `SchedulerCoverage.lean`): coverage is frame-only, and a
deletion — which only shrinks the database — cannot lose a leaf solution.
The statements below keep the Scheduler modules out of the import cone by
taking the search space and the frame disjunct as abstract predicates; the
instantiation is `space a := a.Fits orig`,
`frames a := ∃ f ∈ pending, FrameCovers f a` (the curried
`OriginalLeaves` split). -/

/-- The database-exclusion disjunct of the coverage predicate. -/
def DBExcludes (lc : Lifecycle) (a : Assignment) : Prop :=
  ∃ c ∈ lc.active, ¬ c.SatisfiedBy a

/-- Curried `CoversRemainingLeaves`: every member of `space` that is a
leaf solution is covered by the frames or excluded by the active clauses. -/
def CoversWith (leaf : Assignment → Bool) (space : Assignment → Prop)
    (frames : Assignment → Prop) (lc : Lifecycle) : Prop :=
  ∀ a, leaf a = true → space a → frames a ∨ DBExcludes lc a

/-- **THE VACUITY LEMMA**: an entailed active database excludes no leaf
solution. -/
theorem not_dbExcludes_of_entailed {leaf : Assignment → Bool} {lc : Lifecycle}
    (hent : LearnedEntailed leaf lc.active) {a : Assignment} (ha : leaf a = true) :
    ¬ DBExcludes lc a := by
  rintro ⟨c, hc, hnc⟩
  exact hnc (hent c hc a ha)

/-- **FRAME-ONLY COVERAGE**: under an entailed database the coverage
predicate collapses to its frame disjunct — a database-independent
statement, hence immune to any deletion. -/
theorem coversWith_frame_only_of_entailed {leaf : Assignment → Bool}
    {space frames : Assignment → Prop} {lc : Lifecycle}
    (h : CoversWith leaf space frames lc) (hent : LearnedEntailed leaf lc.active) :
    ∀ a, leaf a = true → space a → frames a := by
  intro a ha hsp
  rcases h a ha hsp with hfr | hex
  · exact hfr
  · exact absurd hex (not_dbExcludes_of_entailed hent ha)

/-- **COVERAGE TRANSPORT (DELETE)**: deleting a clause cannot lose a leaf
solution — on leaf solutions the exclusion disjunct was already vacuous,
so the surviving coverage is frame-only. -/
theorem coversWith_delete {leaf : Assignment → Bool} {space frames : Assignment → Prop}
    {lc : Lifecycle} {c : Clause} (h : CoversWith leaf space frames lc)
    (hent : LearnedEntailed leaf lc.active) :
    CoversWith leaf space frames (delete c lc) :=
  fun a ha hsp => Or.inl (coversWith_frame_only_of_entailed h hent a ha hsp)

/-- **COVERAGE TRANSPORT (REDUCE)**: the batch reduction of the
deterministic policy cannot lose a leaf solution either. -/
theorem coversWith_reduce {leaf : Assignment → Bool} {space frames : Assignment → Prop}
    {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    (h : CoversWith leaf space frames lc) (hent : LearnedEntailed leaf lc.active) :
    CoversWith leaf space frames (reduce P trail lc) :=
  fun a ha hsp => Or.inl (coversWith_frame_only_of_entailed h hent a ha hsp)

/-! ## §7 Preserved well-founded progress despite relearning

The L0 re-keying plan (`L0-clause-lifecycle.md` §5): read the existing
pool countdown at `history` instead of the active database. Deletion then
cannot raise it (`reduce`/`delete` leave `history` untouched), and every
HISTORY-NOVEL insertion strictly decreases it. The module proves the
countdown algebra (local twins of `P3.absentCountMap`,
`P3.absentCountMap_mono`, `P3.absentCountMap_lt_of_mono_mem` — the rank
cone itself is out of the import budget), the two-component lex measure,
its strict decrease on every admissible step, and its well-foundedness
(`step_no_infinite`).

The relearning interaction is the exact obligation of L0 §5.4: with the
old ACTIVE-keyed guards (`learnedRepeats`, `recordedAnalysis`,
`explainedDeductionOf`, `terminalResultOf`, the `Pruning.lean`
`db.contains` filters) a deleted clause looks new and would be re-inserted
WITHOUT decreasing any history count. The frozen answer: key the guards to
`history`; then a re-derived clause is already seen and the run must take
the certified chronological fallback — formalized by
`relearn_after_delete_not_admissible`, which shows no admissible insertion
can have a history-seen clause. That re-keying, the pool membership
hypotheses `hp`/`hcanon` of `Step.insert` (unconditional in the rank
vocabulary via `canonicalSortedWith_mem_sortedClausePoolWith`), and the
instantiation of the six-tuple measure of L0 §5.1 remain the runtime
integration obligations. -/

/-- Number of FIXED-POOL clauses whose canonical image `f p` is absent
from the database's canonical image. Local twin of `P3.absentCountMap`
(`UIP/Proofs/SchedulerRank.lean`), read at a lifecycle database (the
`history` component under the L0 re-keying). -/
def absentCount (f : Clause → Clause) (db pool : List Clause) : Nat :=
  match pool with
  | [] => 0
  | p :: ps => (if p ∈ db.map f then 0 else 1) + absentCount f db ps

/-- The countdown is non-increasing under database growth. -/
theorem absentCount_mono {f : Clause → Clause} {db db' : List Clause}
    (h : ∀ d ∈ db, d ∈ db') (pool : List Clause) :
    absentCount f db' pool ≤ absentCount f db pool := by
  induction pool with
  | nil => simp [absentCount]
  | cons p ps ih =>
      simp only [absentCount]
      have hhead : (if p ∈ db'.map f then 0 else 1) ≤
          (if p ∈ db.map f then 0 else 1) := by
        by_cases hp : p ∈ db.map f
        · have hp' : p ∈ db'.map f := by
            rcases List.mem_map.mp hp with ⟨d, hd, hfd⟩
            exact List.mem_map.mpr ⟨d, h d hd, hfd⟩
          simp [hp, hp']
        · by_cases hp' : p ∈ db'.map f <;> simp [hp, hp']
      omega

/-- **THE COUNTDOWN PAYMENT**: one genuinely new pool member strictly
decreases the countdown (the local twin of
`P3.absentCountMap_lt_of_mono_mem`). -/
theorem absentCount_lt_of_new_mem {f : Clause → Clause} {db db' pool : List Clause}
    {p : Clause} (hmono : ∀ d ∈ db, d ∈ db') (hpool : p ∈ pool)
    (hnew : p ∈ db'.map f) (hold : p ∉ db.map f) :
    absentCount f db' pool < absentCount f db pool := by
  induction pool with
  | nil => exact absurd hpool (by simp)
  | cons q qs ih =>
      simp only [absentCount]
      rcases List.mem_cons.mp hpool with rfl | htl
      · have h1 : (if p ∈ db'.map f then 0 else 1) = 0 := if_pos hnew
        have h0 : (if p ∈ db.map f then 0 else 1) = 1 := if_neg hold
        have htle := absentCount_mono (f := f) hmono qs
        rw [h1, h0]
        omega
      · have hhead : (if q ∈ db'.map f then 0 else 1) ≤
            (if q ∈ db.map f then 0 else 1) := by
          by_cases hq : q ∈ db.map f
          · have hq' : q ∈ db'.map f := by
              rcases List.mem_map.mp hq with ⟨d, hd, hfd⟩
              exact List.mem_map.mpr ⟨d, hmono d hd, hfd⟩
            simp [hq, hq']
          · by_cases hq' : q ∈ db'.map f <;> simp [hq, hq']
        have := ih htl
        omega

/-- The countdown is bounded by the fixed pool size, for every history. -/
theorem absentCount_le_length (f : Clause → Clause) (db pool : List Clause) :
    absentCount f db pool ≤ pool.length := by
  induction pool with
  | nil => simp [absentCount]
  | cons p ps ih =>
      simp only [absentCount, List.length_cons]
      split <;> omega

/-- The lexicographic order on the two-component measure: strictly smaller
first component, or equal first and strictly smaller second. -/
def LexLt (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Accessibility of a pair along the lex order (the double strong
recursion that `lexLt_wf` packages). -/
private theorem lexLt_acc : ∀ a b : Nat, Acc LexLt (a, b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a iha =>
    intro b
    induction b using Nat.strongRecOn with
    | ind b ihb =>
      apply Acc.intro
      intro q hq
      rcases q with ⟨x, y⟩
      unfold LexLt at hq
      rcases hq with hlt | ⟨heq, hlt2⟩
      · exact iha x hlt y
      · subst heq
        exact ihb y hlt2

/-- Well-foundedness of the two-component lex order (the pair form of the
`InvImage.wf` pattern used by `P3.phaseLt_wf` /
`ExtendedPoolRank.phaseRankSortedWith_wf`; proved here because the closed
build has no `Prod.lex_wf`). -/
theorem lexLt_wf : WellFounded LexLt :=
  ⟨fun p => lexLt_acc p.1 p.2⟩

/-- The two-component L1 measure: the history-keyed pool countdown and the
active length. The full L0 §5.1 measure puts S3's `restartBudget` above
this pair and the frontier/mass components below; the deletions and
insertions certified here are exactly the steps that pay in these two
components. -/
def Measure (P : Policy) (lc : Lifecycle) : Nat × Nat :=
  (absentCount P.f lc.history P.pool, activeLength lc)

/-- The re-keyed insertion guard (L0 §5.4): the clause is canonically NEW
relative to the certificate. A clause already in `history` — in particular
a deleted clause — fails this guard and must take the certified
chronological fallback instead of an insertion. -/
def GuardHistoryNovel (f : Clause → Clause) (lc : Lifecycle) (c : Clause) : Prop :=
  NovelWith f lc c

theorem guardHistoryNovel_iff_novelWith (f : Clause → Clause) (lc : Lifecycle)
    (c : Clause) : GuardHistoryNovel f lc c ↔ NovelWith f lc c :=
  Iff.rfl

/-- **THE INSERTION PAYMENT**: an admissible insertion — history-novel
clause whose canonical image is a fixed-pool member — strictly decreases
the history countdown. -/
theorem insert_absentCount_lt {P : Policy} {lc : Lifecycle} {c p : Clause}
    (hp : p ∈ P.pool) (hcanon : P.f c = p) (hnov : GuardHistoryNovel P.f lc c) :
    absentCount P.f (insert c lc).history P.pool <
      absentCount P.f lc.history P.pool := by
  have hnew : p ∈ (c :: lc.history).map P.f :=
    List.mem_map.mpr ⟨c, List.mem_cons_self .., hcanon⟩
  have hold : p ∉ lc.history.map P.f := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨d, hd, hfd⟩
    exact hnov (List.mem_map.mpr ⟨d, hd, hfd.trans hcanon.symm⟩)
  exact absentCount_lt_of_new_mem (f := P.f) (db := lc.history)
    (db' := c :: lc.history) (p := p) (pool := P.pool)
    (fun d hd => List.mem_cons_of_mem c hd) hp hnew hold

/-- One step of a certified reduction run: an eligible policy deletion, or
an admissible insertion (history-novel under the rank projection with the
inserted clause's canonical form a fixed-pool member). The `insert`
constructor is the formal shape the L0 §5.4 re-keyed guards must produce
at the runtime insertion sites; the `delete` constructor is the policy
restriction of `deleteEligible`. -/
inductive Step (P : Policy) (trail : List TrailEntry) : Lifecycle → Lifecycle → Prop where
  | delete {lc : Lifecycle} {c : Clause} (h : Eligible P trail lc c) :
      Step P trail lc (delete c lc)
  | insert {lc : Lifecycle} {c p : Clause} (hp : p ∈ P.pool)
      (hcanon : P.f c = p) (hnov : GuardHistoryNovel P.f lc c) :
      Step P trail lc (insert c lc)

/-- The bridge from the operation to the step relation: a policy deletion
is a `Step.delete`. -/
theorem deleteEligible_step {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    {c : Clause} (h : Eligible P trail lc c) :
    Step P trail lc (deleteEligible P trail lc c h) :=
  Step.delete h

/-- **EVERY ADMISSIBLE STEP PAYS**: a step strictly decreases the
two-component lex measure. Deletions pay in `activeLength` (the countdown
is untouched — the certificate absorbs deletion); insertions pay in the
countdown (relearning cannot mint progress because it is refused by
`GuardHistoryNovel`). -/
theorem step_measure_lt {P : Policy} {trail : List TrailEntry} {lc lc' : Lifecycle}
    (h : Step P trail lc lc') : LexLt (Measure P lc') (Measure P lc) := by
  cases h with
  | delete hele =>
      exact Or.inr ⟨rfl, activeLength_delete_lt hele.1⟩
  | insert hp hcanon hnov =>
      exact Or.inl (insert_absentCount_lt hp hcanon hnov)

/-- No function `Nat → α` can be strictly descending for a well-founded
relation. -/
theorem not_exists_descending {α : Type} {r : α → α → Prop} (h : WellFounded r) :
    ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n) := by
  rintro ⟨f, hf⟩
  suffices ∀ a, Acc r a → ¬ (∃ g : Nat → α, g 0 = a ∧ ∀ n, r (g (n + 1)) (g n)) by
    exact this (f 0) (h.apply (f 0)) ⟨f, rfl, hf⟩
  intro a ha
  induction ha with
  | intro _ hstep ih =>
    rintro ⟨g, hg0, hg⟩
    subst hg0
    exact ih (g 1) (hg 0) ⟨fun n => g (n + 1), rfl, fun n => hg (n + 1)⟩

/-- **NO INFINITE REDUCTION RUNS**: every sequence of policy steps
(eligible deletions and admissible history-novel pool insertions) is
finite — well-founded progress survives deletion and relearning. The
runtime obligation is exactly that the wired transitions are instances of
`Step` (`deleteEligible_step` for deletions; the re-keyed guards for
insertions). -/
theorem step_no_infinite (P : Policy) (trail : List TrailEntry) :
    ¬ ∃ l : Nat → Lifecycle, ∀ n, Step P trail (l n) (l (n + 1)) := by
  rintro ⟨l, hl⟩
  exact not_exists_descending (InvImage.wf (Measure P) lexLt_wf)
    ⟨l, fun n => step_measure_lt (hl n)⟩

/-- **THE REUSE/NEW-CLAUSE INTERACTION (L0 §5.4)**: a clause already
certified by `history` can never be the payload of an admissible
insertion, before or after any deletion of it (`canonSeenWith_delete`
keeps it seen). Re-deriving it must therefore take the certified
chronological fallback; with the old active-keyed guard it would look new
and the insertion would mint no countdown progress, breaking the
well-foundedness argument. -/
theorem relearn_after_delete_not_admissible {P : Policy} {lc : Lifecycle}
    {d c : Clause} (hseen : CanonSeenWith P.f lc c) :
    ¬ ∃ p : Clause, p ∈ P.pool ∧ P.f c = p ∧ GuardHistoryNovel P.f (delete d lc) c := by
  rintro ⟨p, -, -, hnov⟩
  exact hnov (canonSeenWith_delete P.f d lc hseen)

/-- Deletion leaves the countdown untouched (the certificate is
invariant): the first component of the measure is unchanged by
`deleteEligible`. -/
theorem deleteEligible_measure_fst (P : Policy) (trail : List TrailEntry)
    (lc : Lifecycle) (c : Clause) (h : Eligible P trail lc c) :
    (Measure P (deleteEligible P trail lc c h)).1 = (Measure P lc).1 :=
  rfl

/-! ## §8 Optimization reuse under the next bound

PLAN O1 / L0 §5.5 (S3 integration point): a branch-and-bound round may
reuse only the retained clauses entailed by the NEXT bound's leaf
semantics. `NextBoundEntailed` is that condition; the provable transport
is `nextBoundEntailed_of_leaf_mono` (tightened bound only: the next
bound's solutions are among the current round's). The exact missing
pieces, wired at the integration site:

  1. `hsub` — that the tightened bound's leaf solutions are a subset of
     the current round's. This holds for monotone tightening and MUST NOT
     be generalized to relaxed bounds (PLAN O1): a relaxed bound admits
     new solutions not covered by the current entailment.
  2. `hent` — the round-end entailment of the retained base
     (`Integration/OptimizeSeed.lean`'s `db_entailed`,
     `Integration/LcgSeed.lean`'s `lcgSolveDb_db_entailed`), available
     after the lifecycle→seed projection is wired into the round loop.
  3. the seed-transport side conditions (`SeedDb` canonical + aligned,
     `LcgSeedClauses.seedClauses_canonical`/`_aligned`) so the retained
     clauses re-enter the next round's `WellFormed` seed. -/

/-- The next-bound entailment condition: every retained clause is entailed
by the NEXT round's leaf semantics. -/
def NextBoundEntailed (leaf' : Assignment → Bool) (keep : List Clause) : Prop :=
  ∀ c ∈ keep, ∀ a, leaf' a = true → c.SatisfiedBy a

/-- The complete reuse contract stated as one proposition: next-round
leaves are among the current round's (monotone tightening), and the
retained base is entailed now. -/
def ReuseContract (leaf leaf' : Assignment → Bool) (keep : List Clause) : Prop :=
  (∀ a, leaf' a = true → leaf a = true) ∧ LearnedEntailed leaf keep

/-- **THE REUSE TRANSPORT**: under monotone tightening, current entailment
is next-bound entailment. -/
theorem nextBoundEntailed_of_leaf_mono {leaf leaf' : Assignment → Bool}
    {keep : List Clause} (hsub : ∀ a, leaf' a = true → leaf a = true)
    (hent : LearnedEntailed leaf keep) : NextBoundEntailed leaf' keep :=
  fun c hc a ha => hent c hc a (hsub a ha)

theorem nextBoundEntailed_of_reuseContract {leaf leaf' : Assignment → Bool}
    {keep : List Clause} (h : ReuseContract leaf leaf' keep) :
    NextBoundEntailed leaf' keep :=
  nextBoundEntailed_of_leaf_mono h.1 h.2

/-- **THE LIFECYCLE FORM**: if the active database (after any deletions)
is entailed now, it is entailed under the next bound — the exact condition
under which the retained clauses of a reduced database may be reused. -/
theorem nextBoundEntailed_active_of_leaf_mono {leaf leaf' : Assignment → Bool}
    {seed : List Clause} {lc : Lifecycle} (hw : WellFormed leaf seed lc)
    (hsub : ∀ a, leaf' a = true → leaf a = true) :
    NextBoundEntailed leaf' lc.active :=
  nextBoundEntailed_of_leaf_mono hsub (wellFormed_active_entailed hw)

/-- The reduced database inherits the next-bound reuse condition (deletion
only shrinks the quantified list). -/
theorem nextBoundEntailed_reduce_of_leaf_mono {leaf leaf' : Assignment → Bool}
    {seed : List Clause} {P : Policy} {trail : List TrailEntry} {lc : Lifecycle}
    (hw : WellFormed leaf seed lc)
    (hsub : ∀ a, leaf' a = true → leaf a = true) :
    NextBoundEntailed leaf' (reduce P trail lc).active :=
  nextBoundEntailed_of_leaf_mono hsub
    (wellFormed_active_entailed (reduce_wellFormed hw))

end LeanFzn.Solver.Propagation.ClauseReduction
