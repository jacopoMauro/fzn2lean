/-
File: LeanFzn/Solver/Propagation/ClauseLifecycle.lean

Purpose (PLAN.md task L0, prerequisites of L1 deletion and S3 restarts):

  A STANDALONE, FROZEN lifecycle vocabulary separating the ACTIVE clause
  database (search data: the list the scans, watches and value-satisfaction
  arguments read) from the persistent HISTORY certificate (every clause
  ever inserted). Deletion and root restoration shrink/rebuild `active`;
  `history` only grows. The two projections and their structural laws are
  the interface L1/S3 code against; the semantic obligations are `Prop`
  definitions here and are proved at the integration site.

  Why a separate history is needed. The existing progress rank
  (`LeanFzn.Solver.UIP.Proofs.SchedulerRank.PhaseRank`,
  `.../SchedulerJumpProgress.PhaseRankSorted`,
  `.../ExtendedPoolRank.PhaseRankSortedWith`) is a lexicographic tuple
  whose most significant component is a COUNTDOWN over a FIXED clause pool
  (`P3.absentCount` / `P3.absentCountMap`), read from `cfg.branch.learned`.
  Monotone database growth is what makes every insertion non-increasing
  (`P3.absentCount_mono`) and every genuinely new pool clause strictly
  decreasing (`P3.absentCountMap_lt_of_mono_mem`). Deletion breaks that
  monotonicity of the measured list; a restart that drops clauses breaks
  it too. REUSE DECISION (no new measure, no duplicated count): the
  countdown of `P3.absentCount` is already parametric in its database
  argument, so L1/S3 read it at `lc.history` instead of
  `cfg.branch.learned`: deletion and restoration leave `history`
  untouched, and only `insert` extends it. This module supplies exactly
  the history-side structural laws that instantiation needs
  (`HistoryGrowth`, `CanonSeen`, `activeInHistory`), so the rank proofs
  are re-keyed, not re-invented.

  Clause roles (audit companion `L0-clause-lifecycle.md`, repo root):
  a clause can simultaneously be search data, a locked reason, an
  original/seed clause, an optimization seed, and a progress witness.
  `ClauseRole` names the five roles the audit distinguishes;
  `roleProtected` records the default deletion-protection map: originals,
  locked reasons and optimization seeds must stay active, while progress
  witnesses are carried by `history` (not by `active`) and need no
  active protection.

  Honest scope: this module fixes vocabulary and proves only structural
  list/set laws. It does NOT wire any runtime transition and does NOT
  claim well-foundedness of a deletion-enabled run: that is the L1/S3
  proof plan recorded in `L0-clause-lifecycle.md`, whose obligations are
  named as `Prop`s here (`WellFormed`, `DeleteEligible`, `LockedReasons`,
  `KeyCertificate`) and consumed at the integration site.

Dependencies: LeanFzn.Solver.Propagation.BranchState (`Clause`, `Literal.norm`,
`LearnedEntailed`) only. No runtime module is edited; no `sorry`, no axiom.
-/

import LeanFzn.Legacy.Solver.Propagation.BranchState

set_option autoImplicit false

namespace LeanFzn.Solver.Propagation.ClauseLifecycle
open LeanFzn.Semantics

/-! ## §1 Clause roles -/

/-- The roles a learned/stored clause can play. The list is exhaustive for
the audit in `L0-clause-lifecycle.md`: semantic search data (scanned /
watched / used in satisfaction arguments), locked reason (the `Reason` of a
live trail or checkpoint entry), original constraint (the `original` clause
base seeded into `SchedulerConfig.init`), optimization seed (a `SeedDb`
carried across branch-and-bound rounds) and progress witness (a pool clause
counted by the `PhaseRank` countdown component). -/
inductive ClauseRole where
  | searchData
  | lockedReason
  | original
  | optimizationSeed
  | progressWitness
  deriving DecidableEq, Repr

/-- Default deletion-protection map. `true` means the role must remain in
`active` under every deletion policy: originals (coverage/seed arguments),
locked reasons (reason availability of live entries) and optimization seeds
(the next round's re-entry clauses). `false` means the history certificate
carries the clause's obligations: `progressWitness` clauses are remembered
by `history` even after `delete`, and plain `searchData` clauses are
disposable by construction. The concrete policy may refine this map; the
lifecycle laws below do not depend on it. -/
def roleProtected : ClauseRole → Bool
  | .searchData => false
  | .lockedReason => true
  | .original => true
  | .optimizationSeed => true
  | .progressWitness => false

/-! ## §2 The lifecycle record and its operations -/

/-- The two projections of clause life: `active` is the semantic search
database (what every scan/watch/satisfaction consumer reads); `history`
records every clause that was ever inserted, newest first, and only grows.
Both are plain clause lists so that the existing consumers
(`scanDatabase`, `nextPruningEvent`, `CoversRemainingLeaves`,
`P3.absentCount`) accept them unchanged. -/
structure Lifecycle where
  /-- the active clause database (search data) -/
  active : List Clause
  /-- every clause ever inserted, newest first; never shrinks -/
  history : List Clause
  deriving Repr

namespace Lifecycle

/-- The empty lifecycle. -/
def empty : Lifecycle := { active := [], history := [] }

/-- Insertion (learn, propagate-deduction, local-exclude payload, seed
re-entry): the clause joins search data AND the history. It is the only
operation that extends `history`. -/
def insert (c : Clause) (lc : Lifecycle) : Lifecycle :=
  { active := c :: lc.active, history := c :: lc.history }

/-- Deletion from search data only: `history` is untouched, so every
obligation carried by the certificate (novelty/seen facts, rank countdown)
survives the deletion. -/
def delete (c : Clause) (lc : Lifecycle) : Lifecycle :=
  { active := lc.active.erase c, history := lc.history }

/-- Root restoration (S3) with an already-certified retained seed: the
active set becomes `seed`, the history is kept. Callers that retain a
clause not yet in `history` must use `restart` (or `replay`) instead, which
certifies it. -/
def restore (seed : List Clause) (lc : Lifecycle) : Lifecycle :=
  { active := seed, history := lc.history }

/-- Replay a batch of clauses as insertions (newest-first). Used for
re-inserting retained clauses after a deletion or for a restarted round. -/
def replay (cs : List Clause) (lc : Lifecycle) : Lifecycle :=
  cs.foldl (fun acc c => acc.insert c) lc

/-- Root restart (S3): the active set is rebuilt from `seed`, and every seed
clause is certified in the same step (unlike `restore`, which assumes
certification). `history` only grows, so retained-clause obligations are
automatic. -/
def restart (seed : List Clause) (lc : Lifecycle) : Lifecycle :=
  replay seed { active := [], history := lc.history }

@[simp] theorem insert_active (c : Clause) (lc : Lifecycle) :
    (insert c lc).active = c :: lc.active := rfl

@[simp] theorem insert_history (c : Clause) (lc : Lifecycle) :
    (insert c lc).history = c :: lc.history := rfl

@[simp] theorem delete_active (c : Clause) (lc : Lifecycle) :
    (delete c lc).active = lc.active.erase c := rfl

@[simp] theorem delete_history (c : Clause) (lc : Lifecycle) :
    (delete c lc).history = lc.history := rfl

@[simp] theorem restore_active (seed : List Clause) (lc : Lifecycle) :
    (restore seed lc).active = seed := rfl

@[simp] theorem restore_history (seed : List Clause) (lc : Lifecycle) :
    (restore seed lc).history = lc.history := rfl

@[simp] theorem empty_active : (empty).active = [] := rfl

@[simp] theorem empty_history : (empty).history = [] := rfl

/-- The batch history of `replay`: the replayed clauses in reverse order,
followed by the old history. -/
theorem replay_history (cs : List Clause) (lc : Lifecycle) :
    (replay cs lc).history = cs.reverse ++ lc.history := by
  induction cs generalizing lc with
  | nil => rfl
  | cons c cs ih =>
      rw [replay, List.foldl_cons]
      change (replay cs (insert c lc)).history = (c :: cs).reverse ++ lc.history
      rw [ih, insert_history, List.reverse_cons, List.append_assoc,
        List.singleton_append]

/-- The restart history: the seed in reverse order, followed by the old
history. -/
theorem restart_history (seed : List Clause) (lc : Lifecycle) :
    (restart seed lc).history = seed.reverse ++ lc.history := by
  unfold restart
  exact replay_history seed { active := [], history := lc.history }

/-! ## §3 History monotonicity (the certificate never shrinks) -/

/-- `HistoryGrowth lc lc'`: every clause certified by `lc` is still
certified by `lc'`. This is the order that every operation respects and
that the countdown instantiation consumes (it is the `hmono` premise of
`P3.absentCount_mono` / `P3.absentCountMap_lt_of_mono_mem` at
`db := lc.history`). -/
def HistoryGrowth (lc lc' : Lifecycle) : Prop :=
  ∀ c ∈ lc.history, c ∈ lc'.history

theorem historyGrowth_refl (lc : Lifecycle) : HistoryGrowth lc lc :=
  fun _ h => h

theorem historyGrowth_trans {lc lc' lc'' : Lifecycle}
    (h : HistoryGrowth lc lc') (h' : HistoryGrowth lc' lc'') :
    HistoryGrowth lc lc'' :=
  fun c hc => h' c (h c hc)

theorem historyGrowth_insert (c : Clause) (lc : Lifecycle) :
    HistoryGrowth lc (insert c lc) :=
  fun _ hd => List.mem_cons_of_mem _ hd

theorem historyGrowth_delete (c : Clause) (lc : Lifecycle) :
    HistoryGrowth lc (delete c lc) :=
  fun _ h => h

theorem historyGrowth_restore (seed : List Clause) (lc : Lifecycle) :
    HistoryGrowth lc (restore seed lc) :=
  fun _ h => h

theorem historyGrowth_replay (cs : List Clause) (lc : Lifecycle) :
    HistoryGrowth lc (replay cs lc) := by
  induction cs generalizing lc with
  | nil => exact historyGrowth_refl lc
  | cons c cs ih =>
      rw [replay, List.foldl_cons]
      exact historyGrowth_trans (historyGrowth_insert c lc) (ih (insert c lc))

theorem historyGrowth_restart (seed : List Clause) (lc : Lifecycle) :
    HistoryGrowth lc (restart seed lc) := by
  intro c hc
  exact historyGrowth_replay seed { active := [], history := lc.history } c hc

/-- Insertion growth only: `HistoryGrowth` of `insert` with the inserted
clause named (the shape a rank step consumes when it knows the new entry). -/
theorem mem_insert_history (c : Clause) (lc : Lifecycle) :
    c ∈ (insert c lc).history :=
  List.mem_cons_self ..

/-! ## §3b Active is a sublist of the certificate (the deletion-count bound)

`activeLength := lc.active.length` is the component that strictly decreases on
a deletion step of the frozen L1 measure (see `L0-clause-lifecycle.md` §5).
Under the `ActiveSublist` discipline its value is bounded by the certificate
length, so the number of deletions between two history-growing steps is
finite. `insert` preserves the discipline with `cons_cons`; `delete` with
`List.erase_sublist`; replay/restart by induction. -/

/-- Active clauses occur in the certificate in order (the discipline that
makes `activeLength` certificate-bounded). Every operation preserves it. -/
def ActiveSublist (lc : Lifecycle) : Prop := List.Sublist lc.active lc.history

theorem activeSublist_empty : ActiveSublist empty :=
  List.nil_sublist _

theorem activeSublist_insert {lc : Lifecycle} {c : Clause}
    (h : ActiveSublist lc) : ActiveSublist (insert c lc) :=
  List.Sublist.cons_cons c (show List.Sublist lc.active lc.history from h)

theorem activeSublist_delete {lc : Lifecycle} {c : Clause}
    (h : ActiveSublist lc) : ActiveSublist (delete c lc) := by
  show List.Sublist (lc.active.erase c) lc.history
  exact List.erase_sublist.trans (show List.Sublist lc.active lc.history from h)

theorem activeSublist_replay (cs : List Clause) {lc : Lifecycle}
    (h : ActiveSublist lc) : ActiveSublist (replay cs lc) := by
  induction cs generalizing lc with
  | nil => exact h
  | cons c cs ih =>
      rw [replay, List.foldl_cons]
      exact ih (activeSublist_insert h)

theorem activeSublist_restart (seed : List Clause) (lc : Lifecycle) :
    ActiveSublist (restart seed lc) := by
  unfold restart
  exact activeSublist_replay seed (lc := { active := [], history := lc.history })
    (List.nil_sublist _)

/-- The size component of the deletion step's strict decrease. -/
def activeLength (lc : Lifecycle) : Nat := lc.active.length

/-- Under the sublist discipline, `activeLength` is bounded by the
certificate length: no deletion can occur more often than that between two
history-growing steps. -/
theorem activeLength_le_historyLength {lc : Lifecycle}
    (h : ActiveSublist lc) : lc.active.length ≤ lc.history.length :=
  List.Sublist.length_le (show List.Sublist lc.active lc.history from h)

private theorem erase_length_lt_of_mem {c : Clause} :
    ∀ {l : List Clause}, c ∈ l → (l.erase c).length < l.length
  | [], h => by cases h
  | d :: ds, h => by
      rw [List.erase_cons]
      by_cases hdc : d = c
      · rw [if_pos (by simpa [beq_iff_eq] using hdc)]
        simp
      · rw [if_neg (by simpa [beq_iff_eq] using hdc)]
        simp only [List.length_cons]
        have hmem : c ∈ ds := by
          rcases List.mem_cons.mp h with heq | hmem
          · exact absurd heq.symm hdc
          · exact hmem
        have := erase_length_lt_of_mem hmem
        omega

/-- A deletion step strictly decreases `activeLength` as soon as the deleted
clause is active — the L1 deletion-step rank decrease. -/
theorem activeLength_delete_lt {lc : Lifecycle} {c : Clause}
    (h : c ∈ lc.active) : (delete c lc).active.length < lc.active.length :=
  erase_length_lt_of_mem h

/-- An insertion step increases `activeLength` — which is why the frozen
measure puts the certificate countdown ABOVE it: only history-novel
insertions may occur, and they strictly decrease the countdown. -/
theorem activeLength_insert (c : Clause) (lc : Lifecycle) :
    lc.active.length < (insert c lc).active.length := by
  simp [insert]

/-! ## §4 Active clauses are certified (`active ⊆ history`) -/

/-- Structural well-formedness of a lifecycle: every active clause is
already certified. `insert` maintains it, `delete` shrinks the left side,
and `restart` re-certifies its seed. This is the purely structural half of
the semantic `WellFormed` below. -/
def ActiveInHistory (lc : Lifecycle) : Prop :=
  ∀ c ∈ lc.active, c ∈ lc.history

theorem activeInHistory_empty : ActiveInHistory empty :=
  fun _ h => by cases h

theorem activeInHistory_insert {lc : Lifecycle} {c : Clause}
    (h : ActiveInHistory lc) : ActiveInHistory (insert c lc) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h d hd)

theorem activeInHistory_delete {lc : Lifecycle} {c : Clause}
    (h : ActiveInHistory lc) : ActiveInHistory (delete c lc) :=
  fun d hd => h d (List.mem_of_mem_erase hd)

theorem activeInHistory_restore {lc : Lifecycle} {seed : List Clause}
    (hseed : ∀ c ∈ seed, c ∈ lc.history) : ActiveInHistory (restore seed lc) :=
  fun _ hd => hseed _ hd

theorem activeInHistory_replay (cs : List Clause) {lc : Lifecycle}
    (h : ActiveInHistory lc) : ActiveInHistory (replay cs lc) := by
  induction cs generalizing lc with
  | nil => exact h
  | cons c cs ih =>
      rw [replay, List.foldl_cons]
      exact ih (activeInHistory_insert h)

/-- A restart needs no certification premise: the seed is replayed into the
history in the same operation. -/
theorem activeInHistory_restart (seed : List Clause) (lc : Lifecycle) :
    ActiveInHistory (restart seed lc) := by
  unfold restart
  exact activeInHistory_replay seed (lc := { active := [], history := lc.history })
    (fun _ hd => by cases hd)

/-! ## §5 Semantic well-formedness (seed + history entailment) -/

/-- The semantic lifecycle predicate: every active clause is either a seed
clause or certified, and both the seed and the certificate are entailed by
the leaf. `LearnedEntailed` is the existing entailment vocabulary
(`BranchState.lean`), so this is the same obligation the run invariants
(`LcgRunState.core.reach.learned_ent`) already use. -/
def WellFormed (leaf : LeanFzn.Solver.Core.Assignment → Bool) (seed : List Clause)
    (lc : Lifecycle) : Prop :=
  (∀ c ∈ lc.active, c ∈ seed ∨ c ∈ lc.history) ∧
    LearnedEntailed leaf seed ∧ LearnedEntailed leaf lc.history

/-- Every active clause is entailed — the `LearnedEntailed` fact the scans,
satisfaction arguments and coverage statements consume, derived from
seed+history entailment without any monotonicity of `active`. -/
theorem wellFormed_active_entailed {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    {seed : List Clause} {lc : Lifecycle} (h : WellFormed leaf seed lc) :
    LearnedEntailed leaf lc.active := by
  intro c hc a ha
  rcases h.1 c hc with hs | hh
  · exact h.2.1 c hs a ha
  · exact h.2.2 c hh a ha

theorem wellFormed_empty {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    (h : LearnedEntailed leaf seed) : WellFormed leaf seed empty :=
  ⟨(fun _ hc => by cases hc), h, (fun _ hc => by cases hc)⟩

/-- Insertion preserves well-formedness when the inserted clause is
entailed (the producer obligations of every real insertion site:
propagation deductions, jump analyses, local-exclude payloads). -/
theorem wellFormed_insert {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    {lc : Lifecycle} (h : WellFormed leaf seed lc) {c : Clause}
    (hc : ∀ a, leaf a = true → c.SatisfiedBy a) :
    WellFormed leaf seed (insert c lc) := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Or.inr (List.mem_cons_self ..)
    · rcases h.1 d hd with hs | hh
      · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem _ hh)
  · intro d hd a ha
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc a ha
    · exact h.2.2 d hd a ha

/-- Deletion preserves well-formedness unconditionally: the seed and the
history are untouched and `active` shrinks. This is the L1 database-
entailment obligation in its strongest form. -/
theorem wellFormed_delete {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    {lc : Lifecycle} (h : WellFormed leaf seed lc) (c : Clause) :
    WellFormed leaf seed (delete c lc) := by
  refine ⟨?_, h.2⟩
  intro d hd
  exact h.1 d (List.mem_of_mem_erase hd)

/-- Restoring an already-certified seed preserves well-formedness (the
history is untouched and every seed clause is trivially a seed clause). -/
theorem wellFormed_restore {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    {lc : Lifecycle} (h : WellFormed leaf seed lc) :
    WellFormed leaf seed (restore seed lc) :=
  ⟨fun _ hd => Or.inl hd, h.2⟩

/-- Replaying entailed clauses preserves well-formedness (each replayed
clause is certified by `insert` in the same step). -/
theorem wellFormed_replay {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    {lc : Lifecycle} (h : WellFormed leaf seed lc) {cs : List Clause}
    (hcs : ∀ c ∈ cs, ∀ a, leaf a = true → c.SatisfiedBy a) :
    WellFormed leaf seed (replay cs lc) := by
  induction cs generalizing lc with
  | nil => exact h
  | cons c cs ih =>
      rw [replay, List.foldl_cons]
      refine ih (wellFormed_insert h (hcs c (List.mem_cons_self ..))) ?_
      intro d hd
      exact hcs d (List.mem_cons_of_mem _ hd)

/-- A restart of entailed seed clauses produces a well-formed lifecycle from
any well-formed one. -/
theorem wellFormed_restart {leaf : LeanFzn.Solver.Core.Assignment → Bool} {seed : List Clause}
    {lc : Lifecycle} (h : WellFormed leaf seed lc)
    (hseed : ∀ c ∈ seed, ∀ a, leaf a = true → c.SatisfiedBy a) :
    WellFormed leaf seed (restart seed lc) := by
  unfold restart
  refine wellFormed_replay (lc := { active := [], history := lc.history })
    ⟨?_, h.2.1, h.2.2⟩ hseed
  intro c hc
  cases hc

/-! ## §6 Novelty: canonical presence in the certificate -/

/-- Literal-wise normalization of a clause. Definitionally the existing
`Clause.canonicalClause` (`Proofs/SchedulerVocabulary`); restated here so
this module's import cone stays at `BranchState` (the audit records the
definitional bridge instead of importing the rank stack). -/
def Fingerprint (c : Clause) : Clause := c.map Literal.norm

/-- Canonical presence under an ARBITRARY canonical projection `f`: the
image `f c` occurs among the images of the certificate. This is exactly the
membership `f c ∈ P3.canonicalDBMap f lc.history` tested by P3's
`absentCountMap`, so the L1 re-keying instantiates `f` from the existing
rank machinery: `f := Clause.canonicalClause` for `P3.PhaseRank`,
`f := canonicalSorted orig` for `P4.PhaseRankSorted`, and
`f := canonicalSortedWith extra orig` for
`ExtendedPoolRank.PhaseRankSortedWith`. -/
def CanonSeenWith (f : Clause → Clause) (lc : Lifecycle) (c : Clause) : Prop :=
  f c ∈ lc.history.map f

/-- The default projection is literal normalization (definitionally
`Clause.canonicalClause`). -/
abbrev CanonSeen (lc : Lifecycle) (c : Clause) : Prop :=
  CanonSeenWith Fingerprint lc c

/-- The inserted clause is immediately canonically seen — the strict
countdown flip of a genuinely new insertion. -/
theorem canonSeenWith_insert_self (f : Clause → Clause) (c : Clause)
    (lc : Lifecycle) : CanonSeenWith f (insert c lc) c :=
  List.mem_cons_self ..

theorem canonSeen_insert_self (c : Clause) (lc : Lifecycle) :
    CanonSeen (insert c lc) c :=
  canonSeenWith_insert_self Fingerprint c lc

/-- Canonical presence transfers along history growth. -/
theorem canonSeenWith_mono (f : Clause → Clause) {lc lc' : Lifecycle}
    (h : HistoryGrowth lc lc') {c : Clause} (hc : CanonSeenWith f lc c) :
    CanonSeenWith f lc' c := by
  obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hc
  exact List.mem_map.mpr ⟨d, h d hd, hdeq⟩

theorem canonSeen_mono {lc lc' : Lifecycle} (h : HistoryGrowth lc lc')
    {c : Clause} (hc : CanonSeen lc c) : CanonSeen lc' c :=
  canonSeenWith_mono Fingerprint h hc

/-- Deleting any clause preserves canonical presence: the certificate is
untouched. This is the exported fact L1 uses to show that deletion cannot
undo a consumed progress witness. -/
theorem canonSeenWith_delete (f : Clause → Clause) (d : Clause)
    (lc : Lifecycle) {c : Clause} (hc : CanonSeenWith f lc c) :
    CanonSeenWith f (delete d lc) c :=
  canonSeenWith_mono f (historyGrowth_delete d lc) hc

theorem canonSeen_delete (d : Clause) (lc : Lifecycle) {c : Clause}
    (hc : CanonSeen lc c) : CanonSeen (delete d lc) c :=
  canonSeenWith_delete Fingerprint d lc hc

/-- A clause whose canonical form already occurs in the certificate is not "new". -/
def NovelWith (f : Clause → Clause) (lc : Lifecycle) (c : Clause) : Prop :=
  ¬ CanonSeenWith f lc c

abbrev Novel (lc : Lifecycle) (c : Clause) : Prop := NovelWith Fingerprint lc c

theorem novelWith_of_not_canonSeenWith {f : Clause → Clause} {lc : Lifecycle}
    {c : Clause} (h : ¬ CanonSeenWith f lc c) : NovelWith f lc c := h

theorem not_canonSeenWith_of_novelWith {f : Clause → Clause} {lc : Lifecycle}
    {c : Clause} (h : NovelWith f lc c) : ¬ CanonSeenWith f lc c := h

/-- Novelty is anti-monotone along history growth: if `c` is still novel
after growth, it was already novel before (contrapositive of
`canonSeenWith_mono`; the direction under which the rank's strict countdown
survives growth). -/
theorem novelWith_of_mono (f : Clause → Clause) {lc lc' : Lifecycle}
    (h : HistoryGrowth lc lc') {c : Clause} (hn : NovelWith f lc' c) :
    NovelWith f lc c :=
  fun hc => hn (canonSeenWith_mono f h hc)

/-- Deleting a clause keeps every other clause's novelty. -/
theorem novelWith_delete (f : Clause → Clause) (d : Clause) (lc : Lifecycle)
    {c : Clause} (hn : NovelWith f lc c) : NovelWith f (delete d lc) c :=
  fun hc => hn (canonSeenWith_delete f d lc hc)

end Lifecycle

/-! ## §7 The keyed/hash certificate (what an exact-form history avoids)

`Lifecycle.history` is an exact-form list, so no injectivity obligation is
needed. A memory-optimized variant that stores only `Nat` fingerprints must
discharge `KeyInjectiveOn`; the theorem below is the exact place where that
obligation enters, and the audit (`L0-clause-lifecycle.md`) shows the
obligation is not currently proved for any compression function, which is
why the frozen default is the exact-form history. -/

namespace Lifecycle

/-- The key projection of the certificate under a canonical projection `f`:
one `Nat` per certified clause, computed from its canonical image. -/
def keysWith (f : Clause → Clause) (key : Clause → Nat) (lc : Lifecycle) :
    List Nat :=
  lc.history.map fun c => key (f c)

/-- The default key projection (literal normalization). -/
abbrev keys (key : Clause → Nat) (lc : Lifecycle) : List Nat :=
  keysWith Fingerprint key lc

/-- Injectivity of a keying function on a clause list: the extra obligation
a hash-like certificate must prove before keys may replace exact forms. -/
def KeyInjectiveOn (key : Clause → Nat) (s : List Clause) : Prop :=
  ∀ c ∈ s, ∀ d ∈ s, key c = key d → c = d

/-- The key-certificate soundness proposition: key membership reflects
canonical presence of the exact clause. -/
def KeyCertificateWith (f : Clause → Clause) (key : Clause → Nat)
    (lc : Lifecycle) : Prop :=
  ∀ c : Clause, key (f c) ∈ keysWith f key lc → CanonSeenWith f lc c

/-- The default key certificate (literal normalization). -/
abbrev KeyCertificate (key : Clause → Nat) (lc : Lifecycle) : Prop :=
  KeyCertificateWith Fingerprint key lc

/-- **THE INJECTIVITY OBLIGATION SUPPLIES THE CERTIFICATE**: with `key`
injective on the canonical forms of the history plus the queried clause,
key membership implies canonical presence — a hash certificate therefore
needs exactly this proof (the audit records that no such proof exists for a
compressing hash). -/
theorem canonSeenWith_of_key_mem {f : Clause → Clause} {key : Clause → Nat}
    {lc : Lifecycle} {c : Clause}
    (hinj : KeyInjectiveOn key (f c :: lc.history.map f))
    (hmem : key (f c) ∈ keysWith f key lc) : CanonSeenWith f lc c := by
  obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hmem
  have heq : f c = f d :=
    hinj (f c) (List.mem_cons_self ..) (f d)
      (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := f) hd)) hdeq.symm
  show f c ∈ lc.history.map f
  rw [heq]
  exact List.mem_map_of_mem (f := f) hd

/-- Exact-form membership is the certificate's definition: no injectivity
needed for the default representation. -/
theorem canonSeen_iff_mem (lc : Lifecycle) (c : Clause) :
    CanonSeen lc c ↔ ∃ d ∈ lc.history, Fingerprint d = Fingerprint c :=
  List.mem_map

end Lifecycle

/-! ## §8 Locked reasons (L1 reason availability) -/

namespace Lifecycle

/-- The clauses attached as reasons to the entries of a trail. -/
def liveReasons (trail : List TrailEntry) : List Clause :=
  trail.filterMap fun e => e.reason.map Reason.clause

/-- Reason availability: every live reason clause is still active. This is
the L1 obligation a deletion must preserve so that trail entries (and any
later analysis) can still cite their reason clauses. Deleting a clause that
is NOT a live reason preserves the predicate. -/
def LockedReasons (lc : Lifecycle) (trail : List TrailEntry) : Prop :=
  ∀ c ∈ liveReasons trail, c ∈ lc.active

/-- Deleting a non-reason clause keeps every live reason active. -/
theorem lockedReasons_delete {lc : Lifecycle} {trail : List TrailEntry}
    (h : LockedReasons lc trail) {c : Clause}
    (hc : c ∉ liveReasons trail) : LockedReasons (delete c lc) trail := by
  intro d hd
  rw [delete_active]
  by_cases hdc : d = c
  · subst hdc
    exact absurd hd hc
  · exact (List.mem_erase_of_ne hdc).mpr (h d hd)

/-- Insertion keeps every live reason active (reasons are active by
hypothesis; the new clause is added on top). -/
theorem lockedReasons_insert {lc : Lifecycle} {trail : List TrailEntry}
    (h : LockedReasons lc trail) (c : Clause) :
    LockedReasons (insert c lc) trail :=
  fun d hd => List.mem_cons_of_mem _ (h d hd)

/-- A restart to a seed that contains every live reason keeps reason
availability (S3 form). -/
theorem lockedReasons_restore {lc : Lifecycle} {trail : List TrailEntry}
    {seed : List Clause} (hseed : ∀ c ∈ liveReasons trail, c ∈ seed) :
    LockedReasons (restore seed lc) trail :=
  fun _ hd => hseed _ hd

end Lifecycle

/-! ## §9 Deletion eligibility -/

namespace Lifecycle

/-- Deletion eligibility, parameterized by the caller's live protection set
`keep` (original/seed clauses, live reason clauses, optimization seeds the
round still needs). The structural lifecycle laws do not depend on the
choice of `keep`; a deletion step may only remove an eligible clause. The
default role map is `roleProtected`. -/
def DeleteEligible (keep : List Clause) (lc : Lifecycle) (c : Clause) : Prop :=
  c ∈ lc.active ∧ c ∉ keep

/-- The one structural consequence eligibility adds: the certificate is
untouched, so every history-side obligation (novelty, countdown, growth,
entailment) survives any eligible deletion — see `canonSeen_delete`,
`wellFormed_delete`, `lockedReasons_delete` for the consumer forms. -/
theorem deleteEligible_history {keep : List Clause} {lc : Lifecycle}
    {c : Clause} (_h : DeleteEligible keep lc c) :
    (delete c lc).history = lc.history := rfl

end Lifecycle

end LeanFzn.Solver.Propagation.ClauseLifecycle
