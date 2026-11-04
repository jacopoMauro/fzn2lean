/-
File: LeanFzn/Solver/Propagation/ScheduledPropagation.lean

Purpose (PLAN tasks P1 + P2): INCREMENTAL PROPAGATOR SCHEDULING with a proved
REFINEMENT theorem. The full scan `scanPropagators` re-runs every registered
propagator at every propagation step; the scheduled scan
`scanPropagatorsSched` memorizes, per propagator, the WATCH PROJECTION of the
frame together with the result the run produced there, and re-uses the
memorized result while the projection is unchanged — re-running the
propagator only when one of its watched slots changed.

P2 (version-keyed stamps): the reuse decision is O(1) per memorized entry and
does NOT compare domain contents. The scheduler carries a per-slot counter
vector `versions` (`SchedVersions`, the local twin of `SlotVersions`, aligned
with `Frame.domains`) together with the frame `vframe` at which it was taken.
At every scheduled scan the vector is bumped by `sVersionBumpAll` over
`frameChanged vframe f` (the local twin of the frozen E0 extraction
`frameEvents`); an entry survives the sync only
when the version counters at its watched slots did not move. `domain_eq_of_
version_eq` then proves that the slot domains (hence the watch projection)
are unchanged, so the old result stays exact. Entries whose watched version
moved are dropped (monotone counters: they can never become reusable again),
and the propagator is re-run and re-recorded. The domain projection stored in
each entry is PROOF-ONLY: the scan never compares it, `EntryOK` uses it to
transport the recording frame's run to every frame with that projection via
the static locality hypothesis `PropLocal`.

The equivalence is a REFINEMENT, not a weakening:

* `scanPropagatorsSched_fst_eq` — the scheduled scan produces EXACTLY the
  same `PruningEvent` as the full `scanPropagators` (same list, same order,
  same early exit), provided the memorized table is consistent
  (`PropSchedulerOK`).
* `scanPropagatorsSched_OK` — the table stays consistent across scans: a
  version-synced entry is justified by `domain_eq_of_version_eq` and the
  static per-propagator locality hypothesis `PropLocal`, which the concrete
  LCG registrations discharge in `ScheduledFamilies.lean`.
* `nextPruningEventSched_fst_eq` — the event-selection entry point
  (`scanDatabase` unchanged, the same liveness gates) agrees with the
  certified `nextPruningEvent` under the same table consistency.

History: P1 keyed the table by the CONTENT of the watched slots. P2 replaces
the hot-path content compare (`stampEqB`, O(domain size) per watched slot)
by the per-slot version compare (`stampNatEqB` on `watchVersions`, O(1) per
watched slot). The content-projection functions remain for the legacy
counting twin (the retired SchedCounts diagnostic); the wired path uses
`watchVersions`. The version vector and the changed-slot extraction are
restated locally (`SchedVersions`, `frameChanged`) instead of importing
`SlotVersions`, which sits ABOVE this module (`ScheduledFamilies ->
EventContract -> SlotVersions`); the local twins carry the same semantics
and the two soundness lemmas the sync consumes, and they avoid paying for
the full event-kind extraction on the hot path.

The watched-clause index (`ClauseWatch.lean`, PLAN task W1) is NOT wired
here. Four measured iterations settled it: the original guard (`decide
(idx.db = db)`) cost 1362 ms on FBDk04 against an 819 ms whole oracle; the
corrected slot-entry scheme kept the O(|db|) guard; the self-validating
entry scheme (`WatchEntry` = positions + literals, skip re-checked against
the clause and the current frame via `literalImpossibleFast`) removed the
guard entirely (setup 4 ms) and lifted the FBDk04 skip rate to 94% (12.95M
skips, 155k rechecks), yet the watched scan still measures 1966-2044 ms vs
the oracle's 816-847 ms on FBDk04 and 187-206 ms vs 20-22 ms on the
43-instance battery; the PLAN §3.4 version-keyed scheme (`VersionWatch.lean`,
SlotVersions discipline, prepend-aligned entries, generation + two version
stamps, summary refresh on a moved stamp) measures 1349-1380 ms vs 899-932 ms
on FBDk04 and 25 ms vs 14-15 ms on the battery, 0 event disagreements. The
residual blocker is per-clause bookkeeping (entry-list rebuild plus the
second first-two pass on reclassified clauses), not invalidation. The module
and its equality `scanDatabaseWatch2_fst_eq`/`scanDatabaseWatchV_fst_eq`
remain proved and retained unwired; the wired database scan stays
`scanDatabaseFast`.

Dependencies: Pruning/Propagate (the scan and the propagator interface),
`LeanFzn.Semantics.ValueEquality` (sound Boolean value equality — `Value`
has no `DecidableEq`).

DAG: Pruning -> ScheduledPropagation -> ScheduledFamilies (concrete
locality) -> EventContract -> SlotVersions -> the certified runtime driver.
-/
import LeanFzn.Legacy.Solver.Propagation.Pruning
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Legacy.Solver.Propagation.DbScanIndex
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch
import LeanFzn.Semantics.ValueEquality
open LeanFzn.Semantics LeanFzn.Solver.Core


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Watch projections -/

/-- The watch projection of a frame: the current domain of every watched
slot, in watch order. Only `.slot` of a watch atom is read. -/
def watchStamp (f : BranchFrame) (watches : List Atom) : List Domain :=
  watches.map fun a => (Frame.domains f).getD a.slot Dom.empty

/-- Computable equality of watch projections (`Value` has no
`DecidableEq`; `Value.eqB`/`valuesEqB` are its sound Boolean twins).
FIRST-ORDER recursion: no `zip`/`length` intermediate lists. Retained as
the content-keyed reference twin (P1); the wired P2 scan compares
`stampNatEqB` on `watchVersions` instead. -/
def stampEqB : List Domain → List Domain → Bool
  | [], [] => true
  | x :: xs, y :: ys => Dom.eqB x y && stampEqB xs ys
  | _, _ => false

theorem stampEqB_sound {xs ys : List Domain} (h : stampEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [stampEqB]
  | cons x xs ih =>
      cases ys with
      | nil => simp [stampEqB] at h
      | cons y ys =>
          simp only [stampEqB, Bool.and_eq_true] at h
          rw [Dom.eqB_sound h.1, ih h.2]

/-! ## Version stamps (PLAN task P2)

The scheduler carrier is declared in this module, which sits BELOW
`SlotVersions.lean` in the import DAG
(`ScheduledFamilies -> EventContract -> SlotVersions`). The version vector
and the changed-slot extraction are therefore restated here with the same
semantics as their frozen twins, and the two soundness lemmas the design
consumes are proved here:

* `SchedVersions` is definitionally `SlotVersions` (`abbrev SlotVersions :=
  Array Nat`); `sVersionBump`/`sVersionBumpAll` are `SlotVersions.bump` /
  `SlotVersions.bumpEvents` restricted to the `List Nat` slot projection.
* `frameChanged f g` lists exactly the slots whose `Frame.domains` entry
  differs (a missing/extra slot is a change at its position), and
  `frameChanged_complete` is the completeness property E0's `frameEvents`
  provides (`frameEvents` is complete for every changing slot; the kinds are
  not needed by the sync).
* `domains_eq_of_version_eq` is the local copy of
  `SlotVersions.domain_eq_of_version_eq`: an unchanged counter across a sync
  whose bumps cover every changed slot certifies an unchanged domain.

A later extraction of `frameEvents` below this module can replace the local
`frameChanged` by the shared event vocabulary; the sync only consumes the
completeness of the changed-slot list and the bump monotonicity proved here. -/

/-- Per-slot version counters, aligned with `Frame.domains` (the local twin
of `SlotVersions`). -/
abbrev SchedVersions := Array Nat

/-- Bump one slot's counter; identity when the slot is out of range. -/
def sVersionBump (v : SchedVersions) (s : Nat) : SchedVersions :=
  if h : s < v.size then v.set s (v[s] + 1) h else v

/-- Bump every slot in the list (duplicates bump twice; soundness only needs
"at least once"). -/
def sVersionBumpAll (v : SchedVersions) (ss : List Nat) : SchedVersions :=
  ss.foldl (fun v s => sVersionBump v s) v

@[simp] theorem sVersionBump_size (v : SchedVersions) (s : Nat) :
    (sVersionBump v s).size = v.size := by
  unfold sVersionBump
  split
  · next h => exact Array.size_set h
  · rfl

theorem sVersionBumpAll_size (v : SchedVersions) (ss : List Nat) :
    (sVersionBumpAll v ss).size = v.size := by
  unfold sVersionBumpAll
  induction ss generalizing v with
  | nil => rfl
  | cons s ss ih => exact (ih (sVersionBump v s)).trans (sVersionBump_size v s)

theorem sVersionBump_getD_other {v : SchedVersions} {s k : Nat} (h : k ≠ s) :
    (sVersionBump v s).getD k 0 = v.getD k 0 := by
  unfold sVersionBump
  split
  · next hlt =>
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_set hlt]
      rw [if_neg (by simpa [eq_comm] using h)]
  · rfl

theorem sVersionBump_getD_self {v : SchedVersions} {s : Nat} (h : s < v.size) :
    (sVersionBump v s).getD s 0 = v.getD s 0 + 1 := by
  unfold sVersionBump
  rw [dif_pos h]
  have hset : (v.set s (v[s] + 1) h).getD s 0 = v[s] + 1 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_set h, if_pos rfl]
    rfl
  rw [hset, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  simp

theorem sVersionBump_eq_self {v : SchedVersions} {s : Nat} (h : ¬ s < v.size) :
    sVersionBump v s = v := by
  unfold sVersionBump
  rw [dif_neg h]

theorem sVersionBump_getD_ge (v : SchedVersions) (s k : Nat) :
    v.getD k 0 ≤ (sVersionBump v s).getD k 0 := by
  by_cases h : k = s
  · subst h
    by_cases hlt : k < v.size
    · rw [sVersionBump_getD_self hlt]; omega
    · rw [sVersionBump_eq_self hlt]; exact Nat.le_refl _
  · rw [sVersionBump_getD_other h]
    exact Nat.le_refl _

theorem sVersionBumpAll_getD_ge (v : SchedVersions) (ss : List Nat) (s : Nat) :
    v.getD s 0 ≤ (sVersionBumpAll v ss).getD s 0 := by
  unfold sVersionBumpAll
  induction ss generalizing v with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
      dsimp only [List.foldl_cons]
      exact Nat.le_trans (sVersionBump_getD_ge v a s) (ih (v := sVersionBump v a))

/-- **STRICTNESS**: a mentioned in-range slot's counter strictly increases. -/
theorem sVersionBumpAll_getD_gt_of_mem {v : SchedVersions} {ss : List Nat} {s : Nat}
    (hs : s < v.size) (h : s ∈ ss) :
    v.getD s 0 < (sVersionBumpAll v ss).getD s 0 := by
  induction ss generalizing v with
  | nil => simp at h
  | cons a as ih =>
      rcases List.mem_cons.mp h with he | hmem
      · subst he
        have h1 : (sVersionBump v s).getD s 0 = v.getD s 0 + 1 :=
          sVersionBump_getD_self hs
        have h2 : (sVersionBump v s).getD s 0 ≤
            (sVersionBumpAll (sVersionBump v s) as).getD s 0 :=
          sVersionBumpAll_getD_ge (sVersionBump v s) as s
        change v.getD s 0 < (sVersionBumpAll (sVersionBump v s) as).getD s 0
        omega
      · have hs' : s < (sVersionBump v a).size := by simp [hs]
        have hle := sVersionBump_getD_ge v a s
        have hlt := ih hs' hmem
        change v.getD s 0 < (sVersionBumpAll (sVersionBump v a) as).getD s 0
        exact Nat.lt_of_le_of_lt hle hlt

/-! ## The changed slots of a frame transition -/

/-- Slot-indexed extraction of the CHANGED slots over the two certified
domain lists; a missing/extra slot is a change at its position. -/
def frameChangedAux (s : Nat) : List Domain → List Domain → List Nat
  | [], [] => []
  | [], _ :: es => s :: frameChangedAux (s + 1) [] es
  | _ :: ds, [] => s :: frameChangedAux (s + 1) ds []
  | d :: ds, e :: es =>
      (if Dom.eqB d e then [] else [s]) ++ frameChangedAux (s + 1) ds es

/-- The slots whose domains changed in one frame transition. -/
def frameChanged (f g : BranchFrame) : List Nat :=
  frameChangedAux 0 (Frame.domains f) (Frame.domains g)

theorem frameChangedAux_nil_left_complete (s : Nat) :
    ∀ (es : List Domain) (i : Nat), es.getD i Dom.empty ≠ Dom.empty → s + i ∈ frameChangedAux s [] es := by
  intro es
  induction es generalizing s with
  | nil => intro i h; simp at h
  | cons e es ih =>
      intro i h
      cases i with
      | zero => simp [frameChangedAux]
      | succ i =>
          have h' : es.getD i Dom.empty ≠ Dom.empty := by simpa using h
          have hm := ih (s := s + 1) i h'
          have hidx : s + (i + 1) = s + 1 + i := by omega
          rw [hidx]
          simp only [frameChangedAux]
          exact List.mem_cons_of_mem _ hm

theorem frameChangedAux_nil_right_complete (s : Nat) :
    ∀ (ds : List Domain) (i : Nat), ds.getD i Dom.empty ≠ Dom.empty → s + i ∈ frameChangedAux s ds [] := by
  intro ds
  induction ds generalizing s with
  | nil => intro i h; simp at h
  | cons d ds ih =>
      intro i h
      cases i with
      | zero => simp [frameChangedAux]
      | succ i =>
          have h' : ds.getD i Dom.empty ≠ Dom.empty := by simpa using h
          have hm := ih (s := s + 1) i h'
          have hidx : s + (i + 1) = s + 1 + i := by omega
          rw [hidx]
          simp only [frameChangedAux]
          exact List.mem_cons_of_mem _ hm

theorem frameChangedAux_complete :
    ∀ (s : Nat) (ds es : List Domain) (i : Nat),
      ds.getD i Dom.empty ≠ es.getD i Dom.empty → s + i ∈ frameChangedAux s ds es := by
  intro s ds
  induction ds generalizing s with
  | nil =>
      intro es i h
      exact frameChangedAux_nil_left_complete s es i (by simpa [eq_comm] using h)
  | cons d ds ih =>
      intro es i h
      cases es with
      | nil =>
          cases i with
          | zero => simp [frameChangedAux]
          | succ i =>
              have h' : ds.getD i Dom.empty ≠ Dom.empty := by simpa using h
              have hm := ih (s := s + 1) [] i h'
              have hidx : s + (i + 1) = s + 1 + i := by omega
              rw [hidx]
              simp only [frameChangedAux]
              exact List.mem_cons_of_mem _ hm
      | cons e es =>
          cases i with
          | zero =>
              have hde : d ≠ e := by simpa using h
              have hv : Dom.eqB d e = false := by
                cases hv : Dom.eqB d e with
                | false => rfl
                | true => exact absurd (Dom.eqB_sound hv) hde
              simp [frameChangedAux, hv]
          | succ i =>
              have h' : ds.getD i Dom.empty ≠ es.getD i Dom.empty := by simpa using h
              have hm := ih (s := s + 1) es i h'
              have hidx : s + (i + 1) = s + 1 + i := by omega
              rw [hidx]
              simp only [frameChangedAux]
              exact List.mem_append_right _ hm

/-- Completeness: a slot whose `getD`-form domain differs between the two
frames is reported by `frameChanged`. -/
theorem frameChanged_complete {f g : BranchFrame} {s : Nat}
    (h : (Frame.domains f).getD s Dom.empty ≠ (Frame.domains g).getD s Dom.empty) :
    s ∈ frameChanged f g := by
  have h' := frameChangedAux_complete 0 (Frame.domains f) (Frame.domains g) s
    (by simpa using h)
  simpa [frameChanged] using h'

/-- **THE DISCIPLINE**: one sync whose bumps cover every changed slot. If the
counter at `s` did not move, the slot's certified domain did not change (the
`getD` form of `Frame.domains` agreement). The length premises make `getD`
total; they hold for the dispatcher's fixed-width frame. -/
theorem domains_eq_of_version_eq {f g : BranchFrame} {v : SchedVersions} {s : Nat}
    (hsize : v.size = (Frame.domains f).length)
    (hsize' : (sVersionBumpAll v (frameChanged f g)).size = (Frame.domains g).length)
    (h : (sVersionBumpAll v (frameChanged f g)).getD s 0 = v.getD s 0) :
    (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty := by
  apply Classical.not_not.mp
  intro hne
  have hmem : s ∈ frameChanged f g := frameChanged_complete hne
  have hs : s < v.size := by
    rw [hsize]
    by_cases hlt : s < (Frame.domains f).length
    · exact hlt
    · have hflen : (Frame.domains f).length ≤ s := by omega
      have heq : (Frame.domains g).length = (Frame.domains f).length := by
        rw [← hsize', sVersionBumpAll_size, hsize]
      have hglen : (Frame.domains g).length ≤ s := by omega
      have hf : (Frame.domains f).getD s Dom.empty = Dom.empty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hflen]
        rfl
      have hg : (Frame.domains g).getD s Dom.empty = Dom.empty := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hglen]
        rfl
      exact absurd (hf.trans hg.symm) hne
  have hgt := sVersionBumpAll_getD_gt_of_mem hs hmem
  omega

/-! ## Version-keyed watch stamps -/

/-- The version stamp of a watch list: the current counter of every watched
slot, in watch order. O(1) per watched slot (an `Array.getD` read). -/
def watchVersions (v : SchedVersions) (watches : List Atom) : List Nat :=
  watches.map fun a => v.getD a.slot 0

@[simp] theorem watchVersions_length (v : SchedVersions) (watches : List Atom) :
    (watchVersions v watches).length = watches.length := by
  simp [watchVersions]

/-- Sound Boolean equality of two version stamp lists. FIRST-ORDER recursion
(no `zip`/`length` intermediates): this is the scheduled scan's hot-path skip
test, over O(1) per-slot counters instead of O(domain) values. -/
def stampNatEqB : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && stampNatEqB xs ys
  | _, _ => false

theorem stampNatEqB_sound {xs ys : List Nat} (h : stampNatEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [stampNatEqB]
  | cons x xs ih =>
      cases ys with
      | nil => simp [stampNatEqB] at h
      | cons y ys =>
          simp only [stampNatEqB, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, ih h.2]

/-- Pointwise `≤` of version stamp lists: the recorded stamp of every watched
slot is at most the current version (the monotonicity half of `EntryOK`). It
is a `Prop` (not on the hot path) so the proof does not pay for `Bool`
reflection. -/
def stampLe : List Nat → List Nat → Prop
  | [], [] => True
  | x :: xs, y :: ys => x ≤ y ∧ stampLe xs ys
  | _, _ => False

theorem stampLe.length_eq {xs ys : List Nat} (h : stampLe xs ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          simp only [stampLe] at h
          simp [ih h.2]

theorem stampLe.refl (xs : List Nat) : stampLe xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨Nat.le_refl _, ih⟩

theorem stampLe.trans {xs ys zs : List Nat} (h1 : stampLe xs ys) (h2 : stampLe ys zs) :
    stampLe xs zs := by
  induction xs generalizing ys zs with
  | nil => cases ys <;> cases zs <;> simp_all [stampLe]
  | cons x xs ih =>
      cases ys with
      | nil => cases h1
      | cons y ys =>
          cases zs with
          | nil => cases h2
          | cons z zs =>
              simp only [stampLe] at h1 h2 ⊢
              exact ⟨Nat.le_trans h1.1 h2.1, ih h1.2 h2.2⟩

theorem stampLe.antisymm {xs ys : List Nat} (h1 : stampLe xs ys) (h2 : stampLe ys xs) :
    xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => cases h2
  | cons x xs ih =>
      cases ys with
      | nil => cases h1
      | cons y ys =>
          simp only [stampLe] at h1 h2
          have hxy : x = y := Nat.le_antisymm h1.1 h2.1
          rw [hxy, ih h1.2 h2.2]

theorem watchVersions_le_of_pointwise {v v' : SchedVersions}
    (h : ∀ s, v.getD s 0 ≤ v'.getD s 0) (ws : List Atom) :
    stampLe (watchVersions v ws) (watchVersions v' ws) := by
  induction ws with
  | nil => trivial
  | cons a as ih =>
      simp only [watchVersions, List.map_cons, stampLe]
      exact ⟨h a.slot, ih⟩

theorem watchVersions_getD_of_eq {v v' : SchedVersions} {ws : List Atom}
    (h : watchVersions v ws = watchVersions v' ws) {a : Atom} (ha : a ∈ ws) :
    v.getD a.slot 0 = v'.getD a.slot 0 := by
  induction ws with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [watchVersions, List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact h.1
      · exact ih h.2 hmem

/-! ## The scheduler state -/

/-! ### The E1 event-keyed work queue (carrier and invariant)

The queue carrier and its proof invariant are declared HERE (rather than in
`WorkQueue.lean`) because the runtime dispatcher threads them through
`PropScheduler`, while `WorkQueue.lean` sits ABOVE this module in the import
DAG (it consumes `EventContract`). The queue's operations, its event-silence
algebra, and every preservation/completeness proof live in
`Propagation/WorkQueue.lean`; this section only fixes the data and the
invariant the threaded state carries.

The coverage certificate `QueueQuiet` is deliberately E0-free: it asks for
`watchStamp` agreement on a NONEMPTY footprint (exactly what the registered
locality theorems `PropLocalOne` consume) and for full `Frame.domains`
agreement on an empty footprint (a footprint-less unit subscribes to every
event, so only an unchanged domain list certifies it). E0's event silence
implies `QueueQuiet` (`eventSilent_imp_quiet`, `WorkQueue.lean`), but
`QueueQuiet` is slightly laxer (a truncated watched slot holding an EMPTY
domain may carry a `replaced` event while its `getD` agrees); this is sound
because only `PropLocalOne` is consumed, never the event vocabulary itself. -/

/-- The persistent work queue's data: per-unit reference frame + recorded
result (aligned with the caller's propagator list) and the deduplicated
pending unit indices. -/
structure WorkQueue where
  /-- Per-unit records, aligned with the propagator list. -/
  seen : List (Option (BranchFrame × PropagationResult))
  /-- Pending unit indices, in insertion order, without duplicates. -/
  pending : List Nat

/-- The conservative start: every unit is queued and nothing is recorded. -/
def WorkQueue.init (props : List Propagator) : WorkQueue :=
  { seen := props.map fun _ => none, pending := List.range props.length }

/-- Conservative rebuild (restore / database change): re-queue everything and
drop the records. -/
def WorkQueue.rebuild (_q : WorkQueue) (props : List Propagator) : WorkQueue :=
  WorkQueue.init props

/-- The queue's progress measure: the number of pending units. -/
def queueMeasure (q : WorkQueue) : Nat := q.pending.length

/-- The E0-free coverage certificate: the transition `f → g` cannot change the
unit's run. Empty footprint: the whole domain list is unchanged (so the run's
whole input state is unchanged); nonempty footprint: the watch projection is
unchanged (consumed by `PropLocalOne`). -/
def QueueQuiet (p : Propagator) (f g : BranchFrame) : Prop :=
  (p.watches = [] ∧ Frame.domains f = Frame.domains g) ∨
    (p.watches ≠ [] ∧ watchStamp f p.watches = watchStamp g p.watches)

/-- Structural well-formedness: the records are aligned with the propagator
list, the pending indices are distinct and in range. -/
def QueueShape (props : List Propagator) (q : WorkQueue) : Prop :=
  q.seen.length = props.length ∧ q.pending.Nodup ∧ ∀ i ∈ q.pending, i < props.length

/-- Record correctness: every stored result is the run's result at its stored
reference frame. -/
def QueueRecords (props : List Propagator) (q : WorkQueue) : Prop :=
  ∀ (i : Nat) (p : Propagator) (f : BranchFrame) (r : PropagationResult),
    props[i]? = some p → q.seen[i]? = some (some (f, r)) → r = p.run (frameState f)

/-- **COVERAGE**: every unit is EITHER queued OR its stored reference frame is
`QueueQuiet` to the current frame (its result is provably unchanged), i.e. a
unit that could contribute something different at the current frame is always
in the queue. -/
def QueueCovered (props : List Propagator) (q : WorkQueue) (g : BranchFrame) : Prop :=
  ∀ (i : Nat) (p : Propagator), props[i]? = some p →
    i ∈ q.pending ∨
      ∃ f r, q.seen[i]? = some (some (f, r)) ∧ QueueQuiet p f g

/-- The full queue invariant (shape, records, coverage). -/
def QueueOK (props : List Propagator) (q : WorkQueue) (g : BranchFrame) : Prop :=
  QueueShape props q ∧ QueueRecords props q ∧ QueueCovered props q g

/-- The queue invariant transports along equal propagator lists. -/
theorem QueueOK.of_props_eq {props props' : List Propagator} {q : WorkQueue}
    {g : BranchFrame} (h : props' = props) (hok : QueueOK props q g) :
    QueueOK props' q g := by
  subst h
  exact hok

/-- `init` is covered at any frame (everything is queued). -/
theorem QueueOK_init (props : List Propagator) (g : BranchFrame) :
    QueueOK props (WorkQueue.init props) g := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [WorkQueue.init]
  · exact List.nodup_range
  · intro i hi
    simpa [WorkQueue.init] using (List.mem_range.mp hi)
  · intro i p f r hp hseen
    simp [WorkQueue.init] at hseen
  · intro i p hp
    exact Or.inl (by
      simp only [WorkQueue.init, List.mem_range]
      exact (List.getElem?_eq_some_iff.mp hp).1)

/-- `rebuild` is covered at any frame. -/
theorem QueueOK_rebuild (props : List Propagator) (q : WorkQueue) (g : BranchFrame) :
    QueueOK props (q.rebuild props) g :=
  QueueOK_init props g

/-! ### The scheduled scan's version-keyed table

`SchedEntry.stamps` is the VERSION of every watched slot at record time: the
hot-path key. `SchedEntry.domains` is the watch projection at record time; it
is kept for the proof only and is never compared by the scan (the old content
comparison is gone). -/

/-- One memorized scheduled-scan record. -/
structure SchedEntry where
  /-- Version of every watched slot at record time (hot-path key). -/
  stamps : List Nat
  /-- Watch projection at record time (proof only; never compared). -/
  domains : List Domain
  /-- The result the run produced there. -/
  result : PropagationResult

/-- The record a run observed at `f` under versions `v`. -/
def freshEntry (v : SchedVersions) (f : BranchFrame) (p : Propagator)
    (r : PropagationResult) : SchedEntry :=
  { stamps := watchVersions v p.watches, domains := watchStamp f p.watches, result := r }

/-- The scheduled scan's memorized table, aligned with the propagator list:
entry `i` records the version stamps of the watched slots and the watch
projection at which propagator `i` last ran, together with the result observed
there. The E1 work queue and the frame it was last synced to ride along
(defaulted so standalone literals keep elaborating; `PropScheduler.init` fills
them). `versions` is the per-slot counter vector, `vframe` the frame it refers
to. -/
structure PropScheduler where
  seen : List (Option SchedEntry)
  /-- The E1 event-keyed work queue (PLAN task E1). -/
  work : WorkQueue := { seen := [], pending := [] }
  /-- The frame at which `work` was last synced: the queue step enqueues the
  units subscribed to `frameEvents qframe f`. The empty frame is a safe
  default because a fresh queue is entirely pending, so coverage holds at any
  frame. -/
  qframe : BranchFrame := ({ doms := [], order := [] } : BranchFrame)
  /-- Per-slot version counters, aligned with `Frame.domains`. Defaulted so
  standalone literals keep elaborating; `PropScheduler.init` starts empty
  (the first `sync` then resets to the frame's width). -/
  versions : SchedVersions := #[]
  /-- The frame `versions` refers to. -/
  vframe : BranchFrame := ({ doms := [], order := [] } : BranchFrame)
  /-- The watched-clause database index (PLAN K3).  It is aligned with the
  scanned learned database and self-validating (`scanDatabaseWatch2_fst_eq`);
  the default empty index makes the first scan an establish pass. -/
  watch : WatchIndex := WatchIndex.init

/-- The empty scheduler: nothing memorized (the full scan's behaviour), a
fully pending queue (conservative coverage at any frame), and the empty
version vector at the empty reference frame. -/
def PropScheduler.init (props : List Propagator) : PropScheduler :=
  { seen := props.map fun _ => none,
    work := WorkQueue.init props,
    qframe := ({ doms := [], order := [] } : BranchFrame),
    versions := #[],
    vframe := ({ doms := [], order := [] } : BranchFrame) }

/-- Sync the version vector to `f` (PLAN task P2). At a matching width the
counters of exactly the changed slots are bumped (`frameChanged` is complete
for them, so an unchanged counter certifies an unchanged domain); at a width
change -- not performed by the dispatcher, but supported -- the vector is
reset to zeros of the new width and every memorized entry is dropped (the
conservative reset). The queue fields are untouched. -/
def PropScheduler.sync (sched : PropScheduler) (f : BranchFrame) : PropScheduler :=
  if sched.versions.size = (Frame.domains f).length then
    { sched with
        versions := sVersionBumpAll sched.versions (frameChanged sched.vframe f),
        vframe := f }
  else
    { sched with
        versions := Array.replicate (Frame.domains f).length 0,
        vframe := f,
        seen := sched.seen.map fun _ => none }

theorem PropScheduler.sync_versions_size (sched : PropScheduler) (f : BranchFrame) :
    (sched.sync f).versions.size = (Frame.domains f).length := by
  unfold PropScheduler.sync
  by_cases h : sched.versions.size = (Frame.domains f).length
  · rw [if_pos h, sVersionBumpAll_size]
    exact h
  · rw [if_neg h]
    exact Array.size_replicate

theorem PropScheduler.sync_vframe (sched : PropScheduler) (f : BranchFrame) :
    (sched.sync f).vframe = f := by
  unfold PropScheduler.sync
  split <;> rfl

theorem PropScheduler.sync_work (sched : PropScheduler) (f : BranchFrame) :
    (sched.sync f).work = sched.work := by
  unfold PropScheduler.sync
  split <;> rfl

theorem PropScheduler.sync_qframe (sched : PropScheduler) (f : BranchFrame) :
    (sched.sync f).qframe = sched.qframe := by
  unfold PropScheduler.sync
  split <;> rfl

/-- Consistency of ONE memorized entry: the stamps are aligned with the
watched slots and are at most the current versions (monotonicity); if the
current version stamps still equal the recorded ones, the recorded domain
projection is the current one; and the recorded result is the run's result at
EVERY frame whose watch projection is the recorded `domains`. The table only
requires this for a propagator with a NONEMPTY declared footprint: a
footprint-less unit is never reused, so its entry carries no claim (exactly
the old vacuous-entry behaviour). -/
structure EntryOK (p : Propagator) (v : SchedVersions) (f : BranchFrame)
    (e : SchedEntry) : Prop where
  /-- The recorded stamps are aligned with the watched slots. -/
  stamps_len : e.stamps.length = (watchVersions v p.watches).length
  /-- Monotonicity: a recorded stamp never exceeds the current version. -/
  mono : stampLe e.stamps (watchVersions v p.watches)
  /-- The recorded projection is the current one when the versions have not
  moved since the record. -/
  domains_eq : watchVersions v p.watches = e.stamps → watchStamp f p.watches = e.domains
  /-- The recorded result is the run's result at every frame with the recorded
  watch projection. -/
  run_eq : ∀ g : BranchFrame, watchStamp g p.watches = e.domains → p.run (frameState g) = e.result

/-- Consistency of a memorized table with the runs, at version vector `v` and
frame `f` (which `v` must be aligned with). -/
structure TableOK (props : List Propagator) (v : SchedVersions) (f : BranchFrame)
    (seen : List (Option SchedEntry)) : Prop where
  /-- The vector width is the frame width. -/
  size_eq : v.size = (Frame.domains f).length
  /-- Every aligned entry is consistent at this vector and frame. -/
  entry : ∀ (j : Nat) (p : Propagator) (e : SchedEntry),
    props[j]? = some p → seen[j]? = some (some e) → p.watches ≠ [] → EntryOK p v f e

/-- Consistency of a scheduler: the memorized version-stamp table AND the E1
work queue's invariant at its stored sync frame. -/
def PropSchedulerOK (props : List Propagator) (sched : PropScheduler) : Prop :=
  TableOK props sched.versions sched.vframe sched.seen ∧
    QueueOK props sched.work sched.qframe

/-- Table consistency transports along equal propagator lists. -/
theorem TableOK.of_props_eq {props props' : List Propagator}
    {v : SchedVersions} {f : BranchFrame} {seen : List (Option SchedEntry)}
    (h : props' = props) (hok : TableOK props v f seen) : TableOK props' v f seen := by
  subst h
  exact hok

/-- Scheduler consistency transports along equal propagator lists. -/
theorem PropSchedulerOK.of_props_eq {props props' : List Propagator}
    {sched : PropScheduler} (h : props' = props) (hok : PropSchedulerOK props sched) :
    PropSchedulerOK props' sched :=
  ⟨TableOK.of_props_eq h hok.1, QueueOK.of_props_eq h hok.2⟩

/-- The empty scheduler is consistent (every table entry is `none`, so its
obligations are vacuous; the fresh queue is entirely pending; the empty
version vector is aligned with the empty reference frame). -/
theorem PropSchedulerOK.init (props : List Propagator) :
    PropSchedulerOK props (PropScheduler.init props) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simp [PropScheduler.init, Frame.domains]
    · intro j p e _ he
      simp only [PropScheduler.init, List.getElem?_map, Option.map_eq_some_iff] at he
      obtain ⟨a, _, ha⟩ := he
      exact absurd ha (by simp)
  · show QueueOK props (WorkQueue.init props) ({ doms := [], order := [] } : BranchFrame)
    exact QueueOK_init props _

/-- The per-propagator STATIC locality hypothesis: the run depends only on
the current domains of its watched slots. This is the (honest) semantic
content the scheduling consumes; it is discharged per family for the
concrete registrations (`ScheduledFamilies.lean`). -/
def PropLocalOne (p : Propagator) : Prop :=
  ∀ f g : BranchFrame, watchStamp f p.watches = watchStamp g p.watches →
    p.run (frameState f) = p.run (frameState g)

def PropLocal (props : List Propagator) : Prop :=
  ∀ p ∈ props, p.watches ≠ [] → PropLocalOne p

theorem PropLocal.tail {p : Propagator} {ps : List Propagator}
    (h : PropLocal (p :: ps)) : PropLocal ps :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- Locality transports along equal propagator lists. -/
theorem PropLocal.of_props_eq {props props' : List Propagator} (h : props' = props)
    (hloc : PropLocal props) : PropLocal props' :=
  fun q hq hne => hloc q (by simpa [h] using hq) hne

/-! ## The scheduled scan -/

/-- The scheduled propagator scan (table-aligned recursion) under version
vector `v`. For each propagator in order: if the memorized version stamps
equal the current ones (and the footprint is nonempty), re-use the memorized
result (the run is skipped); otherwise run the propagator and memorize its
result when the scan continues past it. The continuation logic (conflict
report, productivity gate, early exit) is the verbatim `scanPropagators`
logic; only the table key changed (versions instead of domain content).
P2b: like `scanPropagators`, emitted deductions carry `learnReason = false`
(no propagator-reason clause enters the global learned database). -/
def scanPropagatorsSchedAux (f : BranchFrame) (v : SchedVersions) :
    List (Option SchedEntry) → List Propagator →
      PruningEvent × List (Option SchedEntry)
  | seens, [] => (.stable, seens)
  | [], p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAux f v [] ps
          (ev, some (freshEntry v f p .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), [])
      | .implied l r =>
          if productive l f then
            (.implied l r.clause false false, [])
          else
            let (ev, seens') := scanPropagatorsSchedAux f v [] ps
            (ev, some (freshEntry v f p (.implied l r)) :: seens')
  | some e :: seens, p :: ps =>
      if stampNatEqB e.stamps (watchVersions v p.watches) && !p.watches.isEmpty then
        match e.result with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAux f v seens ps
            (ev, some e :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some e :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause false false, some e :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAux f v seens ps
              (ev, some e :: seens')
      else
        match p.run (frameState f) with
        | .stable =>
            let (ev, seens') := scanPropagatorsSchedAux f v seens ps
            (ev, some (freshEntry v f p .stable) :: seens')
        | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some e :: seens)
        | .implied l r' =>
            if productive l f then
              (.implied l r'.clause false false, some e :: seens)
            else
              let (ev, seens') := scanPropagatorsSchedAux f v seens ps
              (ev, some (freshEntry v f p (.implied l r')) :: seens')
  | none :: seens, p :: ps =>
      match p.run (frameState f) with
      | .stable =>
          let (ev, seens') := scanPropagatorsSchedAux f v seens ps
          (ev, some (freshEntry v f p .stable) :: seens')
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), none :: seens)
      | .implied l r =>
          if productive l f then
            (.implied l r.clause false false, none :: seens)
          else
            let (ev, seens') := scanPropagatorsSchedAux f v seens ps
            (ev, some (freshEntry v f p (.implied l r)) :: seens')

/-- The scheduled scan of a frame against a scheduler. It syncs the version
vector to `f` on EVERY call (the width check / frame-event bump of
`PropScheduler.sync`), scans under the synced vector, and stores the synced
vector and frame in the result. The queue fields ride along untouched. -/
def scanPropagatorsSched (f : BranchFrame) (sched : PropScheduler)
    (props : List Propagator) : PruningEvent × PropScheduler :=
  let sched' := sched.sync f
  let (ev, seen) := scanPropagatorsSchedAux f sched'.versions sched'.seen props
  (ev, { sched' with seen := seen })

/-- The scheduled event selection: the DB scan is the optimised `scanDatabaseFast`
(proved equal to the certified `scanDatabase` by `scanDatabaseFast_eq`, so the
certified equivalence below is unaffected) and the liveness gates are the
certified ones; only the propagator scan is scheduled. The watched-scan
candidate (PLAN K3) was measured a NO-GO on the K3 panel, so the default keeps
`scanDatabaseFast`; the test-only twin used for that measurement lives in
`Tests/Legacy/Benchmarks/HeurTiming.lean`. -/
def nextPruningEventSched (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  match scanDatabaseFast original f db with
  | .stable =>
      if frameViewedB f then scanPropagatorsSched f sched props else (.stable, sched)
  | .conflict cs => (.conflict cs, sched)
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then (.implied l c learnReason fromLearned, sched) else (.stable, sched)

/-! ## Table algebra -/

/-- A run observed at `f` under versions `v`, recorded as a fresh entry. -/
theorem EntryOK.of_local_run {p : Propagator} {v : SchedVersions} {f : BranchFrame}
    {r : PropagationResult} (h : PropLocalOne p) (hrun : p.run (frameState f) = r) :
    EntryOK p v f (freshEntry v f p r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · exact stampLe.refl _
  · intro _; rfl
  · intro g hg
    exact ((h f g hg.symm).symm).trans hrun

/-- Entry transport across one version sync: monotonicity gives
`old ≤ new`, the recorded stamps are `≤ old`, and an unchanged new stamp is
also `≤ old`, so antisymmetry recovers the old stamps; `domains_eq` then uses
the version discipline (`domains_eq_of_version_eq`) on every watched slot. -/
theorem EntryOK.sync {p : Propagator} {v v' : SchedVersions} {f0 f : BranchFrame}
    {e : SchedEntry}
    (hbump : v' = sVersionBumpAll v (frameChanged f0 f))
    (hsize : v.size = (Frame.domains f0).length)
    (hsize' : v'.size = (Frame.domains f).length)
    (h : EntryOK p v f0 e) : EntryOK p v' f e := by
  refine ⟨?_, ?_, ?_, h.run_eq⟩
  · rw [hbump, h.stamps_len, watchVersions_length, watchVersions_length]
  · rw [hbump]
    exact stampLe.trans h.mono
      (watchVersions_le_of_pointwise
        (fun s => sVersionBumpAll_getD_ge v (frameChanged f0 f) s) p.watches)
  · intro hveq
    rw [hbump] at hveq hsize'
    have hle : stampLe (watchVersions v p.watches)
        (watchVersions (sVersionBumpAll v (frameChanged f0 f)) p.watches) :=
      watchVersions_le_of_pointwise
        (fun s => sVersionBumpAll_getD_ge v (frameChanged f0 f) s) p.watches
    have hmono' : stampLe (watchVersions (sVersionBumpAll v (frameChanged f0 f)) p.watches)
        (watchVersions v p.watches) :=
      hveq.symm ▸ h.mono
    have heq : watchVersions v p.watches
        = watchVersions (sVersionBumpAll v (frameChanged f0 f)) p.watches :=
      stampLe.antisymm hle hmono'
    have hdom := h.domains_eq (heq.trans hveq)
    rw [← hdom]
    simp only [watchStamp]
    apply List.map_congr_left
    intro a ha
    have hvs := watchVersions_getD_of_eq heq ha
    exact (domains_eq_of_version_eq (g := f) hsize hsize' hvs.symm).symm

/-- The empty table is consistent at any propagator list. -/
theorem TableOK.nil {props : List Propagator} {v : SchedVersions}
    {f : BranchFrame} (hsize : v.size = (Frame.domains f).length) :
    TableOK props v f ([] : List (Option SchedEntry)) :=
  ⟨hsize, fun j q e hq he _ => by simp at he⟩

/-- The empty table is consistent at any nonempty propagator list. -/
theorem TableOK.nil_cons {p : Propagator} {ps : List Propagator} {v : SchedVersions}
    {f : BranchFrame} (hsize : v.size = (Frame.domains f).length) :
    TableOK (p :: ps) v f ([] : List (Option SchedEntry)) :=
  TableOK.nil hsize

/-- The tail of a consistent table is consistent. -/
theorem TableOK.tail {p : Propagator} {e : Option SchedEntry} {ps : List Propagator}
    {v : SchedVersions} {f : BranchFrame} {seens : List (Option SchedEntry)}
    (h : TableOK (p :: ps) v f (e :: seens)) : TableOK ps v f seens :=
  ⟨h.size_eq, fun j q e' hq he hne =>
    h.entry (j + 1) q e' (by simpa using hq) (by simpa using he) hne⟩

/-- The head entry of a consistent table is consistent (for a nonempty
footprint). -/
theorem TableOK.head {p : Propagator} {e : SchedEntry} {ps : List Propagator}
    {v : SchedVersions} {f : BranchFrame} {seens : List (Option SchedEntry)}
    (h : TableOK (p :: ps) v f (some e :: seens)) :
    p.watches ≠ [] → EntryOK p v f e :=
  fun hne => h.entry 0 p e rfl (by simp) hne

/-- Rebuild a consistent table with a recorded head entry. -/
theorem TableOK.cons_head {p : Propagator} {ps : List Propagator} {v : SchedVersions}
    {f : BranchFrame} {e : SchedEntry} {seens : List (Option SchedEntry)}
    (hsize : v.size = (Frame.domains f).length)
    (h0 : ∀ _hne : p.watches ≠ [], EntryOK p v f e)
    (htail : TableOK ps v f seens) :
    TableOK (p :: ps) v f (some e :: seens) := by
  refine ⟨hsize, ?_⟩
  intro j q e' hq he hne
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq he
      subst hq
      subst he
      exact h0 hne
  | succ j =>
      exact htail.entry j q e' (by simpa using hq) (by simpa using he) hne

/-- Rebuild a consistent table with a vacuous head entry. -/
theorem TableOK.cons_none {p : Propagator} {ps : List Propagator} {v : SchedVersions}
    {f : BranchFrame} {seens : List (Option SchedEntry)}
    (hsize : v.size = (Frame.domains f).length)
    (htail : TableOK ps v f seens) :
    TableOK (p :: ps) v f (none :: seens) := by
  refine ⟨hsize, ?_⟩
  intro j q e hq he hne
  cases j with
  | zero => simp only [List.getElem?_cons_zero] at he; cases he
  | succ j =>
      exact htail.entry j q e (by simpa using hq) (by simpa using he) hne

/-- **TABLE SYNC**: the table transports across one version sync, by
`EntryOK.sync` on every aligned entry. A width change resets the table
(conservative; not performed by the dispatcher). The vector size invariant is
re-established by `sVersionBumpAll_size` (or the reset's replicate). -/
theorem TableOK.sync {props : List Propagator} {sched : PropScheduler}
    {f : BranchFrame} (h : TableOK props sched.versions sched.vframe sched.seen) :
    TableOK props (sched.sync f).versions f (sched.sync f).seen := by
  unfold PropScheduler.sync
  by_cases hsize : sched.versions.size = (Frame.domains f).length
  · rw [if_pos hsize]
    refine ⟨?_, ?_⟩
    · rw [sVersionBumpAll_size]
      exact hsize
    · intro j p e hq he hne
      exact EntryOK.sync (hbump := rfl) h.size_eq (by rwa [sVersionBumpAll_size])
        (h.entry j p e hq he hne)
  · rw [if_neg hsize]
    refine ⟨?_, ?_⟩
    · exact Array.size_replicate
    · intro j p e hq he _
      simp only [List.getElem?_map, Option.map_eq_some_iff] at he
      obtain ⟨a, _, ha⟩ := he
      exact absurd ha (by simp)

/-! ## Equation lemmas for the scheduled scan -/

section Equations

variable (f : BranchFrame) (v : SchedVersions)

theorem schedAux_nil_nil : scanPropagatorsSchedAux f v [] [] = (.stable, []) := rfl

theorem schedAux_nil_stable (p : Propagator) (ps : List Propagator)
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f v [] (p :: ps)
      = ((scanPropagatorsSchedAux f v [] ps).1,
         some (freshEntry v f p .stable) :: (scanPropagatorsSchedAux f v [] ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v [] ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hrec]

theorem schedAux_nil_conflict (p : Propagator) (ps : List Propagator) (c : Clause)
    (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f v [] (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), []) := by
  simp only [scanPropagatorsSchedAux, h]

theorem schedAux_nil_implied_hit (p : Propagator) (ps : List Propagator)
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : productive l f = true) :
    scanPropagatorsSchedAux f v [] (p :: ps)
      = (.implied l r.clause false false, []) := by
  simp only [scanPropagatorsSchedAux, h, hp, if_pos]

theorem schedAux_nil_implied_miss (p : Propagator) (ps : List Propagator)
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f v [] (p :: ps)
      = ((scanPropagatorsSchedAux f v [] ps).1,
         some (freshEntry v f p (.implied l r)) :: (scanPropagatorsSchedAux f v [] ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v [] ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hp, Bool.false_eq_true, hrec]
      rfl

theorem schedAux_some_stable (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, .stable⟩ :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some ⟨stamps, doms, .stable⟩ :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, if_pos, hrec]

theorem schedAux_some_conflict (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (c : Clause)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, .conflict c⟩ :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), some ⟨stamps, doms, .conflict c⟩ :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, if_pos]

theorem schedAux_some_implied_hit (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (l : Literal) (r : Reason)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = true)
    (hp : productive l f = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, .implied l r⟩ :: seens) (p :: ps)
      = (.implied l r.clause false false, some ⟨stamps, doms, .implied l r⟩ :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, if_pos, hp, if_pos]

theorem schedAux_some_implied_miss (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (l : Literal) (r : Reason)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = true)
    (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, .implied l r⟩ :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some ⟨stamps, doms, .implied l r⟩ :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, if_pos, hp, Bool.false_eq_true, hrec]
      rfl

theorem schedAux_miss_stable (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (r : PropagationResult)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = false)
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, r⟩ :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some (freshEntry v f p .stable) :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hrec]
      rfl

theorem schedAux_miss_conflict (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (r : PropagationResult)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = false)
    (c : Clause) (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, r⟩ :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), some ⟨stamps, doms, r⟩ :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h]
  rfl

theorem schedAux_miss_implied_hit (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (r : PropagationResult)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = false)
    (l : Literal) (r' : Reason)
    (h : p.run (frameState f) = .implied l r') (hp : productive l f = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, r⟩ :: seens) (p :: ps)
      = (.implied l r'.clause false false, some ⟨stamps, doms, r⟩ :: seens) := by
  simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hp, if_pos]
  rfl

theorem schedAux_miss_implied_miss (p : Propagator) (ps : List Propagator)
    (stamps : List Nat) (doms : List Domain) (r : PropagationResult)
    (seens : List (Option SchedEntry))
    (hm : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = false)
    (l : Literal) (r' : Reason)
    (h : p.run (frameState f) = .implied l r') (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f v (some ⟨stamps, doms, r⟩ :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some (freshEntry v f p (.implied l r')) :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, hm, Bool.false_eq_true, h, hp, hrec]
      rfl

theorem schedAux_none_stable (p : Propagator) (ps : List Propagator)
    (seens : List (Option SchedEntry))
    (h : p.run (frameState f) = .stable) :
    scanPropagatorsSchedAux f v (none :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some (freshEntry v f p .stable) :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hrec]

theorem schedAux_none_conflict (p : Propagator) (ps : List Propagator)
    (seens : List (Option SchedEntry)) (c : Clause)
    (h : p.run (frameState f) = .conflict c) :
    scanPropagatorsSchedAux f v (none :: seens) (p :: ps)
      = (.conflict (if c.isEmpty then [] else [c]), none :: seens) := by
  simp only [scanPropagatorsSchedAux, h]

theorem schedAux_none_implied_hit (p : Propagator) (ps : List Propagator)
    (seens : List (Option SchedEntry))
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : productive l f = true) :
    scanPropagatorsSchedAux f v (none :: seens) (p :: ps)
      = (.implied l r.clause false false, none :: seens) := by
  simp only [scanPropagatorsSchedAux, h, hp, if_pos]

theorem schedAux_none_implied_miss (p : Propagator) (ps : List Propagator)
    (seens : List (Option SchedEntry))
    (l : Literal) (r : Reason)
    (h : p.run (frameState f) = .implied l r) (hp : ¬ productive l f = true) :
    scanPropagatorsSchedAux f v (none :: seens) (p :: ps)
      = ((scanPropagatorsSchedAux f v seens ps).1,
         some (freshEntry v f p (.implied l r)) :: (scanPropagatorsSchedAux f v seens ps).2) := by
  cases hrec : scanPropagatorsSchedAux f v seens ps with
  | mk ev seens' =>
      simp only [scanPropagatorsSchedAux, h, hp, Bool.false_eq_true, hrec]
      rfl

end Equations

/-! ## The equivalence theorems -/

/-- **THE EQUIVALENCE (scan level)**: a consistent table makes the scheduled
scan produce EXACTLY the event of the full `scanPropagators`, and the table
returned by the scan stays consistent at the same vector and frame. The skip
path consumes `EntryOK.domains_eq` (the version stamps still match the record,
so the recorded projection is the current one) and `EntryOK.run_eq` (the
recorded result is the run's at the current frame). -/
theorem scanPropagatorsSchedAux_spec {f : BranchFrame} {v : SchedVersions} :
    ∀ (ps : List Propagator) (seens : List (Option SchedEntry)),
      TableOK ps v f seens → PropLocal ps →
      (scanPropagatorsSchedAux f v seens ps).1 = scanPropagators f ps ∧
      TableOK ps v f (scanPropagatorsSchedAux f v seens ps).2 := by
  intro ps
  induction ps with
  | nil =>
      intro seens _ _
      exact ⟨by first | rfl | trivial, by assumption⟩
  | cons p ps ih =>
      intro seens hok hloc
      have hlocp : p.watches ≠ [] → PropLocalOne p := hloc p (List.mem_cons_self ..)
      have hsize : v.size = (Frame.domains f).length := hok.size_eq
      cases seens with
      | nil =>
          have hoktail : TableOK ps v f [] := TableOK.nil hsize
          have ih' := ih [] hoktail hloc.tail
          cases hrun : p.run (frameState f) with
          | stable =>
              rw [schedAux_nil_stable f v p ps hrun, scanPropagators, hrun]
              exact ⟨ih'.1, TableOK.cons_head hsize
                (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩
          | conflict c =>
              simp only [schedAux_nil_conflict f v p ps c hrun, scanPropagators, hrun]
              exact ⟨by first | rfl | trivial, TableOK.nil_cons hsize⟩
          | implied l r =>
              by_cases hprod : productive l f = true
              · simp only [schedAux_nil_implied_hit f v p ps l r hrun hprod, scanPropagators,
                  hrun, if_pos hprod]
                exact ⟨by first | rfl | trivial, TableOK.nil_cons hsize⟩
              · simp only [schedAux_nil_implied_miss f v p ps l r hrun hprod, scanPropagators,
                  hrun, if_neg hprod]
                exact ⟨ih'.1, TableOK.cons_head hsize
                  (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩
      | cons e seens =>
          cases e with
          | none =>
              have hoktail : TableOK ps v f seens := TableOK.tail hok
              have ih' := ih seens hoktail hloc.tail
              cases hrun : p.run (frameState f) with
              | stable =>
                  simp only [schedAux_none_stable f v p ps seens hrun, scanPropagators, hrun]
                  exact ⟨ih'.1, TableOK.cons_head hsize
                    (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩
              | conflict c =>
                  simp only [schedAux_none_conflict f v p ps seens c hrun, scanPropagators, hrun]
                  exact ⟨by first | rfl | trivial, TableOK.cons_none hsize hoktail⟩
              | implied l r =>
                  by_cases hprod : productive l f = true
                  · simp only [schedAux_none_implied_hit f v p ps seens l r hrun hprod,
                      scanPropagators, hrun, if_pos hprod]
                    exact ⟨by first | rfl | trivial, TableOK.cons_none hsize hoktail⟩
                  · simp only [schedAux_none_implied_miss f v p ps seens l r hrun hprod,
                      scanPropagators, hrun, if_neg hprod]
                    exact ⟨ih'.1, TableOK.cons_head hsize
                      (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩

          | some entry =>
              obtain ⟨stamps, doms, res⟩ := entry
              have hoktail : TableOK ps v f seens := TableOK.tail hok
              have ih' := ih seens hoktail hloc.tail
              have hok0 : ∀ hne : p.watches ≠ [], EntryOK p v f ⟨stamps, doms, res⟩ :=
                fun hne => hok.entry 0 p ⟨stamps, doms, res⟩ rfl (by simp) hne
              by_cases hmatch :
                  (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = true
              · have hboth := hmatch
                simp only [Bool.and_eq_true] at hboth
                have hstamp : stampNatEqB stamps (watchVersions v p.watches) = true := hboth.1
                have hne : p.watches ≠ [] := by simpa using hboth.2
                have hveq : watchVersions v p.watches = stamps :=
                  (stampNatEqB_sound hstamp).symm
                have hdom : watchStamp f p.watches = doms := (hok0 hne).domains_eq hveq
                have hrun_eq : p.run (frameState f) = res := (hok0 hne).run_eq f hdom
                cases res with
                | stable =>
                    simp only [schedAux_some_stable f v p ps stamps doms seens hmatch,
                      scanPropagators, hrun_eq]
                    exact ⟨ih'.1, TableOK.cons_head hsize hok0 ih'.2⟩
                | conflict c =>
                    simp only [schedAux_some_conflict f v p ps stamps doms c seens hmatch,
                      scanPropagators, hrun_eq]
                    exact ⟨by first | rfl | trivial, TableOK.cons_head hsize hok0 hoktail⟩
                | implied l r =>
                    by_cases hprod : productive l f = true
                    · simp only [schedAux_some_implied_hit f v p ps stamps doms l r seens hmatch hprod,
                        scanPropagators, hrun_eq, if_pos hprod]
                      exact ⟨by first | rfl | trivial, TableOK.cons_head hsize hok0 hoktail⟩
                    · simp only [schedAux_some_implied_miss f v p ps stamps doms l r seens hmatch hprod,
                        scanPropagators, hrun_eq, if_neg hprod]
                      exact ⟨ih'.1, TableOK.cons_head hsize hok0 ih'.2⟩
              · have hmatch' :
                    (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) = false := by
                  cases h : (stampNatEqB stamps (watchVersions v p.watches) && !p.watches.isEmpty) with
                  | false => rfl
                  | true => exact absurd h hmatch
                cases hrun : p.run (frameState f) with
                | stable =>
                    simp only [schedAux_miss_stable f v p ps stamps doms res seens hmatch' hrun,
                      scanPropagators, hrun]
                    exact ⟨ih'.1, TableOK.cons_head hsize
                      (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩
                | conflict c =>
                    simp only [schedAux_miss_conflict f v p ps stamps doms res seens hmatch' c hrun,
                      scanPropagators, hrun]
                    exact ⟨by first | rfl | trivial, TableOK.cons_head hsize hok0 hoktail⟩
                | implied l r' =>
                    by_cases hprod : productive l f = true
                    · simp only [schedAux_miss_implied_hit f v p ps stamps doms res seens hmatch'
                        l r' hrun hprod, scanPropagators, hrun, if_pos hprod]
                      exact ⟨by first | rfl | trivial, TableOK.cons_head hsize hok0 hoktail⟩
                    · simp only [schedAux_miss_implied_miss f v p ps stamps doms res seens hmatch'
                        l r' hrun hprod, scanPropagators, hrun, if_neg hprod]
                      exact ⟨ih'.1, TableOK.cons_head hsize
                        (fun hne => EntryOK.of_local_run (hlocp hne) hrun) ih'.2⟩

/-- **THE EQUIVALENCE (public scan form)**: consistency of the scheduler's
version-stamp table makes the scheduled scan return exactly the full scan's
event. The scan syncs the version vector to the frame first
(`PropScheduler.sync`); `TableOK.sync` transports the table across that sync. -/
theorem scanPropagatorsSched_fst_eq {f : BranchFrame} {sched : PropScheduler}
    {props : List Propagator} (hok : PropSchedulerOK props sched)
    (hloc : PropLocal props) :
    (scanPropagatorsSched f sched props).1 = scanPropagators f props := by
  simp only [scanPropagatorsSched]
  exact (scanPropagatorsSchedAux_spec (f := f) (v := (sched.sync f).versions)
    props (sched.sync f).seen (TableOK.sync hok.1) hloc).1

/-- The table returned by a scheduled scan of a locally-sound propagator
list stays consistent; the E1 queue fields are carried through untouched. -/
theorem scanPropagatorsSched_OK {f : BranchFrame} {sched : PropScheduler}
    {props : List Propagator} (hok : PropSchedulerOK props sched)
    (hloc : PropLocal props) : PropSchedulerOK props (scanPropagatorsSched f sched props).2 := by
  refine ⟨?_, ?_⟩
  · simp only [scanPropagatorsSched]
    rw [PropScheduler.sync_vframe]
    exact (scanPropagatorsSchedAux_spec (f := f) (v := (sched.sync f).versions)
      props (sched.sync f).seen (TableOK.sync hok.1) hloc).2
  · have h1 : (scanPropagatorsSched f sched props).2.work = sched.work := by
      simp only [scanPropagatorsSched, PropScheduler.sync_work]
    have h2 : (scanPropagatorsSched f sched props).2.qframe = sched.qframe := by
      simp only [scanPropagatorsSched, PropScheduler.sync_qframe]
    rw [h1, h2]
    exact hok.2

/-- **THE EQUIVALENCE (event-selection form)**: the scheduled event selection
agrees with the certified `nextPruningEvent` (database scan — through
`scanDatabaseFast_eq` — and liveness gates unchanged). -/
theorem nextPruningEventSched_fst_eq (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause)
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (nextPruningEventSched original props sched f db).1
      = nextPruningEvent original props f db := by
  rw [nextPruningEventSched, scanDatabaseFast_eq]
  cases hdb : scanDatabase original f db with
  | stable =>
      simp only [nextPruningEvent, hdb]
      split
      · exact scanPropagatorsSched_fst_eq hok hloc
      · rfl
  | conflict cs => simp only [nextPruningEvent, hdb]
  | implied l c lr fl =>
      simp only [nextPruningEvent, hdb]
      split <;> rfl

end LeanFzn.Solver.Propagation
