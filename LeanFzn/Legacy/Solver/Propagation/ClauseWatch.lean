/-
File: LeanFzn/Solver/Propagation/ClauseWatch.lean

Purpose (PLAN tasks W0/W1): the WATCHED-CLAUSE INDEX CORE for finite-domain
literals — a persistent, exactly-equivalent replacement for the per-step full
learned-database scan `scanDatabase` (`Pruning.lean`).

The certified reference route rescans the WHOLE learned database at every
propagation step (`scanDatabase` -> `clauseRemaining` -> `literalImpossible`),
and the fast executable twin `scanDatabaseFast` (`DbScanIndex.lean`) has the
same shape. The index built here carries, per database clause, a pair of
WATCHED POSITIONS `(i, j)` whose literals were possible when the entry was
recorded and such that every NON-watched literal was already impossible
there (`WatchEntryOK`). Impossibility is MONOTONE under domain narrowing (every
value of the narrower frame occurs in the ancestor domains), so between
restores the recorded entries keep their meaning: a clause whose watch slots
are untouched has at least two remaining literals and the scan may skip it
WITHOUT reading a single literal.

Structure (per `ClauseWatch`):

* `basis : List Domain` — the `Frame.domains` list at the establishment frame;
* `entries : List (Option (Nat × Nat))` — aligned with the scanned database;
* `fresh : Bool` — `false` forces the full ESTABLISH pass.

Rules of the watched scan `scanDatabaseWatch` (exactly mirroring
`scanDatabase`, early exit and payloads included):

* guard false (`fresh = false`, or misaligned) -> ESTABLISH pass: run the
  certified per-clause classification in database order, return exactly the
  reference event, and record for every clause it can an entry valid at
  `Frame.domains f` (`none` = no valid entry / no remaining literal,
  `(i,i)` = exactly one remaining literal, `(i,j)` = exactly two remaining
  literals); clauses after the first event are padded with `none`.
* guard true -> fast pass: walk clauses with their entries. An entry
  `some (i,j)` with `i < j` whose two watch slots are unchanged since the
  basis (`changedSlotsB`, structural equality of the slot domains through the
  sound Boolean `Dom.eqB`) skips the clause — non-watched impossibility persists
  by monotonicity, watched possibility persists by slot equality, so at least
  two literals remain (the reference scan skips it too). Every other clause
  is re-decided exactly as the reference classifier does: `watchClassify`
  re-reads the two watch positions (valid because the entry pins the whole
  remaining set to the watches), `clauseClassifyD` re-classifies an entry-less
  clause; conflicts and productive units terminate the scan with the identical
  payload. The fast pass KEEPS the entries it walked: a dead watch leaves no
  valid replacement at the same basis (all non-watched literals were
  impossible at the basis and stay impossible), and keeping the old entry is
  sound because the skip rule only fires on slots that still equal the basis.

Delivered theorems:

* `scanDatabaseWatch_fst_eq` — EVENT EQUALITY with the certified
  `scanDatabase` whenever the index is consistent at the CURRENT frame
  (`WatchOK f db w`);
* `scanDatabaseWatch_spec_of_table` — the general fast-pass statement: at a
  frame `f` narrower than the recording basis, a consistent index
  (`WatchTableOK basis f db w`) yields the same event AND the index stays
  consistent;
* `establish_WatchOK` — the establish pass returns an index valid at the
  current frame;
* `scanDatabaseWatch_WatchOK` / `scanDatabaseWatch_reset_fst` — preservation
  and the `ClauseWatch.reset` safety facts;
* `WatchOK.descend` — the paper argument the fast pass rests on: entries
  recorded at a frame stay valid (at the old basis) at any frame the old one
  descends to, provided the newer frame is LIVE; `two_le_clauseRemaining_of_watchesClear`
  is the "up to watch-slot change" clause-level form.

DESIGN NOTE (first-order reformulations, PLAN §3 "freeze statements"):
`WatchEntryOK` is defined through the frame-free `EntryOKD` on a raw
`List Domain` (the basis is a domain list, not a frame); bounds are
carried existentially instead of as `c[i]` proof arguments so that every
statement stays first-order. The frame-level `WatchEntryOK f c e` is
`EntryOKD (Frame.domains f) c e`; it is a convenience alias no other
declaration of this module uses. The name was deliberately chosen to avoid
the `EntryOK`/`EntriesOK` names already exported by
`ScheduledPropagation` (a different propagator-table predicate), so a module
importing both needs no qualification. `literalImpossible_mono_frameDescends` takes the unfolding of
`FrameDescendsFrom g f` (BackjumpFrontier) as an explicit hypothesis —
`FrameDescendsFrom` is definitionally that function — so this module does not
depend on the backjump layer; it needs LIVENESS (`frameLiveB g`) because a
coverless frame admits no assignment to descend.
`two_le_clauseRemaining_of_watchesClear` carries a descent hypothesis for
interface stability but its proof does NOT use it: slot equality alone makes
both watches possible at the new frame, which already certifies two remaining
literals.

DAG: DbScanIndex (Pruning + ClausePropagation) + Semantics.ValueEquality ->
ClauseWatch -> (future version-keyed scheduler). The appended section
"SELF-VALIDATING WATCH ENTRIES (EVENT-KEYED, NO DATABASE OR BASIS GUARD)"
implements the final invalidation design agreed after the measured guard
blocker: an entry stores the two watched POSITIONS with the LITERALS recorded
there, and every use re-checks the clause at those positions and decides both
literals' possibility at the CURRENT frame from `frameDomainArray` /
`sumsOfArray`. There is NO database comparison, NO recording basis, NO
descent check and NO establish pass: a learned-clause insertion shifts
entries, which simply fail self-validation and are re-recorded during
classification; a restoration is handled the same way (`alignEntries` is a
pure performance heuristic). The wrapper is unconditional
(`scanDatabaseWatch2_fst_eq`, and `scanDatabaseWatch2_fst_eq_fast` against the
oracle) and carries only the per-entry distinctness invariant plus the
per-scan work counters in `WatchIndex.work`.

It is deliberately NOT wired into the scheduled dispatcher. Measured with
`tests_heur_timing --watch 46 300000` / `--watch-battery 400000` (oracle =
the wired `scanDatabaseFast`, same states, 0 event disagreements over 8507
FBDk04 steps and the 3418-step battery):

* FBDk04 bound-46 walk (db to 4047, 1619 visited clauses/step): oracle
  816-847 ms vs watched 1966-2044 ms (2.4x), with the whole guard eliminated
  (setup = `frameDomainArray` + `sumsOfArray` = 4 ms total), 12.95M skips
  (94% of visited clauses) and only 155k rechecks + 669k classifies;
* battery (43 instances): oracle 20-22 ms vs watched 187-206 ms (8-9x);
  skips 81k, classifies 82k, rechecks 7k (half the visited clauses are
  reclassified because the propagated literals ARE the watched ones).

The residual blocker is per-clause cost, not invalidation: one skip costs
~150 ns on FBDk04 (two positional reads, two `BEq Literal` comparisons and
two `literalImpossibleFast` checks plus the functional list/counter
threading), while the oracle's summary-driven classification costs ~60 ns per
clause; a battery reclassification costs ~1 µs.

PLAN §3.4 UPDATE (2026-10-24): the version-keyed variant this header asked
for is now implemented and measured in `VersionWatch.lean` (with the
`SlotVersions` discipline in `SlotVersions.lean`). It removes the clause
reads from the fast path (generation + two slot-version comparisons), aligns
entries across learned-clause prepends (`VWatchOK.prepend`) and refreshes a
version-stale-but-still-possible watch from the slot summaries. Measured,
0 event disagreements: FBDk04 oracle 899-932 ms vs versioned 1349-1380 ms
(1.5x) and battery oracle 14-15 ms vs versioned 25 ms. The remaining cost is
the per-clause entry-list rebuild (~13.8M cons cells per FBDk04 run) plus the
second first-two-positions pass on the ~0.8M reclassified clauses; the
domain stamp is also coarser than the oracle summary test. It is therefore
retained UNWIRED; the wired route stays on `scanDatabaseFast`.
-/
import LeanFzn.Legacy.Solver.Propagation.DbScanIndex
import LeanFzn.Semantics.ValueEquality
open LeanFzn.Semantics LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Slot-indexed impossibility and monotonicity under narrowing -/

/-- Enumeration membership implies domain membership. -/
theorem mem_of_mem_enum {d : Domain} {v : Value} (h : v ∈ Dom.enum d) : v ∈ d := by
  rw [DomainLike.mem_iff, domElems_eq_enum]
  exact h

/-- Domain membership implies enumeration membership. -/
theorem mem_enum_of_mem {d : Domain} {v : Value} (h : v ∈ d) : v ∈ Dom.enum d := by
  rw [← domElems_eq_enum, ← DomainLike.mem_iff]
  exact h

/-- `literalImpossible` against a raw `Frame.domains` list (no frame needed:
the certified predicate only reads `Frame.domains`). -/
def literalImpossibleD (doms : List Domain) (l : Literal) : Bool :=
  (((doms.getD l.atom.slot Dom.empty).enum).all fun v => !l.valueHolds v)

/-- The certified `literalImpossible` is `literalImpossibleD` at the frame's
own domain list. -/
theorem literalImpossibleD_frame (f : BranchFrame) (l : Literal) :
    literalImpossibleD (Frame.domains f) l = literalImpossible f l := rfl

/-- Pointwise domain descent: every value the frame `f` still admits occurs in
the ancestor domain list `basis`. Frames only narrow between restores, so
`basis := Frame.domains f₀` of an ancestor frame satisfies this at every
descendant frame. -/
def DomainsDescend (basis : List Domain) (f : BranchFrame) : Prop :=
  ∀ (s : Nat) (v : Value),
    v ∈ (Frame.domains f).getD s Dom.empty → v ∈ basis.getD s Dom.empty

/-- **MONOTONICITY (pointwise list form)**: if every value of the frame `f`
occurs in `basis`, a literal impossible at `basis` stays impossible at `f`.
This is the semilattice fact the whole index rests on. -/
theorem literalImpossibleD_mono {basis : List Domain} {f : BranchFrame}
    (hd : DomainsDescend basis f) (l : Literal) :
    literalImpossibleD basis l = true → literalImpossible f l = true := by
  intro h
  unfold literalImpossibleD at h
  unfold literalImpossible
  exact List.all_eq_true.mpr fun v hv =>
    List.all_eq_true.mp h v
      (mem_enum_of_mem (hd l.atom.slot v (mem_of_mem_enum hv)))

/-- **MONOTONICITY (pointwise `List`-subset form, two frames)**: every value
of `g`'s domains occurring in `f`'s makes impossibility monotone `f → g`. -/
theorem literalImpossible_mono_subset {f g : BranchFrame}
    (hsub : ∀ (s : Nat) (v : Value),
      v ∈ (Frame.domains g).getD s Dom.empty →
        v ∈ (Frame.domains f).getD s Dom.empty)
    (l : Literal) :
    literalImpossible f l = true → literalImpossible g l = true :=
  literalImpossibleD_mono (basis := Frame.domains f) hsub l

/-! ### The `FrameDescendsFrom` form (needs liveness) -/

/-- Liveness of a frame as per-domain nonemptiness (`frameLiveB` unfolds). -/
theorem live_of_frameLiveB {g : BranchFrame} (h : frameLiveB g = true) :
    ∀ d ∈ g.doms, Dom.enum d ≠ [] := by
  intro d hd hnil
  have h1 : (!d.isEmpty) = true := List.all_eq_true.mp h d hd
  have hfalse : d.isEmpty = false := by simpa using h1
  have htrue : d.isEmpty = true := (Dom.isEmpty_eq_true_iff d).mpr hnil
  rw [htrue] at hfalse
  cases hfalse

/-- A list of nonempty domains has at least one complete assignment. -/
theorem allAssigns_nonempty_of_live {slots : List Domain}
    (hlive : ∀ d ∈ slots, Dom.enum d ≠ []) : ∃ tail, tail ∈ allAssigns slots := by
  induction slots with
  | nil => exact ⟨[], by simp [allAssigns]⟩
  | cons d ds ih =>
      match hd : Dom.enum d with
      | [] => exact absurd hd (hlive d (by simp))
      | w :: ws =>
          obtain ⟨tail, htail⟩ := ih fun d' hd' => hlive d' (List.mem_cons_of_mem _ hd')
          exact ⟨w :: tail,
            (mem_allAssigns_cons (d := d) hd ds (w :: tail)).mpr
              ⟨w, List.mem_cons_self .., tail, htail, rfl⟩⟩

/-- A list of nonempty domains has an assignment with a PRESCRIBED value at
any in-range position. -/
theorem exists_allAssigns_getElem {slots : List Domain}
    (hlive : ∀ d ∈ slots, Dom.enum d ≠ []) {i : Nat} {v : Value}
    (hv : v ∈ slots.getD i Dom.empty) :
    ∃ tail ∈ allAssigns slots, tail[i]? = some v := by
  induction slots generalizing i with
  | nil => simp at hv
  | cons d ds ih =>
      cases i with
      | zero =>
          simp only [List.getD_cons_zero] at hv
          match hd : Dom.enum d with
          | [] => exact absurd hd (hlive d (by simp))
          | w :: ws =>
              obtain ⟨tail, htail⟩ := allAssigns_nonempty_of_live
                fun d' hd' => hlive d' (List.mem_cons_of_mem _ hd')
              have hv' : v ∈ w :: ws := by
                rw [← hd]
                exact mem_enum_of_mem hv
              exact ⟨v :: tail,
                (mem_allAssigns_cons (d := d) hd ds (v :: tail)).mpr
                  ⟨v, hv', tail, htail, rfl⟩,
                rfl⟩
      | succ i =>
          simp only [List.getD_cons_succ] at hv
          obtain ⟨tail, htail, hget⟩ :=
            ih (fun d' hd' => hlive d' (List.mem_cons_of_mem _ hd')) hv
          match hd : Dom.enum d with
          | [] => exact absurd hd (hlive d (by simp))
          | w :: ws =>
              refine ⟨w :: tail, ?_, ?_⟩
              · exact (mem_allAssigns_cons (d := d) hd ds (w :: tail)).mpr
                  ⟨w, List.mem_cons_self .., tail, htail, rfl⟩
              · simpa using hget

/-- In a live frame, every value of a slot domain extends to a covering
assignment that reads it at that slot. -/
theorem exists_frameCovers_getElem (g : BranchFrame)
    (hlive : ∀ d ∈ g.doms, Dom.enum d ≠ []) {s : Nat} {v : Value}
    (hv : v ∈ (Frame.domains g).getD s Dom.empty) :
    ∃ a, FrameCovers g a ∧ a[s]? = some v :=
  exists_allAssigns_getElem hlive hv

/-- **MONOTONICITY (`FrameDescendsFrom` form)**: on LIVE frames, semantic
descent (every assignment covered by `g` was covered by the ancestor `f`)
implies impossibility monotonicity. This is the paper argument; `hdesc` is
definitionally `FrameDescendsFrom g f` (BackjumpFrontier), inlined to keep
this module's DAG narrow. Liveness is necessary: a coverless `g` admits no
assignment to descend, so it can still hold values `f` has lost. -/
theorem literalImpossible_mono_frameDescends {f g : BranchFrame}
    (hdesc : ∀ a, FrameCovers g a → FrameCovers f a)
    (hlive : frameLiveB g = true) (l : Literal) :
    literalImpossible f l = true → literalImpossible g l = true := by
  intro himp
  by_cases hg : literalImpossible g l = true
  · exact hg
  · exfalso
    have hfalse : literalImpossible g l = false := Bool.eq_false_iff.mpr hg
    have hfalse' : (((Frame.domains g).getD l.atom.slot Dom.empty).enum).all
        (fun v => !l.valueHolds v) = false := hfalse
    obtain ⟨v, hv, hnot⟩ := List.all_eq_false.mp hfalse'
    have hvdom : v ∈ (Frame.domains g).getD l.atom.slot Dom.empty := mem_of_mem_enum hv
    have hval : l.valueHolds v = true := by
      cases h : l.valueHolds v with
      | false => exact absurd (by simp [h]) hnot
      | true => rfl
    obtain ⟨a, hcover, ha⟩ :=
      exists_frameCovers_getElem g (live_of_frameLiveB hlive) hvdom
    have heval : l.eval a = some true := (valueHolds_read ha).mp hval
    have := literalImpossible_false (hdesc a hcover) heval
    rw [himp] at this
    exact absurd this (by simp)

/-- **DOMAIN DESCENT FROM FRAME DESCENT**: a live descendant frame's slot
values all occur in the ancestor's domains. This converts the semantic
`FrameDescendsFrom` (the only form the scheduler maintains) into the
pointwise `DomainsDescend` shape the index proofs consume. -/
theorem domains_descend_of_frameDescends {f g : BranchFrame}
    (hdesc : ∀ a, FrameCovers g a → FrameCovers f a)
    (hlive : frameLiveB g = true) :
    DomainsDescend (Frame.domains f) g := by
  intro s v hv
  obtain ⟨a, hcover, ha⟩ :=
    exists_frameCovers_getElem g (live_of_frameLiveB hlive) hv
  exact (hdesc a hcover).fits.2 s v ha

/-! ## Values equality and the changed-slot map -/

/-- Soundness of the Boolean domain equality (`valuesEqB`): `Value` has no
`DecidableEq`, so every domain comparison goes through this test. -/
theorem valuesEqB_sound {xs ys : List Value} (h : valuesEqB xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [valuesEqB] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [valuesEqB] at h
      | cons y ys =>
          simp only [valuesEqB, Bool.and_eq_true] at h
          rw [LeanFzn.Semantics.Evaluation.value_eqB_iff.mp h.1, ih h.2]

/-- `valuesEqB` is reflexive. -/
theorem valuesEqB_self (xs : List Value) : valuesEqB xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [valuesEqB, Bool.and_eq_true]
      exact ⟨LeanFzn.Semantics.Evaluation.value_eqB_refl x, ih⟩

/-- The frame's slot domains against the basis, slot by slot, as a Bool list:
`true` at slot `s` iff the slot domains differ STRUCTURALLY (`Dom.eqB`, no
enumeration) or the basis has no such slot. FIRST-ORDER recursion — no
`zip`/`length` intermediate lists. -/
def changedSlotsList : List Domain → List Domain → List Bool
  | [], [] => []
  | [], doms@(_ :: _) => doms.map fun _ => true
  | bs@(_ :: _), [] => bs.map fun _ => true
  | b :: bs, d :: ds => (!Dom.eqB d b) :: changedSlotsList bs ds

/-- The changed-slot map of the fast pass. Slot `s` is `true` iff
`(Frame.domains f).getD s []` differs from `basis.getD s []`. -/
def changedSlotsB (basis : List Domain) (f : BranchFrame) : Array Bool :=
  (changedSlotsList basis (Frame.domains f)).toArray

/-- A constant-`true` map never reads `false`. -/
theorem map_const_true_ne_some_false {l : List α} {s : Nat} :
    (l.map (fun _ => true))[s]? ≠ some false := by
  intro h
  rw [List.getElem?_map] at h
  cases hl : l[s]? with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some a => rw [hl] at h; exact absurd h (by simp)

/-- A `false` entry of the Bool list certifies list equality of the two slot
domains at that position. -/
theorem changedSlotsList_sound :
    ∀ (basis doms : List Domain) (s : Nat),
      (changedSlotsList basis doms)[s]? = some false →
      valuesEqB (Dom.enum (doms.getD s Dom.empty))
        (Dom.enum (basis.getD s Dom.empty)) = true := by
  intro basis
  induction basis with
  | nil =>
      intro doms s h
      cases doms with
      | nil => simp [changedSlotsList] at h
      | cons d ds =>
          exact absurd h (map_const_true_ne_some_false (l := d :: ds) (s := s))
  | cons b bs ih =>
      intro doms s h
      cases doms with
      | nil =>
          exact absurd h (map_const_true_ne_some_false (l := b :: bs) (s := s))
      | cons d ds =>
          cases s with
          | zero =>
              have h' : !Dom.eqB d b = false := by
                simpa [changedSlotsList] using h
              have hdb : Dom.eqB d b = true := by simpa using h'
              rw [Dom.eqB_sound hdb]
              exact valuesEqB_self _
          | succ s =>
              have h' : (changedSlotsList bs ds)[s]? = some false := by
                simpa [changedSlotsList] using h
              have := ih ds s h'
              simpa [List.getD_cons_succ] using this

/-- **SOUNDNESS of `changedSlotsB`**: a `false` lookup stalls the two slot
domains as EQUAL lists. -/
theorem changedSlotsB_sound {basis : List Domain} {f : BranchFrame} {s : Nat}
    (h : (changedSlotsB basis f)[s]? = some false) :
    valuesEqB (Dom.enum ((Frame.domains f).getD s Dom.empty))
      (Dom.enum (basis.getD s Dom.empty)) = true := by
  rw [changedSlotsB, List.getElem?_toArray] at h
  exact changedSlotsList_sound basis (Frame.domains f) s h

/-- An `Option Bool` that defaults to `true` and reads `false` must be
`some false`. -/
theorem option_getD_true_eq_false {a : Option Bool} (h : a.getD true = false) :
    a = some false := by
  cases a with
  | none => simp at h
  | some b => cases b <;> simp_all

/-- The defaulted lookup used by `watchesClear` also certifies slot equality. -/
theorem changedSlotsB_getD_false {basis : List Domain} {f : BranchFrame} {s : Nat}
    (h : (changedSlotsB basis f)[s]?.getD true = false) :
    valuesEqB (Dom.enum ((Frame.domains f).getD s Dom.empty))
      (Dom.enum (basis.getD s Dom.empty)) = true :=
  changedSlotsB_sound (option_getD_true_eq_false h)

/-- The two watch slots of a clause entry are UNCHANGED since the basis
(`false` = unchanged; unknown slots count as changed). Array lookups only —
this test reads no literal and no domain value. -/
def watchesClear (changed : Array Bool) (c : Clause) (i j : Nat) : Bool :=
  (match c[i]? with
   | some li => !(changed[li.atom.slot]?.getD true)
   | none => false) &&
  (match c[j]? with
   | some lj => !(changed[lj.atom.slot]?.getD true)
   | none => false)

/-- **SOUNDNESS of `watchesClear`**: each present watch position's slot is
marked unchanged. -/
theorem watchesClear_sound {changed : Array Bool} {c : Clause} {i j : Nat}
    (h : watchesClear changed c i j = true) :
    (∀ l, c[i]? = some l → changed[l.atom.slot]?.getD true = false) ∧
    (∀ l, c[j]? = some l → changed[l.atom.slot]?.getD true = false) := by
  have h' := h
  simp only [watchesClear, Bool.and_eq_true_iff] at h'
  constructor <;> intro l hl
  · have h1 := h'.1
    rw [hl] at h1
    dsimp only at h1
    simpa using h1
  · have h2 := h'.2
    rw [hl] at h2
    dsimp only at h2
    simpa using h2

/-- **WATCH-SLOT STABILITY**: an unchanged watch slot has the same literal
impossibility at the new frame as at the basis. -/
theorem watchesClear_literalImpossible {basis : List Domain} {f : BranchFrame}
    {c : Clause} {i j k : Nat} {l : Literal}
    (h : watchesClear (changedSlotsB basis f) c i j = true)
    (hk : k = i ∨ k = j) (hl : c[k]? = some l) :
    literalImpossible f l = literalImpossibleD basis l := by
  have hclear : (changedSlotsB basis f)[l.atom.slot]?.getD true = false := by
    rcases hk with rfl | rfl
    · exact (watchesClear_sound h).1 l hl
    · exact (watchesClear_sound h).2 l hl
  have h2 := valuesEqB_sound (changedSlotsB_getD_false hclear)
  show literalImpossibleD (Frame.domains f) l = literalImpossibleD basis l
  unfold literalImpossibleD
  rw [h2]

/-! ## Per-clause remaining-set lemmas -/

/-- Two distinct, in-range positions whose literals satisfy a Bool test make
the filtered list at least two long. -/
theorem two_le_length_filter {α : Type} {l : List α} {p : α → Bool}
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) :
    2 ≤ (l.filter p).length := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl hij
          | succ j =>
              have hpa : p a = true := by simpa using hpi
              rw [List.filter_cons_of_pos hpa]
              have hj' : j < t.length := Nat.lt_of_succ_lt_succ hj
              have hmem : t[j]'hj' ∈ t.filter p :=
                List.mem_filter.mpr ⟨List.getElem_mem .., by simpa using hpj⟩
              have hpos : 0 < (t.filter p).length :=
                List.length_pos_iff.mpr fun hnil => by
                  rw [hnil] at hmem
                  simp at hmem
              simp only [List.length_cons]
              omega
      | succ i =>
          cases j with
          | zero =>
              have hpa : p a = true := by simpa using hpj
              rw [List.filter_cons_of_pos hpa]
              have hi' : i < t.length := Nat.lt_of_succ_lt_succ hi
              have hmem : t[i]'hi' ∈ t.filter p :=
                List.mem_filter.mpr ⟨List.getElem_mem .., by simpa using hpi⟩
              have hpos : 0 < (t.filter p).length :=
                List.length_pos_iff.mpr fun hnil => by
                  rw [hnil] at hmem
                  simp at hmem
              simp only [List.length_cons]
              omega
          | succ j =>
              have h2 := ih (i := i) (j := j) (by simpa using hi) (by simpa using hj)
                (by simpa using hij) (by simpa using hpi) (by simpa using hpj)
              rw [List.filter_cons]
              by_cases hpa : p a = true
              · simp only [hpa, if_true, List.length_cons]
                omega
              · rw [if_neg hpa]
                exact h2

/-- If `p` falsifies a clause at every position, the filtered list is empty. -/
theorem clauseRemaining_eq_nil_of_entry (f : BranchFrame) (c : Clause)
    (hdead : ∀ k (hk : k < c.length),
      literalImpossible f (c[k]'hk) = true) :
    clauseRemaining f c = [] := by
  show c.filter (fun l => !literalImpossible f l) = []
  induction c with
  | nil => rfl
  | cons a t ih =>
      have hdead0 : literalImpossible f a = true := by
        have := hdead 0 (by simp)
        simpa using this
      rw [List.filter_cons_of_neg (by simp [hdead0])]
      exact ih fun k hk => by
        have := hdead (k + 1) (by simp; omega)
        simpa using this

/-- If `p` holds exactly at position `p` of a clause (all other positions
falsify it), the filtered list is the singleton of that literal. -/
theorem clauseRemaining_eq_singleton_of_entry (f : BranchFrame) (c : Clause)
    (p : Nat) (hp : p < c.length)
    (halive : literalImpossible f (c[p]'hp) = false)
    (hdead : ∀ k (hk : k < c.length), k ≠ p →
      literalImpossible f (c[k]'hk) = true) :
    clauseRemaining f c = [c[p]'hp] := by
  show c.filter (fun l => !literalImpossible f l) = [c[p]'hp]
  revert hp halive hdead p
  induction c with
  | nil => intro p hp _ _; simp at hp
  | cons a t ih =>
      intro p hp halive hdead
      cases p with
      | zero =>
          have hnil : t.filter (fun l => !literalImpossible f l) = [] :=
            clauseRemaining_eq_nil_of_entry f t fun k hk => by
              have := hdead (k + 1) (by simp; omega) (by omega)
              simpa using this
          rw [List.filter_cons_of_pos (by simpa using halive)]
          simp only [List.getElem_cons_zero]
          rw [hnil]
      | succ p =>
          have hdead0 : literalImpossible f a = true := by
            have := hdead 0 (by simp) (by omega)
            simpa using this
          rw [List.filter_cons_of_neg (by simp [hdead0])]
          have htrans : ∀ k (hk : k < t.length), k ≠ p →
              literalImpossible f (t[k]'hk) = true := by
            intro k hk hkp
            have := hdead (k + 1) (by simp; omega) (by omega)
            simpa using this
          have halive_t : literalImpossible f (t[p]'(by simpa using hp)) = false := by
            simpa using halive
          simp only [List.getElem_cons_succ]
          rw [ih p (by simpa using hp) halive_t htrans]

/-! ## The entry predicate -/

/-- **ENTRY VALIDITY (core, domain list)**. `none` = no claim. For
`some (i, j)`: the two positions are in range with `i ≤ j`, every OTHER
position's literal is impossible, and both watched literals are possible.
For `i = j` this pins exactly one remaining literal; for `i < j` at least
two — both legal. Bounds are carried existentially to keep every consumer
first-order (the frame-level `WatchEntryOK` is the requested frame form). -/
def EntryOKD (doms : List Domain) (c : Clause) : Option (Nat × Nat) → Prop
  | none => True
  | some (i, j) =>
      ∃ (hij : i ≤ j) (hj : j < c.length),
        (∀ (k : Nat) (hk : k < c.length), k ≠ i → k ≠ j →
          literalImpossibleD doms (c[k]'hk) = true) ∧
        literalImpossibleD doms (c[i]'(Nat.lt_of_le_of_lt hij hj)) = false ∧
        literalImpossibleD doms (c[j]'hj) = false

/-- **ENTRY VALIDITY (frame form, as specified)**: `WatchEntryOK f c e` is entry
validity at the frame's own domain list. -/
def WatchEntryOK (f : BranchFrame) (c : Clause) : Option (Nat × Nat) → Prop :=
  EntryOKD (Frame.domains f) c

/-- **THE INDEX INVARIANT (aligned form)**: every database clause's recorded
entry (itself an `Option`) is valid at the domain list. -/
def WatchEntriesOK (doms : List Domain) (db : List Clause)
    (es : List (Option (Nat × Nat))) : Prop :=
  ∀ (j : Nat) (c : Clause) (e : Option (Nat × Nat)),
    db[j]? = some c → es[j]? = some e → EntryOKD doms c e

/-- Tail of an aligned consistent entry list. -/
theorem WatchEntriesOK.tail {doms : List Domain} {c : Clause}
    {e : Option (Nat × Nat)} {rest : List Clause} {es : List (Option (Nat × Nat))}
    (h : WatchEntriesOK doms (c :: rest) (e :: es)) : WatchEntriesOK doms rest es :=
  fun j c' e' hj he => h (j + 1) c' e' (by simpa using hj) (by simpa using he)

/-- Rebuild a consistent entry list with a valid head. -/
theorem WatchEntriesOK.cons_head {doms : List Domain} {c : Clause}
    {e : Option (Nat × Nat)} {rest : List Clause} {es : List (Option (Nat × Nat))}
    (h0 : EntryOKD doms c e) (htail : WatchEntriesOK doms rest es) :
    WatchEntriesOK doms (c :: rest) (e :: es) := by
  intro j c' e' hj he
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj he
      subst hj
      subst he
      exact h0
  | succ k =>
      exact htail k c' e' (by simpa using hj) (by simpa using he)

/-- Padding after the first event: every aligned entry is `none`, hence
vacuously valid. -/
theorem WatchEntriesOK.pad (doms : List Domain) (rest : List Clause) :
    WatchEntriesOK doms rest (rest.map fun _ => none) := by
  intro j c e hj he
  rw [List.getElem?_map, hj] at he
  have he' : none = e := by simpa using he
  cases he'
  trivial

/-! ## Recording entries: positions of the remaining literals -/

/-- Indices of the remaining literals of a clause (against a domain list),
walking with an absolute position counter. FIRST-ORDER, no `filter`/`enum`. -/
def remIdx (doms : List Domain) : List Literal → Nat → List Nat
  | [], _ => []
  | l :: ls, idx =>
      match literalImpossibleD doms l with
      | true => remIdx doms ls (idx + 1)
      | false => idx :: remIdx doms ls (idx + 1)

/-- **MEMBERSHIP CHARACTERIZATION of `remIdx`**: exactly the in-range
positions of literals that are still possible. -/
theorem mem_remIdx {doms : List Domain} {lits : List Literal} :
    ∀ (idx k : Nat), k ∈ remIdx doms lits idx ↔
      ∃ (t : Nat) (ht : t < lits.length), k = idx + t ∧
        literalImpossibleD doms (lits[t]'ht) = false := by
  induction lits with
  | nil => intro idx k; simp [remIdx]
  | cons l ls ih =>
      intro idx k
      by_cases himp : literalImpossibleD doms l = true
      · simp only [remIdx, himp]
        rw [ih (idx + 1) k]
        constructor
        · rintro ⟨t, ht, hk, hp⟩
          exact ⟨t + 1, by simpa using ht, by omega, by simpa using hp⟩
        · rintro ⟨t, ht, hk, hp⟩
          cases t with
          | zero =>
              simp only [List.getElem_cons_zero] at hp
              rw [himp] at hp
              exact absurd hp (by simp)
          | succ t =>
              exact ⟨t, by simpa using ht, by omega, by simpa using hp⟩
      · have hfalse : literalImpossibleD doms l = false := Bool.eq_false_iff.mpr himp
        simp only [remIdx, hfalse]
        rw [List.mem_cons, ih (idx + 1) k]
        constructor
        · rintro (hk | ⟨t, ht, hk, hp⟩)
          · exact ⟨0, by simp, by omega, by simpa using hfalse⟩
          · exact ⟨t + 1, by simpa using ht, by omega, by simpa using hp⟩
        · rintro ⟨t, ht, hk, hp⟩
          cases t with
          | zero => left; omega
          | succ t =>
              right
              exact ⟨t, by simpa using ht, by omega, by simpa using hp⟩

/-- Every `remIdx` position is at or after the walk's starting index. -/
theorem remIdx_ge {doms : List Domain} {lits : List Literal} :
    ∀ (idx k : Nat), k ∈ remIdx doms lits idx → idx ≤ k := by
  induction lits with
  | nil => intro idx k hk; simp [remIdx] at hk
  | cons l ls ih =>
      intro idx k hk
      by_cases himp : literalImpossibleD doms l = true
      · simp only [remIdx, himp] at hk
        have := ih (idx + 1) k hk
        omega
      · have hfalse : literalImpossibleD doms l = false := Bool.eq_false_iff.mpr himp
        simp only [remIdx, hfalse, List.mem_cons] at hk
        rcases hk with hk | hk
        · omega
        · have := ih (idx + 1) k hk
          omega

/-- `remIdx` positions come out strictly increasing. -/
theorem remIdx_pairwise (doms : List Domain) (lits : List Literal) :
    ∀ (idx : Nat), (remIdx doms lits idx).Pairwise (· < ·) := by
  induction lits with
  | nil => intro idx; simp [remIdx]
  | cons l ls ih =>
      intro idx
      by_cases himp : literalImpossibleD doms l = true
      · simp only [remIdx, himp]
        exact ih (idx + 1)
      · have hfalse : literalImpossibleD doms l = false := Bool.eq_false_iff.mpr himp
        simp only [remIdx, hfalse]
        refine List.Pairwise.cons ?_ (ih (idx + 1))
        intro a ha
        have := remIdx_ge (idx + 1) a ha
        omega

/-- A membership in `remIdx` at index `0` exposes the literal's possibility
through any proof of the position bound (proof-irrelevant transport). -/
theorem literalImpossibleD_of_mem_remIdx {doms : List Domain} {c : Clause}
    {i : Nat} (hi : i < c.length) (hmem : i ∈ remIdx doms c 0) :
    literalImpossibleD doms (c[i]'hi) = false := by
  obtain ⟨t, ht, hit, hp⟩ := (mem_remIdx 0 i).mp hmem
  have heq : c[i]'hi = c[t]'ht := by
    have h1 := List.getElem?_eq_getElem hi
    have h2 : c[i]? = some (c[t]'ht) := by
      rw [show i = t by omega]
      exact List.getElem?_eq_getElem ht
    rw [h1] at h2
    exact Option.some.inj h2
  rw [heq]
  exact hp

/-- The entry recorded for a clause: `none` when it has no or at least three
remaining literals, `(i,i)` for exactly one, `(i,j)` for exactly two. -/
def clauseEntry (doms : List Domain) (c : Clause) : Option (Nat × Nat) :=
  match remIdx doms c 0 with
  | [] => none
  | [i] => some (i, i)
  | [i, j] => some (i, j)
  | _ => none

/-- **RECORDED ENTRIES ARE VALID** at the domain list they were recorded at. -/
theorem clauseEntry_ok (doms : List Domain) (c : Clause) :
    EntryOKD doms c (clauseEntry doms c) := by
  unfold clauseEntry
  cases h : remIdx doms c 0 with
  | nil => trivial
  | cons i t =>
      cases t with
      | nil =>
          have hmem : i ∈ remIdx doms c 0 := by rw [h]; simp
          obtain ⟨ti, hti, hii, _⟩ := (mem_remIdx 0 i).mp hmem
          have hilen : i < c.length := by omega
          refine ⟨Nat.le_refl i, hilen, ?_, ?_, ?_⟩
          · intro k hk hki _
            by_cases hc : literalImpossibleD doms (c[k]'hk) = true
            · exact hc
            · exfalso
              have hc' : literalImpossibleD doms (c[k]'hk) = false :=
                Bool.eq_false_iff.mpr hc
              have hmemk : k ∈ remIdx doms c 0 :=
                (mem_remIdx 0 k).mpr ⟨k, hk, by omega, hc'⟩
              rw [h] at hmemk
              simp only [List.mem_singleton] at hmemk
              omega
          · exact literalImpossibleD_of_mem_remIdx hilen hmem
          · exact literalImpossibleD_of_mem_remIdx hilen hmem
      | cons j t' =>
          cases t' with
          | nil =>
              have hmem_i : i ∈ remIdx doms c 0 := by rw [h]; simp
              have hmem_j : j ∈ remIdx doms c 0 := by rw [h]; simp
              obtain ⟨ti, hti, hii, _⟩ := (mem_remIdx 0 i).mp hmem_i
              obtain ⟨tj, htj, hjj, _⟩ := (mem_remIdx 0 j).mp hmem_j
              have hilen : i < c.length := by omega
              have hjlen : j < c.length := by omega
              have hpair := remIdx_pairwise doms c 0
              rw [h] at hpair
              have hijlt : i < j := (List.pairwise_cons.mp hpair).1 j (by simp)
              refine ⟨Nat.le_of_lt hijlt, hjlen, ?_, ?_, ?_⟩
              · intro k hk hki hkj
                by_cases hc : literalImpossibleD doms (c[k]'hk) = true
                · exact hc
                · exfalso
                  have hc' : literalImpossibleD doms (c[k]'hk) = false :=
                    Bool.eq_false_iff.mpr hc
                  have hmemk : k ∈ remIdx doms c 0 :=
                    (mem_remIdx 0 k).mpr ⟨k, hk, by omega, hc'⟩
                  rw [h] at hmemk
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmemk
                  rcases hmemk with hk' | hk'
                  · exact hki hk'
                  · exact hkj hk'
              · exact literalImpossibleD_of_mem_remIdx hilen hmem_i
              · exact literalImpossibleD_of_mem_remIdx hjlen hmem_j
          | cons k t'' => trivial

/-! ## First-order clause classification (reference-recursion shape) -/

/-- `clauseClassify` (`DbScanIndex.lean`) with the slot index replaced by the
frame itself: the same first-order recursion, same short-circuit, over
`literalImpossible` directly (no array copy for wide domains). -/
def clauseClassifyD (f : BranchFrame) :
    List Literal → Option Literal → Option (Option Literal)
  | [], none => none
  | [], some l => some (some l)
  | l :: ls, acc =>
    match literalImpossible f l with
    | true => clauseClassifyD f ls acc
    | false =>
      match acc with
      | none => clauseClassifyD f ls (some l)
      | some _ => some none

/-- **EQUIVALENCE (one remaining already seen)**: the list-based classifier
has the reference's compressed-remaining semantics. -/
theorem clauseClassifyD_some (f : BranchFrame) (c : Clause) (l₀ : Literal) :
    clauseClassifyD f c (some l₀)
      = (match c.filter (fun l => !literalImpossible f l) with
         | [] => some (some l₀)
         | _ => some none) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      rw [clauseClassifyD]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]

/-- **EQUIVALENCE (start state)**: the list-based classifier IS the reference
compressed remaining set `reduceRemaining (clauseRemaining f c)`. -/
theorem clauseClassifyD_none (f : BranchFrame) (c : Clause) :
    clauseClassifyD f c none = reduceRemaining (c.filter (fun l => !literalImpossible f l)) := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      rw [clauseClassifyD]
      by_cases himp : literalImpossible f l = true
      · rw [himp]
        rw [List.filter_cons_of_neg (p := fun l => !literalImpossible f l) (by simp [himp])]
        rw [ih]
      · have hf : literalImpossible f l = false := Bool.eq_false_iff.mpr himp
        rw [hf]
        rw [List.filter_cons_of_pos (p := fun l => !literalImpossible f l) (by simp [hf])]
        rw [clauseClassifyD_some f ls l]
        cases hq : ls.filter (fun l => !literalImpossible f l) with
        | nil => simp only [reduceRemaining]
        | cons q qs => simp only [reduceRemaining]

/-! ## Watch classification and the skip lemma -/

/-- Decide the compressed remaining set of a clause from its two watched
positions alone (valid when the entry pins every other position as
impossible): both dead -> conflict, exactly one alive -> unit on it,
both alive -> at least two remain (for `i = j` "both" means the single watch,
so a live single watch is a UNIT). -/
def watchClassify (f : BranchFrame) (c : Clause) (i j : Nat) :
    Option (Option Literal) :=
  match c[i]?, c[j]? with
  | some li, some lj =>
      match literalImpossible f li with
      | true =>
          match literalImpossible f lj with
          | true => none
          | false => some (some lj)
      | false =>
          match literalImpossible f lj with
          | true => some (some li)
          | false => if i = j then some (some li) else some none
  | _, _ => none

/-- **WATCH CLASSIFICATION IS THE REFERENCE CLASSIFICATION**: for an entry
valid at `basis` and a frame `f` it descends from, reading the two watch
positions decides `reduceRemaining (clauseRemaining f c)` exactly. -/
theorem watchClassify_eq {basis : List Domain} {f : BranchFrame} {c : Clause}
    {i j : Nat} (he : EntryOKD basis c (some (i, j))) (hd : DomainsDescend basis f) :
    watchClassify f c i j = reduceRemaining (clauseRemaining f c) := by
  obtain ⟨hij, hj, hother, hwi, hwj⟩ := he
  have hi : i < c.length := Nat.lt_of_le_of_lt hij hj
  by_cases hij_eq : i = j
  · rw [hij_eq] at hi hother ⊢
    rw [watchClassify, List.getElem?_eq_getElem hj]
    dsimp only
    by_cases hp : literalImpossible f (c[j]'hj) = true
    · rw [hp]
      have hdead : ∀ k (hk : k < c.length),
          literalImpossible f (c[k]'hk) = true := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj; exact hp
        · exact literalImpossibleD_mono hd (c[k]'hk) (hother k hk hkj hkj)
      rw [clauseRemaining_eq_nil_of_entry f c hdead]
      simp only [reduceRemaining]
    · have hp' : literalImpossible f (c[j]'hj) = false := Bool.eq_false_iff.mpr hp
      rw [hp']
      have hdead : ∀ k (hk : k < c.length), k ≠ j →
          literalImpossible f (c[k]'hk) = true :=
        fun k hk hkj => literalImpossibleD_mono hd (c[k]'hk) (hother k hk hkj hkj)
      rw [clauseRemaining_eq_singleton_of_entry f c j hj hp' hdead]
      simp only [reduceRemaining, if_true]
  · rw [watchClassify, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    dsimp only
    by_cases hpi : literalImpossible f (c[i]'hi) = true
    · rw [hpi]
      by_cases hpj : literalImpossible f (c[j]'hj) = true
      · rw [hpj]
        have hdead : ∀ k (hk : k < c.length),
            literalImpossible f (c[k]'hk) = true := by
          intro k hk
          by_cases hki : k = i
          · subst hki; exact hpi
          · by_cases hkj : k = j
            · subst hkj; exact hpj
            · exact literalImpossibleD_mono hd (c[k]'hk) (hother k hk hki hkj)
        rw [clauseRemaining_eq_nil_of_entry f c hdead]
        simp only [reduceRemaining]
      · have hpj' : literalImpossible f (c[j]'hj) = false := Bool.eq_false_iff.mpr hpj
        rw [hpj']
        have hdead : ∀ k (hk : k < c.length), k ≠ j →
            literalImpossible f (c[k]'hk) = true := by
          intro k hk hkj
          by_cases hki : k = i
          · subst hki; exact hpi
          · exact literalImpossibleD_mono hd (c[k]'hk) (hother k hk hki hkj)
        rw [clauseRemaining_eq_singleton_of_entry f c j hj hpj' hdead]
        simp only [reduceRemaining]
    · have hpi' : literalImpossible f (c[i]'hi) = false := Bool.eq_false_iff.mpr hpi
      rw [hpi']
      by_cases hpj : literalImpossible f (c[j]'hj) = true
      · rw [hpj]
        have hdead : ∀ k (hk : k < c.length), k ≠ i →
            literalImpossible f (c[k]'hk) = true := by
          intro k hk hki
          by_cases hkj : k = j
          · subst hkj; exact hpj
          · exact literalImpossibleD_mono hd (c[k]'hk) (hother k hk hki hkj)
        rw [clauseRemaining_eq_singleton_of_entry f c i hi hpi' hdead]
        simp only [reduceRemaining]
      · have hpj' : literalImpossible f (c[j]'hj) = false := Bool.eq_false_iff.mpr hpj
        rw [hpj', if_neg hij_eq]
        have h2 : 2 ≤ (clauseRemaining f c).length := by
          have := two_le_length_filter (l := c) (p := fun l => !literalImpossible f l)
            hi hj hij_eq (by simp [hpi']) (by simp [hpj'])
          simpa [clauseRemaining] using this
        cases hr : clauseRemaining f c with
        | nil => rw [hr] at h2; simp at h2
        | cons u us =>
            cases us with
            | nil => rw [hr] at h2; simp at h2
            | cons v vs => simp only [reduceRemaining]

/-- **THE SKIP LEMMA**: an entry whose two (distinct) watch slots are
unchanged since the basis has at least two remaining literals at the new
frame — the clause can be skipped WITHOUT any literal check. The watches stay
possible (slot equality) and everything else stays impossible (monotonicity);
this is the "entries stay valid up to watch-slot change" form the fast pass
uses. -/
theorem two_le_clauseRemaining_of_watchesClear {basis : List Domain}
    {f : BranchFrame} {c : Clause} {i j : Nat}
    (he : EntryOKD basis c (some (i, j))) (hij : i < j)
    (_hd : DomainsDescend basis f)
    (hwc : watchesClear (changedSlotsB basis f) c i j = true) :
    2 ≤ (clauseRemaining f c).length := by
  obtain ⟨hijle, hj, _, hwi, hwj⟩ := he
  have hi : i < c.length := Nat.lt_of_le_of_lt hijle hj
  have hci := watchesClear_literalImpossible hwc (Or.inl rfl) (List.getElem?_eq_getElem hi)
  have hcj := watchesClear_literalImpossible hwc (Or.inr rfl) (List.getElem?_eq_getElem hj)
  have hpif : literalImpossible f (c[i]'hi) = false := by
    rw [hci]
    exact hwi
  have hpjf : literalImpossible f (c[j]'hj) = false := by
    rw [hcj]
    exact hwj
  have := two_le_length_filter (l := c) (p := fun l => !literalImpossible f l)
    hi hj (Nat.ne_of_lt hij) (by simp [hpif]) (by simp [hpjf])
  simpa [clauseRemaining] using this

/-! ## The watched scan -/

/-- **THE FAST-PASS RECURSION** (event only; the index is kept unchanged by
the caller). One clause at a time:

* entry `some (i,j)`, `i < j`, both watch slots unchanged since the basis ->
  SKIP (no literal is read);
* every other entry -> re-decide: `watchClassify` for entries
  (the entry pins all non-watched positions, so the two watch reads suffice),
  `clauseClassifyD` for entry-less clauses;
* conflicts and productive units terminate exactly like the reference scan,
  with the identical `.conflict [c]` / `.implied l c false (!(original.contains c))`
  payloads.

A misaligned recursion (impossible under the length invariant, guarded at the
top level) falls back to the reference scan so the function is total. -/
def scanWatchAux (original : List Clause) (f : BranchFrame) (changed : Array Bool) :
    List Clause → List (Option (Nat × Nat)) → PruningEvent
  | [], _ => .stable
  | c :: rest, [] => scanDatabase original f (c :: rest)
  | c :: rest, e :: es =>
      match e with
      | none =>
          match clauseClassifyD f c none with
          | none => .conflict [c]
          | some none => scanWatchAux original f changed rest es
          | some (some l) =>
              if productiveFast l f then .implied l c false (!(original.contains c))
              else scanWatchAux original f changed rest es
      | some (i, j) =>
          if i < j && watchesClear changed c i j then
            scanWatchAux original f changed rest es
          else
            match watchClassify f c i j with
            | none => .conflict [c]
            | some none => scanWatchAux original f changed rest es
            | some (some l) =>
                if productiveFast l f then .implied l c false (!(original.contains c))
                else scanWatchAux original f changed rest es

/-- **EVENT EQUALITY OF THE FAST PASS**: at an aligned, basis-consistent entry
list, the watched recursion returns EXACTLY the certified `scanDatabase`
event — same order, same early exit, same payloads. -/
theorem scanWatchAux_eq (original : List Clause) (f : BranchFrame)
    (basis : List Domain) (db : List Clause) (es : List (Option (Nat × Nat)))
    (hl : es.length = db.length) (he : WatchEntriesOK basis db es)
    (hd : DomainsDescend basis f) :
    scanWatchAux original f (changedSlotsB basis f) db es
      = scanDatabase original f db := by
  induction db generalizing es with
  | nil =>
      cases es with
      | nil => rfl
      | cons e es' => simp at hl
  | cons c rest ih =>
      cases es with
      | nil => simp at hl
      | cons e es' =>
          have hl' : es'.length = rest.length := by
            simp only [List.length_cons] at hl
            omega
          have he' : WatchEntriesOK basis rest es' := WatchEntriesOK.tail he
          have ih' := ih es' hl' he'
          cases e with
          | none =>
              rw [scanWatchAux, clauseClassifyD_none f c]
              rw [show c.filter (fun l => !literalImpossible f l) = clauseRemaining f c
                from rfl]
              rw [scanDatabase]
              cases hr : clauseRemaining f c with
              | nil => simp only [reduceRemaining]
              | cons x xs =>
                  cases xs with
                  | nil =>
                      simp only [reduceRemaining]
                      rw [productiveFast_eq x f]
                      by_cases hp : productive x f = true
                      · rw [hp]; simp
                      · rw [Bool.eq_false_iff.mpr hp]
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact ih'
                  | cons y ys => simp only [reduceRemaining]; exact ih'
          | some ij =>
              cases ij with
              | mk i j =>
                  have hentry : EntryOKD basis c (some (i, j)) :=
                    he 0 c (some (i, j)) (by simp) (by simp)
                  by_cases hskip : (i < j
                      && watchesClear (changedSlotsB basis f) c i j) = true
                  · have hijlt : i < j :=
                      of_decide_eq_true (Bool.and_eq_true_iff.mp hskip).1
                    have hwc := (Bool.and_eq_true_iff.mp hskip).2
                    have h2 := two_le_clauseRemaining_of_watchesClear hentry hijlt hd hwc
                    rw [scanWatchAux, if_pos hskip]
                    rw [scanDatabase]
                    cases hr : clauseRemaining f c with
                    | nil => rw [hr] at h2; simp at h2
                    | cons x xs =>
                        cases xs with
                        | nil => rw [hr] at h2; simp at h2
                        | cons y ys => exact ih'
                  · rw [scanWatchAux, if_neg hskip]
                    rw [watchClassify_eq hentry hd]
                    rw [scanDatabase]
                    cases hr : clauseRemaining f c with
                    | nil => simp only [reduceRemaining]
                    | cons x xs =>
                        cases xs with
                        | nil =>
                            simp only [reduceRemaining]
                            rw [productiveFast_eq x f]
                            by_cases hp : productive x f = true
                            · rw [hp]; simp
                            · rw [Bool.eq_false_iff.mpr hp]
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact ih'
                        | cons y ys => simp only [reduceRemaining]; exact ih'

/-! ## The establish pass -/

/-- **THE ESTABLISH RECURSION**: the certified `scanDatabase` walk, recording
a valid entry (`clauseEntry`) for every clause it visits; after the first
event the remaining clauses are padded with `none`. -/
def establishAux (original : List Clause) (f : BranchFrame) :
    List Clause → PruningEvent × List (Option (Nat × Nat))
  | [] => (.stable, [])
  | c :: rest =>
      match clauseClassifyD f c none with
      | none =>
          (.conflict [c], clauseEntry (Frame.domains f) c :: rest.map fun _ => none)
      | some none =>
          let (ev, es) := establishAux original f rest
          (ev, clauseEntry (Frame.domains f) c :: es)
      | some (some l) =>
          if productiveFast l f then
            (.implied l c false (!(original.contains c)),
              clauseEntry (Frame.domains f) c :: rest.map fun _ => none)
          else
            let (ev, es) := establishAux original f rest
            (ev, clauseEntry (Frame.domains f) c :: es)

/-- **SPEC OF THE ESTABLISH PASS**: same event as `scanDatabase`, aligned
entries, and every aligned entry valid at `Frame.domains f`. -/
theorem establishAux_spec (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    (establishAux original f db).1 = scanDatabase original f db ∧
    (establishAux original f db).2.length = db.length ∧
    WatchEntriesOK (Frame.domains f) db (establishAux original f db).2 := by
  induction db with
  | nil => exact ⟨rfl, rfl, fun j c e hj _ => by simp at hj⟩
  | cons c rest ih =>
      rw [establishAux, clauseClassifyD_none f c]
      rw [show c.filter (fun l => !literalImpossible f l) = clauseRemaining f c from rfl]
      rw [scanDatabase]
      obtain ⟨ih1, ih2, ih3⟩ := ih
      cases hr : clauseRemaining f c with
      | nil =>
          simp only [reduceRemaining]
          refine ⟨trivial, ?_, ?_⟩
          · simp [List.length_map]
          · exact WatchEntriesOK.cons_head (clauseEntry_ok (Frame.domains f) c)
              (WatchEntriesOK.pad (Frame.domains f) rest)
      | cons x xs =>
          cases xs with
          | nil =>
              simp only [reduceRemaining]
              rw [productiveFast_eq x f]
              by_cases hp : productive x f = true
              · rw [hp]
                refine ⟨rfl, ?_, ?_⟩
                · simp [List.length_map]
                · exact WatchEntriesOK.cons_head (clauseEntry_ok (Frame.domains f) c)
                    (WatchEntriesOK.pad (Frame.domains f) rest)
              · rw [Bool.eq_false_iff.mpr hp]
                cases hrec : establishAux original f rest with
                | mk ev es =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have ih1' : ev = scanDatabase original f rest := by
                      show (ev, es).1 = scanDatabase original f rest
                      exact hrec ▸ ih1
                    have ih2' : es.length = rest.length := by
                      show (ev, es).2.length = rest.length
                      exact hrec ▸ ih2
                    have ih3' : WatchEntriesOK (Frame.domains f) rest es := by
                      show WatchEntriesOK (Frame.domains f) rest (ev, es).2
                      exact hrec ▸ ih3
                    exact ⟨ih1', by simp [ih2'],
                      WatchEntriesOK.cons_head (clauseEntry_ok (Frame.domains f) c) ih3'⟩
          | cons y ys =>
              simp only [reduceRemaining]
              cases hrec : establishAux original f rest with
              | mk ev es =>
                  have ih1' : ev = scanDatabase original f rest := by
                    show (ev, es).1 = scanDatabase original f rest
                    exact hrec ▸ ih1
                  have ih2' : es.length = rest.length := by
                    show (ev, es).2.length = rest.length
                    exact hrec ▸ ih2
                  have ih3' : WatchEntriesOK (Frame.domains f) rest es := by
                    show WatchEntriesOK (Frame.domains f) rest (ev, es).2
                    exact hrec ▸ ih3
                  exact ⟨ih1', by simp [ih2'],
                    WatchEntriesOK.cons_head (clauseEntry_ok (Frame.domains f) c) ih3'⟩

/-- The index structure: `basis` = `Frame.domains` at the establishment
frame, `entries` aligned with the scanned database, `fresh = false` forces a
full re-establishment (the `ClauseWatch.reset` state, and what every
database change / non-narrowing state transition must use). -/
structure ClauseWatch where
  basis : List Domain
  entries : List (Option (Nat × Nat))
  fresh : Bool

/-- The invalidated index: the next scan runs the establish pass. -/
def ClauseWatch.reset : ClauseWatch :=
  { basis := [], entries := [], fresh := false }

theorem ClauseWatch.reset_fresh : ClauseWatch.reset.fresh = false := rfl

theorem ClauseWatch.reset_entries : ClauseWatch.reset.entries = [] := rfl

theorem ClauseWatch.reset_basis : ClauseWatch.reset.basis = [] := rfl

/-- Run the establish pass and package a fresh index valid at `f`. -/
def establish (original : List Clause) (f : BranchFrame) (db : List Clause) :
    PruningEvent × ClauseWatch :=
  let r := establishAux original f db
  (r.1, { basis := Frame.domains f, entries := r.2, fresh := true })

theorem establish_fst_eq (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    (establish original f db).1 = scanDatabase original f db :=
  (establishAux_spec original f db).1

/-! ## Consistency invariants of the index -/

/-- **THE CURRENT-FRAME INVARIANT** (as specified): the index is fresh,
recorded at exactly the current `Frame.domains`, aligned, and every entry is
valid at the current frame. -/
def WatchOK (f : BranchFrame) (db : List Clause) (w : ClauseWatch) : Prop :=
  w.fresh = true ∧ w.basis = Frame.domains f ∧ w.entries.length = db.length ∧
  WatchEntriesOK (Frame.domains f) db w.entries

/-- **THE FAST-PASS INVARIANT**: the index is fresh and aligned, its entries
are valid at the RECORDING BASIS, and the current frame descends from that
basis. This is the invariant the runtime maintains between restores; the
fast scan consumes it (`scanDatabaseWatch_spec_of_table`). -/
def WatchTableOK (basis : List Domain) (f : BranchFrame) (db : List Clause)
    (w : ClauseWatch) : Prop :=
  w.fresh = true ∧ w.basis = basis ∧ DomainsDescend basis f ∧
  w.entries.length = db.length ∧ WatchEntriesOK basis db w.entries

/-- A current-frame invariant is a fast-pass invariant (descent is reflexive). -/
theorem WatchOK.toTable {f : BranchFrame} {db : List Clause} {w : ClauseWatch}
    (h : WatchOK f db w) : WatchTableOK (Frame.domains f) f db w :=
  ⟨h.1, h.2.1, fun _ _ hv => hv, h.2.2.1, h.2.2.2⟩

/-- The establish pass returns a current-frame-valid index. -/
theorem establish_WatchOK (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    WatchOK f db (establish original f db).2 := by
  obtain ⟨h1, h2, h3⟩ := establishAux_spec original f db
  exact ⟨rfl, rfl, h2, h3⟩

/-! ## The watched database scan -/

/-- **THE WATCHED-CLAUSE SCAN** (the W0/W1 deliverable). Guarded dispatch:
`fresh` and aligned -> the fast pass with the changed-slot map; otherwise the
full establish pass. The fast pass returns the walked index unchanged: a dead
watch leaves no valid replacement at the same basis (every non-watched
literal was impossible at the basis and stays impossible), and keeping the
old entry is sound because skipping only ever fires on slots that still equal
the basis. -/
def scanDatabaseWatch (original : List Clause) (f : BranchFrame) (w : ClauseWatch)
    (db : List Clause) : PruningEvent × ClauseWatch :=
  if w.fresh && (w.entries.length == db.length) then
    (scanWatchAux original f (changedSlotsB w.basis f) db w.entries, w)
  else
    establish original f db

/-- The guard of the fast pass. -/
theorem scanDatabaseWatch_guard {w : ClauseWatch} {db : List Clause} :
    (w.fresh && (w.entries.length == db.length)) = true ↔
      w.fresh = true ∧ w.entries.length = db.length := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨h1, beq_iff_eq.mp h2⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-- **THE EQUIVALENCE THEOREM (fast pass, general form)**: a basis-consistent
index at a frame it descends to makes the watched scan return EXACTLY the
certified `scanDatabase` event, and the index stays consistent. -/
theorem scanDatabaseWatch_spec_of_table (original : List Clause) (f : BranchFrame)
    (basis : List Domain) (w : ClauseWatch) (db : List Clause)
    (h : WatchTableOK basis f db w) :
    (scanDatabaseWatch original f w db).1 = scanDatabase original f db ∧
    WatchTableOK basis f db (scanDatabaseWatch original f w db).2 := by
  obtain ⟨hfresh, hbasis, hdesc, hlen, hentries⟩ := h
  have hguard : (w.fresh && (w.entries.length == db.length)) = true :=
    scanDatabaseWatch_guard.mpr ⟨hfresh, hlen⟩
  constructor
  · rw [scanDatabaseWatch, if_pos hguard, hbasis]
    exact scanWatchAux_eq original f basis db w.entries hlen hentries hdesc
  · rw [scanDatabaseWatch, if_pos hguard]
    show WatchTableOK basis f db w
    exact ⟨hfresh, hbasis, hdesc, hlen, hentries⟩

/-- **THE EQUIVALENCE THEOREM (DoD)**: on a current-frame-consistent index
(`WatchOK f db w`), `scanDatabaseWatch` returns exactly the certified
`scanDatabase` event. -/
theorem scanDatabaseWatch_fst_eq (original : List Clause) (f : BranchFrame)
    (w : ClauseWatch) (db : List Clause) (h : WatchOK f db w) :
    (scanDatabaseWatch original f w db).1 = scanDatabase original f db :=
  (scanDatabaseWatch_spec_of_table original f (Frame.domains f) w db h.toTable).1

/-- Same event as the wired executable oracle `scanDatabaseFast`
(`DbScanIndex.lean`), by `scanDatabaseFast_eq`. -/
theorem scanDatabaseWatch_fst_eq_fast (original : List Clause) (f : BranchFrame)
    (w : ClauseWatch) (db : List Clause) (h : WatchOK f db w) :
    (scanDatabaseWatch original f w db).1 = scanDatabaseFast original f db := by
  rw [scanDatabaseWatch_fst_eq original f w db h, scanDatabaseFast_eq]

/-- The fast pass keeps the current-frame invariant. -/
theorem scanDatabaseWatch_WatchOK (original : List Clause) (f : BranchFrame)
    (w : ClauseWatch) (db : List Clause) (h : WatchOK f db w) :
    WatchOK f db (scanDatabaseWatch original f w db).2 := by
  obtain ⟨hfresh, hbasis, hlen, hentries⟩ := h
  have hguard : (w.fresh && (w.entries.length == db.length)) = true :=
    scanDatabaseWatch_guard.mpr ⟨hfresh, hlen⟩
  rw [scanDatabaseWatch, if_pos hguard]
  exact ⟨hfresh, hbasis, hlen, hentries⟩

/-- The fast pass keeps the general fast-pass invariant. -/
theorem scanDatabaseWatch_WatchTableOK (original : List Clause) (f : BranchFrame)
    (basis : List Domain) (w : ClauseWatch) (db : List Clause)
    (h : WatchTableOK basis f db w) :
    WatchTableOK basis f db (scanDatabaseWatch original f w db).2 :=
  (scanDatabaseWatch_spec_of_table original f basis w db h).2

/-- Guard false: the scan IS the establish pass. -/
theorem scanDatabaseWatch_eq_establish (original : List Clause) (f : BranchFrame)
    (w : ClauseWatch) (db : List Clause)
    (h : (w.fresh && (w.entries.length == db.length)) = false) :
    scanDatabaseWatch original f w db = establish original f db := by
  simp only [scanDatabaseWatch, h, Bool.false_eq_true, ↓reduceIte]

/-! ## `reset` safety and the descent-preservation lemma -/

/-- A reset index always yields the reference event (the guard forces the
establish pass). -/
theorem scanDatabaseWatch_reset_fst (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    (scanDatabaseWatch original f ClauseWatch.reset db).1 = scanDatabase original f db := by
  rw [scanDatabaseWatch_eq_establish _ _ _ _
    (by simp [ClauseWatch.reset, Bool.false_and])]
  exact establish_fst_eq original f db

/-- A reset index yields a current-frame-consistent index after one scan. -/
theorem scanDatabaseWatch_reset_WatchOK (original : List Clause) (f : BranchFrame)
    (db : List Clause) :
    WatchOK f db (scanDatabaseWatch original f ClauseWatch.reset db).2 := by
  rw [scanDatabaseWatch_eq_establish _ _ _ _
    (by simp [ClauseWatch.reset, Bool.false_and])]
  exact establish_WatchOK original f db

/-- **DESCENT PRESERVATION (the paper argument)**: an index established at `f`
stays a fast-pass index at every LIVE frame `g` that `f` descends to. The
watch-slot condition is not part of the invariant — it is consumed by the
skip rule (`two_le_clauseRemaining_of_watchesClear`): entries are valid at the
old basis, and the changed-slot map decides per clause whether the two
watches still certify two remaining literals. `hdesc` is definitionally
`FrameDescendsFrom g f` (BackjumpFrontier), inlined to keep this module's DAG
narrow. -/
theorem WatchOK.descend {f g : BranchFrame} {db : List Clause} {w : ClauseWatch}
    (h : WatchOK f db w)
    (hdesc : ∀ a, FrameCovers g a → FrameCovers f a)
    (hlive : frameLiveB g = true) :
    WatchTableOK (Frame.domains f) g db w :=
  ⟨h.1, h.2.1, domains_descend_of_frameDescends hdesc hlive, h.2.2.1, h.2.2.2⟩

/-! ## Scheduler adapter: the value-carried index and its guarded scan

PLAN task W1 adapter, RETAINED UNWIRED (measured negative result, see the
module header). When the dispatcher does thread a `WatchIndex` through its
`PropScheduler` (the intended future version-keyed scheduler, E1 boundary),
the index travels as a value: the `ClauseWatch`, the database its entries
were recorded for, and a FRAME-FREE validity proof (`WatchEntriesOK` at the
recorded basis). Proof fields of a structure are erased at runtime, so the
compiled dispatcher would carry only `basis`, `entries`, `fresh` and the
database list.

`scanDatabaseWatchIdx` is the guarded entry. It checks, computably, that the
recorded database IS the scanned one (`DecidableEq` on clauses — no value
comparison escapes the sound Boolean `Value.eqB` used by the slot tests) and
that the current frame still descends from the recorded basis
(`domainsDescendB`, soundness `domainsDescendB_sound`). Both hold between
restores, so the fast pass runs; either failure (a restoration ascends the
frame, a learned clause grows the database) falls back to the establish pass,
which re-records at the current frame — no transition kind is plumbed. The
event is UNCONDITIONALLY the certified `scanDatabase` event: the same event as
`scanDatabaseFast`, not a simulation. The unconditional equality is what makes
the adapter safe to wire or unwire freely; it is unwired because the measured
integrated cost exceeded the oracle's (see the module header). -/

/-- Boolean membership test of a domain in another (`Value` has no
`DecidableEq`; the sound `Value.eqB` decides each value). -/
def valuesSubsetB (xs ys : List Value) : Bool :=
  xs.all fun x => ys.any fun y => x.eqB y

theorem valuesSubsetB_sound {xs ys : List Value} (h : valuesSubsetB xs ys = true) :
    ∀ v ∈ xs, v ∈ ys := by
  intro v hv
  have h1 := List.all_eq_true.mp h v hv
  obtain ⟨y, hy, hyb⟩ := List.any_eq_true.mp h1
  rw [LeanFzn.Semantics.Evaluation.value_eqB_iff.mp hyb]
  exact hy

/-! ## Structural domain inclusion `Dom.subsetB` (D0 obligation 8)

`Dom.subsetB` is the representation-level companion of the enumerating
`valuesSubsetB`: the compact shapes answer inclusion from the representation
itself (a 64-bit bit-inclusion test under an offset guard, and interval bounds
plus hole membership) and only shapes the representation does not cover fall
back to the frozen interface `(Dom.enum d).all (Dom.memBool b)`.  Every fast
test is ONE-SIDED — `true` certifies that the enumeration of `d` is contained
in the enumeration of `b` (`subsetBFast_sound`), which is all soundness needs.
Because `subsetB` falls back to the enumeration test whenever the fast test
fails, it is nevertheless EXACT (`Dom.subsetB_eq_valuesSubsetB`), so the watch
chain's per-slot check keeps the old semantics value for value while the
common descending case never allocates an enumeration. -/

namespace Dom

/-- Bit inclusion up to bit `k`: every set bit of `a` below `k` is set in
`b`.  A fixed 64-iteration loop over `Nat.testBit` — no list, no allocation,
and the kernel specification is the pointwise bit implication. -/
def bitsSubsetGo (a b : UInt64) : Nat → Bool
  | 0 => true
  | k + 1 => (!a.toNat.testBit k || b.toNat.testBit k) && bitsSubsetGo a b k

/-- Bit inclusion of two 64-bit patterns (the window of `Rep.small`). -/
def bitsSubsetB (a b : UInt64) : Bool := bitsSubsetGo a b 64

theorem bitsSubsetGo_spec (a b : UInt64) (k : Nat) :
    bitsSubsetGo a b k = true ↔
      ∀ j < k, a.toNat.testBit j = true → b.toNat.testBit j = true := by
  induction k with
  | zero => simp [bitsSubsetGo]
  | succ k ih =>
      rw [bitsSubsetGo, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hhead, htail⟩ j hj ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hjk
        · exact htail j hj' ha
        · rw [hjk] at ha ⊢
          by_cases hb : b.toNat.testBit k = true
          · exact hb
          · have hb' : b.toNat.testBit k = false := by simpa using hb
            rw [hb'] at hhead
            simp only [Bool.or_false] at hhead
            have ha' : a.toNat.testBit k = false := by simpa using hhead
            rw [ha'] at ha
            exact absurd ha (by simp)
      · intro h
        constructor
        · by_cases ha : a.toNat.testBit k = true
          · have hb := h k (Nat.lt_succ_self k) ha
            simp [hb]
          · have ha' : a.toNat.testBit k = false := by simpa using ha
            simp [ha']
        · intro j hj ha
          exact h j (Nat.lt_trans hj (Nat.lt_succ_self k)) ha

theorem bitsSubsetB_spec (a b : UInt64) :
    bitsSubsetB a b = true ↔
      ∀ j < 64, a.toNat.testBit j = true → b.toNat.testBit j = true :=
  bitsSubsetGo_spec a b 64

/-- Bit inclusion of the Boolean bitsets certifies inclusion of the Boolean
enumerations (`smallBools` only reads bits 0 and 1, so requiring all 64 bits
is conservative — which is all the fast test claims). -/
theorem mem_smallBools_of_bitsSubsetB {bd bb : UInt64}
    (h : bitsSubsetB bd bb = true) :
    ∀ v, v ∈ smallBools bd → v ∈ smallBools bb := by
  intro v hv
  obtain ⟨c, rfl, hbit⟩ := mem_smallBools.mp hv
  rw [mem_smallBools_bool]
  have hc : (if c then 1 else 0) < 64 := by cases c <;> simp
  exact (bitsSubsetB_spec bd bb).mp h _ hc hbit

/-- Bit inclusion of equal-offset integer bitsets certifies inclusion of the
integer enumerations. -/
theorem mem_smallInts_of_bitsSubsetB {off : Int} {bd bb : UInt64}
    (h : bitsSubsetB bd bb = true) :
    ∀ v, v ∈ (smallInts off bd).map Value.int →
      v ∈ (smallInts off bb).map Value.int := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  rw [List.mem_map]
  refine ⟨i, ?_, rfl⟩
  rw [mem_smallInts] at hi ⊢
  obtain ⟨k, hk, hbit, rfl⟩ := hi
  exact ⟨k, hk, (bitsSubsetB_spec bd bb).mp h k hk hbit, rfl⟩

/-- Structural inclusion of two interval-with-holes shapes: the interval must
be contained, and every hole of `b` must be a hole of `d` or lie outside
`d`'s interval. -/
def holesSubsetB (lo hi : Int) (hs : List Int) (lo' hi' : Int) (hs' : List Int) : Bool :=
  decide (lo' ≤ lo) && decide (hi ≤ hi') &&
    hs'.all (fun h => memHoles hs h || decide (h < lo) || decide (hi < h))

theorem holesSubsetB_sound {lo hi : Int} {hs : List Int} {lo' hi' : Int}
    {hs' : List Int} (h : holesSubsetB lo hi hs lo' hi' hs' = true) :
    ∀ v, v ∈ enum ⟨.holes lo hi hs⟩ → v ∈ enum ⟨.holes lo' hi' hs'⟩ := by
  unfold holesSubsetB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hlo, hhi⟩, hholes⟩ := h
  have hlo' : lo' ≤ lo := of_decide_eq_true hlo
  have hhi' : hi ≤ hi' := of_decide_eq_true hhi
  intro v hv
  obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
  rw [mem_holes_enum_int] at hv ⊢
  obtain ⟨h1, h2, h3⟩ := hv
  refine And.intro (Int.le_trans hlo' h1) (And.intro (Int.le_trans h2 hhi') ?_)
  intro hmem
  have hall := List.all_eq_true.mp hholes i hmem
  rw [Bool.or_eq_true, Bool.or_eq_true] at hall
  rcases hall with (hm | hlt) | hgt
  · exact h3 (memHoles_iff.mp hm)
  · have hlt' : i < lo := of_decide_eq_true hlt
    omega
  · have hgt' : hi < i := of_decide_eq_true hgt
    omega

/-- The structural fast test of `Dom.subsetB`.  ONE-SIDED: `true` certifies
inclusion of the enumerations (`subsetBFast_sound`); any shape it does not
cover returns `false` and is handed to the enumeration fallback. -/
def subsetBFast : Dom → Dom → Bool
  | ⟨.small true _ bd⟩, ⟨.small true _ bb⟩ => bitsSubsetB bd bb
  | ⟨.small false od wd⟩, ⟨.small false ob wb⟩ =>
      decide (od = ob) && bitsSubsetB wd wb
  | ⟨.holes lo hi hs⟩, ⟨.holes lo' hi' hs'⟩ => holesSubsetB lo hi hs lo' hi' hs'
  | _, _ => false

theorem subsetBFast_sound {d b : Dom} (h : subsetBFast d b = true) :
    ∀ v, v ∈ enum d → v ∈ enum b := by
  obtain ⟨rd⟩ := d
  obtain ⟨rb⟩ := b
  cases rd with
  | small isB od wd =>
      cases rb with
      | small isB' ob wb =>
          cases isB with
          | true =>
              cases isB' with
              | true =>
                  simp only [subsetBFast] at h
                  exact mem_smallBools_of_bitsSubsetB h
              | false => simp [subsetBFast] at h
          | false =>
              cases isB' with
              | true => simp [subsetBFast] at h
              | false =>
                  simp only [subsetBFast, Bool.and_eq_true] at h
                  obtain ⟨hEq, hbits⟩ := h
                  have hoff : od = ob := of_decide_eq_true hEq
                  subst hoff
                  exact mem_smallInts_of_bitsSubsetB hbits
      | holes lo hi hs => simp [subsetBFast] at h
      | general vs => simp [subsetBFast] at h
  | holes lo hi hs =>
      cases rb with
      | small isB ob wb => simp [subsetBFast] at h
      | holes lo' hi' hs' =>
          simp only [subsetBFast] at h
          exact holesSubsetB_sound h
      | general vs => simp [subsetBFast] at h
  | general vs =>
      cases rb with
      | small isB ob wb => simp [subsetBFast] at h
      | holes lo hi hs => simp [subsetBFast] at h
      | general vs' => simp [subsetBFast] at h

/-- **STRUCTURAL DOMAIN INCLUSION (D0 obligation 8)**: a representation-level
test with the enumeration fallback `(Dom.enum d).all (Dom.memBool b)`.  The
fallback runs only when the structural fast test fails, so a descending slot
never materializes an enumeration. -/
def subsetB (d b : Dom) : Bool :=
  match subsetBFast d b with
  | true => true
  | false => (enum d).all fun v => memBool b v

/-- **EXACTNESS**: whenever the fast test fails, `subsetB` is the frozen
interface `(enum d).all (memBool b)`; when it succeeds, the fast test already
certifies that the fallback would return `true`. -/
theorem subsetB_eq_enum_all (d b : Dom) :
    subsetB d b = (enum d).all (fun v => memBool b v) := by
  unfold subsetB
  cases h : subsetBFast d b with
  | false => rfl
  | true =>
      have hall : (enum d).all (fun v => memBool b v) = true := by
        rw [List.all_eq_true]
        intro v hv
        exact (memBool_iff b v).mpr (subsetBFast_sound h v hv)
      rw [hall]

/-- The `all`/`memBool` form is the list-inclusion test: `memBool_iff` plus
`Value.eqB`'s exactness (`value_eqB_iff`, `value_eqB_refl`). -/
theorem all_memBool_eq_valuesSubsetB (d b : Dom) :
    (enum d).all (fun v => memBool b v) =
      valuesSubsetB (enum d) (enum b) := by
  rw [valuesSubsetB]
  congr 1
  funext v
  cases hm : memBool b v with
  | false =>
      have hnot : ¬ (enum b).any (fun y => v.eqB y) = true := by
        intro ha
        obtain ⟨y, hy, hyb⟩ := List.any_eq_true.mp ha
        have hvy : v = y := LeanFzn.Semantics.Evaluation.value_eqB_iff.mp hyb
        exact absurd ((memBool_iff b v).mpr (hvy ▸ hy)) (by rw [hm]; simp)
      cases ha : (enum b).any (fun y => v.eqB y) with
      | false => rfl
      | true => exact absurd ha hnot
  | true =>
      have hv : v ∈ enum b := (memBool_iff b v).mp hm
      have ha : (enum b).any (fun y => v.eqB y) = true :=
        List.any_eq_true.mpr
          ⟨v, hv, LeanFzn.Semantics.Evaluation.value_eqB_refl v⟩
      exact ha.symm

/-- **EXACT CHARACTERIZATION**: `Dom.subsetB` decides exactly the enumeration
inclusion that `valuesSubsetB` decides (no canonicality premise). -/
theorem subsetB_eq_valuesSubsetB (d b : Dom) :
    subsetB d b = valuesSubsetB (enum d) (enum b) := by
  rw [subsetB_eq_enum_all, all_memBool_eq_valuesSubsetB]

/-- **SOUNDNESS of `Dom.subsetB` (D0 obligation 8)**: a passing structural
inclusion certifies domain inclusion. -/
theorem subsetB_sound {d b : Dom} (h : subsetB d b = true) :
    ∀ v ∈ d, v ∈ b := by
  intro v hv
  have hsub : valuesSubsetB (enum d) (enum b) = true := by
    rw [← subsetB_eq_valuesSubsetB]
    exact h
  exact mem_of_mem_enum (valuesSubsetB_sound hsub v (mem_enum_of_mem hv))

end Dom

/-- Per-slot inclusion with a structural fast path: equal slots are decided by
`Dom.eqB` (sound by `Dom.eqB_sound`, no enumeration) and unequal slots by the
structural `Dom.subsetB`.  `valueDomainSubsetB_eq` proves that this is the
previous definition value for value. -/
def valueDomainSubsetB (d b : Domain) : Bool :=
  match Dom.eqB d b with
  | true => true
  | false => Dom.subsetB d b

/-- **REFINEMENT**: the structural definition equals the previous
enumeration-based one, on every pair of domains (no canonicality premise). -/
theorem valueDomainSubsetB_eq (d b : Domain) :
    valueDomainSubsetB d b =
      (match valuesEqB (Dom.enum d) (Dom.enum b) with
       | true => true
       | false => valuesSubsetB (Dom.enum d) (Dom.enum b)) := by
  cases hb : Dom.eqB d b with
  | true =>
      have hdb : d = b := Dom.eqB_sound hb
      subst hdb
      rw [valueDomainSubsetB, hb]
      have hrefl : valuesEqB (Dom.enum d) (Dom.enum d) = true := valuesEqB_self _
      rw [hrefl]
  | false =>
      rw [valueDomainSubsetB, hb, Dom.subsetB_eq_valuesSubsetB]
      cases hE : valuesEqB (Dom.enum d) (Dom.enum b) with
      | false => rfl
      | true =>
          have hlist : Dom.enum d = Dom.enum b := valuesEqB_sound hE
          rw [hlist]
          rw [valuesSubsetB, List.all_eq_true]
          intro v hv
          exact List.any_eq_true.mpr
            ⟨v, hv, LeanFzn.Semantics.Evaluation.value_eqB_refl v⟩

theorem valueDomainSubsetB_sound {d b : Domain} (h : valueDomainSubsetB d b = true) :
    ∀ v ∈ d, v ∈ b := by
  cases hb : Dom.eqB d b with
  | true =>
      have hdb : d = b := Dom.eqB_sound hb
      subst hdb
      exact fun v hv => hv
  | false =>
      have h1 := h
      rw [valueDomainSubsetB, hb] at h1
      exact Dom.subsetB_sound h1

/-- Computable pointwise domain descent, FIRST-ORDER recursion: the second
list's slot domains are included in the first (the basis); slots beyond the
basis must be empty, slots beyond the current list carry no claim. This is the
computable companion of `DomainsDescend`. -/
def domainsDescendB : List Domain → List Domain → Bool
  | [], [] => true
  | [], d :: ds => d.isEmpty && domainsDescendB [] ds
  | _ :: _, [] => true
  | b :: bs, d :: ds => valueDomainSubsetB d b && domainsDescendB bs ds

/-- **SOUNDNESS of `domainsDescendB`**: a passing check certifies
`DomainsDescend` for the corresponding `Frame.domains`. -/
theorem domainsDescendB_sound :
    ∀ (basis doms : List Domain), domainsDescendB basis doms = true →
      ∀ (s : Nat) (v : Value),
        v ∈ doms.getD s Dom.empty → v ∈ basis.getD s Dom.empty := by
  intro basis doms
  revert basis
  induction doms with
  | nil =>
      intro basis h s v hv
      simp at hv
  | cons d ds ih =>
      intro basis h s v hv
      cases basis with
      | nil =>
          cases s with
          | zero =>
              have hd : d.isEmpty = true := (Bool.and_eq_true_iff.mp h).1
              have hnil : Dom.enum d = [] := (Dom.isEmpty_eq_true_iff d).mp hd
              have hmem : v ∈ Dom.empty := by
                have hthis : v ∈ Dom.enum d := by
                  simpa only [List.getD_cons_zero] using mem_enum_of_mem hv
                rw [hnil] at hthis
                simpa using hthis
              exact hmem
          | succ s =>
              exact ih [] (Bool.and_eq_true_iff.mp h).2 s v hv
      | cons b bs =>
          cases s with
          | zero =>
              exact valueDomainSubsetB_sound (Bool.and_eq_true_iff.mp h).1 v hv
          | succ s =>
              exact ih bs (Bool.and_eq_true_iff.mp h).2 s v hv

/-! ## Corrected standard two-watched-literal scheme

The entry predicate above (`EntryOKD`) claims that every NON-watched literal
is impossible at the basis, so `clauseEntry` records only clauses with at most
two remaining literals; loose clauses have no skippable entry and the "fast"
pass re-classifies them at reference cost. The CORRECTED scheme claims only
what the skip rule needs: `some (s₁, s₂)` witnesses two DISTINCT positions
whose literals are possible at the recording basis and names their slots.
Loose clauses are skippable too; the skip test reads only the two slots, and a
clause whose watch slots changed is reclassified by a first-order search that
stops at the second possible literal. -/

/-- The first possible position at or after the walk's start index. -/
def remIdxFirst (doms : List Domain) : List Literal → Nat → Option Nat
  | [], _ => none
  | l :: ls, idx =>
      match literalImpossibleD doms l with
      | true => remIdxFirst doms ls (idx + 1)
      | false => some idx

/-- The first TWO possible positions `i < j` in walk order; `none` when fewer
than two literals of the clause are possible. First-order, no allocation,
stops at the second possible literal. -/
def remIdxFirstTwo (doms : List Domain) : List Literal → Nat → Option (Nat × Nat)
  | [], _ => none
  | l :: ls, idx =>
      match literalImpossibleD doms l with
      | true => remIdxFirstTwo doms ls (idx + 1)
      | false =>
          match remIdxFirst doms ls (idx + 1) with
          | none => none
          | some j => some (idx, j)

/-- `remIdxFirst` is the head of the full remaining-position walk. -/
theorem remIdxFirst_eq (doms : List Domain) (c : Clause) (idx : Nat) :
    remIdxFirst doms c idx = (remIdx doms c idx).head? := by
  induction c generalizing idx with
  | nil => rfl
  | cons l ls ih =>
      simp only [remIdxFirst, remIdx]
      by_cases h : literalImpossibleD doms l = true
      · simp only [h]
        exact ih (idx + 1)
      · have hf : literalImpossibleD doms l = false := Bool.eq_false_iff.mpr h
        simp only [hf]
        rfl

/-- `remIdxFirstTwo` is the first two elements of the full remaining-position
walk. -/
theorem remIdxFirstTwo_eq (doms : List Domain) (c : Clause) (idx : Nat) :
    remIdxFirstTwo doms c idx =
      (match remIdx doms c idx with
       | i :: j :: _ => some (i, j)
       | _ => none) := by
  induction c generalizing idx with
  | nil => rfl
  | cons l ls ih =>
      simp only [remIdxFirstTwo, remIdx]
      by_cases h : literalImpossibleD doms l = true
      · simp only [h]
        exact ih (idx + 1)
      · have hf : literalImpossibleD doms l = false := Bool.eq_false_iff.mpr h
        simp only [hf]
        rw [remIdxFirst_eq doms ls (idx + 1)]
        cases hr : remIdx doms ls (idx + 1) with
        | nil => rfl
        | cons j js => rfl

/-- A first-two hit exposes two distinct possible positions. -/
theorem remIdxFirstTwo_spec {doms : List Domain} {c : Clause} {i j : Nat}
    (h : remIdxFirstTwo doms c 0 = some (i, j)) :
    ∃ (hij : i < j) (hj : j < c.length),
      literalImpossibleD doms (c[i]'(Nat.lt_trans hij hj)) = false ∧
      literalImpossibleD doms (c[j]'hj) = false := by
  rw [remIdxFirstTwo_eq] at h
  cases hr : remIdx doms c 0 with
  | nil => rw [hr] at h; exact absurd h (by simp)
  | cons a t =>
      cases t with
      | nil => rw [hr] at h; exact absurd h (by simp)
      | cons b u =>
          rw [hr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hmemA : a ∈ remIdx doms c 0 := by rw [hr]; exact List.mem_cons_self ..
          have hmemB : b ∈ remIdx doms c 0 := by rw [hr]; simp
          have hpair := remIdx_pairwise doms c 0
          rw [hr] at hpair
          have hab : a < b := (List.pairwise_cons.mp hpair).1 b (by simp)
          obtain ⟨ta, hta, _⟩ := (mem_remIdx 0 a).mp hmemA
          obtain ⟨tb, htb, _⟩ := (mem_remIdx 0 b).mp hmemB
          have halen : a < c.length := by omega
          have hblen : b < c.length := by omega
          exact ⟨hab, hblen,
            literalImpossibleD_of_mem_remIdx halen hmemA,
            literalImpossibleD_of_mem_remIdx hblen hmemB⟩

/-- No first hit: every literal is impossible. -/
theorem all_impossible_of_first_none {doms : List Domain} {c : Clause}
    (h1 : remIdxFirst doms c 0 = none) :
    ∀ k (hk : k < c.length), literalImpossibleD doms (c[k]'hk) = true := by
  intro k hk
  cases hr : remIdx doms c 0 with
  | cons a t =>
      have hhead := remIdxFirst_eq doms c 0
      rw [hr] at hhead
      dsimp only [List.head?] at hhead
      exact absurd (h1.symm.trans hhead) (by simp)
  | nil =>
      cases hb : literalImpossibleD doms (c[k]'hk) with
      | true => rfl
      | false =>
          have hmem : k ∈ remIdx doms c 0 := (mem_remIdx 0 k).mpr ⟨k, hk, by omega, hb⟩
          rw [hr] at hmem
          simp at hmem

/-- No first-two hit but a first hit: exactly one possible position remains. -/
theorem exists_unique_of_firstTwo_none {doms : List Domain} {c : Clause} {k : Nat}
    (h2 : remIdxFirstTwo doms c 0 = none) (h1 : remIdxFirst doms c 0 = some k) :
    ∃ (hk : k < c.length),
      literalImpossibleD doms (c[k]'hk) = false ∧
      ∀ t (ht : t < c.length), t ≠ k → literalImpossibleD doms (c[t]'ht) = true := by
  cases hr : remIdx doms c 0 with
  | nil =>
      have hhead := remIdxFirst_eq doms c 0
      rw [hr] at hhead
      dsimp only [List.head?] at hhead
      exact absurd (h1.symm.trans hhead) (by simp)
  | cons a t =>
      have hhead := remIdxFirst_eq doms c 0
      rw [hr] at hhead
      dsimp only [List.head?] at hhead
      have hak : a = k := (Option.some.inj (h1.symm.trans hhead)).symm
      have ht_nil : t = [] := by
        cases t with
        | nil => rfl
        | cons b u =>
            rw [remIdxFirstTwo_eq, hr] at h2
            simp at h2
      rw [hak, ht_nil] at hr
      have hk_mem : k ∈ remIdx doms c 0 := by rw [hr]; exact List.mem_cons_self ..
      have hklen : k < c.length := by
        obtain ⟨tk, htk, heq, _⟩ := (mem_remIdx 0 k).mp hk_mem
        omega
      refine ⟨hklen, literalImpossibleD_of_mem_remIdx hklen hk_mem, ?_⟩
      intro t ht hne
      cases hb : literalImpossibleD doms (c[t]'ht) with
      | true => rfl
      | false =>
          have hmem : t ∈ remIdx doms c 0 := (mem_remIdx 0 t).mpr ⟨t, ht, by omega, hb⟩
          rw [hr] at hmem
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          exact absurd hmem hne

/-! ## Self-validating watch entries (event-keyed, no database or basis guard)

The earlier corrected scheme still carried a basis and a changed-slot map, so
after every slot had been narrowed once no watch slot was ever "unchanged"
again and the skip rate collapsed. The final scheme is fully self-contained:
an entry stores the two watched POSITIONS and the LITERALS recorded there, and
the skip test RE-CHECKS at the current frame that the clause still carries
those literals and that both are still possible. The invariant is just
`i < j` per entry — no database identity, no basis, no descent, no guard:

* a database change (learned-clause insertion) needs no invalidation: shifted
  entries fail self-validation and are re-recorded during classification;
  `alignEntries` pads/drops the entry list to the database length as a pure
  runtime heuristic (soundness never depends on alignment);
* a restoration needs no re-basis: stale positions simply re-validate or get
  reclassified (possibility is decided at the current frame, never
  transferred from an old one);
* the wrapper is UNCONDITIONAL (`scanDatabaseWatch2_fst_eq`) and has no guard
  at all; the per-scan work counters (`WatchWork`) stay in the index.

The skip test reads the two clause positions, compares the literals and
decides their impossibility from the frame's slot array
(`literalImpossibleArr`), so the only per-scan setup is `frameDomainArray f`. -/

/-- A watch entry: two distinct positions and the literals recorded there. -/
abbrev WatchEntry := Nat × Nat × Literal × Literal

/-- **THE SELF-VALIDATING ENTRY INVARIANT**: `some (i, j, li, lj)` claims only
distinctness of the two positions; everything else is re-checked against the
clause and the current frame at every use. -/
def WatchLitsOK : Option WatchEntry → Prop
  | none => True
  | some (i, j, _, _) => i < j

/-- The positional per-entry invariant of a `WatchIndex` (arbitrary alignment:
entries beyond the list length carry no claim). -/
def WatchLitsEntriesOK (es : List (Option WatchEntry)) : Prop :=
  ∀ (j : Nat) (e : Option WatchEntry), es[j]? = some e → WatchLitsOK e

theorem WatchLitsEntriesOK.tail {e : Option WatchEntry}
    {es : List (Option WatchEntry)}
    (h : WatchLitsEntriesOK (e :: es)) : WatchLitsEntriesOK es :=
  fun j e' he => h (j + 1) e' (by simpa using he)

theorem WatchLitsEntriesOK.cons_head {e : Option WatchEntry}
    {es : List (Option WatchEntry)}
    (h0 : WatchLitsOK e) (htail : WatchLitsEntriesOK es) :
    WatchLitsEntriesOK (e :: es) := by
  intro j e' he
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      exact h0
  | succ k => exact htail k e' (by simpa using he)

/-- Prepending `none` padding preserves the invariant. -/
theorem WatchLitsEntriesOK.pad_left (k : Nat)
    {es : List (Option WatchEntry)} (h : WatchLitsEntriesOK es) :
    WatchLitsEntriesOK (List.replicate k none ++ es) := by
  intro j e he
  rw [List.getElem?_append, List.length_replicate] at he
  by_cases hjk : j < k
  · rw [if_pos hjk] at he
    rw [List.getElem?_replicate_of_lt hjk] at he
    simp only [Option.some.injEq] at he
    subst he
    trivial
  · rw [if_neg hjk] at he
    exact h (j - k) e he

/-- Dropping a prefix preserves the invariant. -/
theorem WatchLitsEntriesOK.drop {es : List (Option WatchEntry)}
    (k : Nat) (h : WatchLitsEntriesOK es) :
    WatchLitsEntriesOK (es.drop k) := by
  intro j e he
  rw [List.getElem?_drop, Nat.add_comm] at he
  exact h (j + k) e he

/-- **ALIGNMENT HEURISTIC**: pad/drop the entry list to the database length so
the positional walk stays aligned across a growing database. Pure runtime
heuristic: soundness never depends on it (entries self-validate). -/
def alignEntries (db : List Clause) (es : List (Option WatchEntry)) :
    List (Option WatchEntry) :=
  if es.length ≤ db.length then
    List.replicate (db.length - es.length) none ++ es
  else
    es.drop (es.length - db.length)

theorem alignEntries_ok (db : List Clause)
    {es : List (Option WatchEntry)} (h : WatchLitsEntriesOK es) :
    WatchLitsEntriesOK (alignEntries db es) := by
  unfold alignEntries
  split
  · exact h.pad_left _
  · exact h.drop _

/-- The self-validating skip test: the clause still carries the recorded
literals at the recorded positions and both literals are possible at the
current frame (decided in O(1) from the precomputed slot summaries). -/
def litsClearB (arr : Array Domain) (sums : Array SlotSum) (c : Clause) (i j : Nat)
    (li lj : Literal) : Bool :=
  (match c[i]? with | some l => l == li | none => false) &&
  (match c[j]? with | some l => l == lj | none => false) &&
  (!(literalImpossibleFast arr sums li) && !(literalImpossibleFast arr sums lj))

theorem litsClearB_spec {arr : Array Domain} {sums : Array SlotSum} {c : Clause}
    {i j : Nat} {li lj : Literal} (h : litsClearB arr sums c i j li lj = true) :
    c[i]? = some li ∧ c[j]? = some lj ∧
    literalImpossibleFast arr sums li = false ∧
    literalImpossibleFast arr sums lj = false := by
  rw [litsClearB, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [Bool.and_eq_true] at h₁
  rw [Bool.and_eq_true] at h₂
  obtain ⟨h₁a, h₁b⟩ := h₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hc : c[i]? with
    | none => rw [hc] at h₁a; exact absurd h₁a (by simp)
    | some l =>
        rw [hc] at h₁a
        rw [beq_iff_eq] at h₁a
        rw [h₁a]
  · cases hc : c[j]? with
    | none => rw [hc] at h₁b; exact absurd h₁b (by simp)
    | some l =>
        rw [hc] at h₁b
        rw [beq_iff_eq] at h₁b
        rw [h₁b]
  · simpa using h₂.1
  · simpa using h₂.2

/-- **THE SELF-VALIDATING SKIP LEMMA**: a re-validated entry with both watch
literals still possible certifies at least two remaining literals. No
database identity, no basis, no descent. -/
theorem two_le_clauseRemaining_of_litsClear {f : BranchFrame} {c : Clause}
    {i j : Nat} {li lj : Literal}
    (hok : WatchLitsOK (some (i, j, li, lj)))
    (hci : c[i]? = some li) (hcj : c[j]? = some lj)
    (hp₁ : literalImpossibleFast (frameDomainArray f) (sumsOfArray (frameDomainArray f)) li = false)
    (hp₂ : literalImpossibleFast (frameDomainArray f) (sumsOfArray (frameDomainArray f)) lj = false) :
    2 ≤ (clauseRemaining f c).length := by
  have hij : i < j := hok
  obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp hci
  obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hcj
  have hp₁' : literalImpossible f (c[i]'hi) = false := by
    rw [show (c[i]'hi) = li from hgeti]
    rw [← literalImpossibleArr_eq f li, ← literalImpossibleFast_eq (frameDomainArray f) li]
    exact hp₁
  have hp₂' : literalImpossible f (c[j]'hj) = false := by
    rw [show (c[j]'hj) = lj from hgetj]
    rw [← literalImpossibleArr_eq f lj, ← literalImpossibleFast_eq (frameDomainArray f) lj]
    exact hp₂
  have := two_le_length_filter (l := c) (p := fun l => !literalImpossible f l)
    hi hj (Nat.ne_of_lt hij) (by simp [hp₁']) (by simp [hp₂'])
  simpa [clauseRemaining] using this

/-- Corrected per-clause classification AND the entry to record: the
compressed remaining set (exactly `reduceRemaining (clauseRemaining f c)` at
`doms = Frame.domains f`) and, when two literals are possible, the two watched
positions with their literals. -/
def clauseClassifyL (doms : List Domain) (c : Clause) :
    Option (Option Literal) × Option WatchEntry :=
  match remIdxFirstTwo doms c 0 with
  | some (i, j) =>
      match c[i]?, c[j]? with
      | some li, some lj => (some none, some (i, j, li, lj))
      | _, _ => (none, none)
  | none =>
      match remIdxFirst doms c 0 with
      | some k => (c[k]?.map some, none)
      | none => (none, none)

theorem clauseClassifyL_fst (f : BranchFrame) (c : Clause) :
    (clauseClassifyL (Frame.domains f) c).1 = reduceRemaining (clauseRemaining f c) := by
  unfold clauseClassifyL
  cases h2 : remIdxFirstTwo (Frame.domains f) c 0 with
  | none =>
      dsimp only
      cases h1 : remIdxFirst (Frame.domains f) c 0 with
      | none =>
          dsimp only
          have hall := all_impossible_of_first_none h1
          rw [clauseRemaining_eq_nil_of_entry f c fun k hk => hall k hk]
          rfl
      | some k =>
          dsimp only
          obtain ⟨hk, hp, hother⟩ := exists_unique_of_firstTwo_none h2 h1
          rw [clauseRemaining_eq_singleton_of_entry f c k hk hp hother]
          rw [List.getElem?_eq_getElem hk]
          rfl
  | some ij =>
      obtain ⟨i, j⟩ := ij
      dsimp only
      obtain ⟨hij, hj, hp1, hp2⟩ := remIdxFirstTwo_spec h2
      have hi : i < c.length := Nat.lt_trans hij hj
      have hci : c[i]? = some (c[i]'hi) := List.getElem?_eq_getElem hi
      have hcj : c[j]? = some (c[j]'hj) := List.getElem?_eq_getElem hj
      have hp1' : literalImpossible f (c[i]'hi) = false := hp1
      have hp2' : literalImpossible f (c[j]'hj) = false := hp2
      have hlen : 2 ≤ (clauseRemaining f c).length := by
        have := two_le_length_filter (l := c) (p := fun l => !literalImpossible f l)
          hi hj (Nat.ne_of_lt hij) (by simp [hp1']) (by simp [hp2'])
        simpa [clauseRemaining] using this
      cases hli : c[i]? with
      | none => rw [hli] at hci; exact absurd hci (by simp)
      | some li =>
          cases hlj : c[j]? with
          | none => rw [hlj] at hcj; exact absurd hcj (by simp)
          | some lj =>
              dsimp only
              cases hcl : clauseRemaining f c with
              | nil => rw [hcl] at hlen; simp at hlen
              | cons x xs =>
                  cases xs with
                  | nil => rw [hcl] at hlen; simp at hlen
                  | cons y ys => rfl

theorem clauseClassifyL_snd_ok (f : BranchFrame) (c : Clause) :
    WatchLitsOK (clauseClassifyL (Frame.domains f) c).2 := by
  unfold clauseClassifyL
  cases h2 : remIdxFirstTwo (Frame.domains f) c 0 with
  | none =>
      dsimp only
      cases h1 : remIdxFirst (Frame.domains f) c 0 <;> dsimp only <;> trivial
  | some ij =>
      obtain ⟨i, j⟩ := ij
      dsimp only
      obtain ⟨hij, hj, _, _⟩ := remIdxFirstTwo_spec h2
      have hi : i < c.length := Nat.lt_trans hij hj
      have hci : c[i]? = some (c[i]'hi) := List.getElem?_eq_getElem hi
      have hcj : c[j]? = some (c[j]'hj) := List.getElem?_eq_getElem hj
      cases hli : c[i]? with
      | none => rw [hli] at hci; exact absurd hci (by simp)
      | some li =>
          cases hlj : c[j]? with
          | none => rw [hlj] at hcj; exact absurd hcj (by simp)
          | some lj => dsimp only; exact hij

/-- Per-scan work counters (measurement data; no proof role). -/
structure WatchWork where
  /-- Clauses skipped through re-validated unchanged watch slots. -/
  skips : Nat := 0
  /-- Entry-carrying clauses reclassified after a failed re-validation. -/
  rechecks : Nat := 0
  /-- Entry-less clauses, classified. -/
  classifies : Nat := 0
  /-- Reserved (no re-basis pass exists in this scheme). -/
  establishes : Nat := 0

/-- The per-clause step result of the corrected scan. -/
inductive WatchStepResult where
  | stop (ev : PruningEvent) (cl : Option (Option Literal)) (e : Option WatchEntry)
  | skip
  | go (cl : Option (Option Literal)) (e : Option WatchEntry)

/-- Reclassification of one clause through the first-two search (no skip
test): the shared body of `watchStep`. -/
def watchClassifyStep (original : List Clause) (doms : List Domain) (f : BranchFrame)
    (c : Clause) : WatchStepResult :=
  match clauseClassifyL doms c with
  | (cl, e') =>
      match cl with
      | none => .stop (.conflict [c]) none e'
      | some none => .go (some none) e'
      | some (some l) =>
          if productive l f then
            .stop (.implied l c false (!(original.contains c))) (some (some l)) e'
          else .go (some (some l)) e'

/-- One clause of the self-validating fast pass: skip when the clause still
carries the recorded literals and both are still possible; otherwise
reclassify through the first-two search and record the fresh pair. -/
def watchStep (original : List Clause) (doms : List Domain) (f : BranchFrame)
    (arr : Array Domain) (sums : Array SlotSum) (c : Clause)
    (e : Option WatchEntry) : WatchStepResult :=
  match e with
  | some (i, j, li, lj) =>
      if litsClearB arr sums c i j li lj then
        .skip
      else watchClassifyStep original doms f c
  | none => watchClassifyStep original doms f c

/-- The reclassification step matches the reference classification: it stops
exactly where `scanDatabase` stops and continues exactly where it continues. -/
theorem watchClassifyStep_spec {original : List Clause} {doms : List Domain}
    {f : BranchFrame} {c : Clause}
    (hclc : (clauseClassifyL doms c).1 = reduceRemaining (clauseRemaining f c))
    (hokc : WatchLitsOK (clauseClassifyL doms c).2) :
    (match watchClassifyStep original doms f c with
     | .skip => 2 ≤ (clauseRemaining f c).length
     | .go cl e' => WatchLitsOK e' ∧ cl = reduceRemaining (clauseRemaining f c) ∧
         (cl = some none ∨ ∃ l, cl = some (some l) ∧ productive l f = false)
     | .stop ev cl e' => WatchLitsOK e' ∧
         cl = reduceRemaining (clauseRemaining f c) ∧
         ((cl = none ∧ ev = .conflict [c]) ∨
          ∃ l, cl = some (some l) ∧ productive l f = true ∧
            ev = .implied l c false (!(original.contains c)))) := by
  unfold watchClassifyStep
  cases hp : clauseClassifyL doms c with
  | mk cl e' =>
      dsimp only
      have hcl : cl = reduceRemaining (clauseRemaining f c) := by
        have h := hclc
        rw [hp] at h
        exact h
      have hok' : WatchLitsOK e' := by
        have h := hokc
        rw [hp] at h
        exact h
      cases cl with
      | none =>
          dsimp only
          exact ⟨hok', hcl, Or.inl ⟨rfl, rfl⟩⟩
      | some cl' =>
          cases cl' with
          | none =>
              dsimp only
              exact ⟨hok', hcl, Or.inl rfl⟩
          | some l =>
              dsimp only
              by_cases hprod : productive l f = true
              · rw [if_pos hprod]
                dsimp only
                exact ⟨hok', hcl, Or.inr ⟨l, rfl, hprod, rfl⟩⟩
              · rw [if_neg hprod]
                dsimp only
                exact ⟨hok', hcl, Or.inr ⟨l, rfl, Bool.eq_false_iff.mpr hprod⟩⟩

/-- **THE ONE-CLAUSE SPEC**: a step either skips (the reference scan skips
too), or continues with a classification equal to the reference
classification and a valid entry, or stops with exactly the reference
event. -/
theorem watchStep_spec {original : List Clause} {doms : List Domain} {f : BranchFrame}
    {c : Clause} {e : Option WatchEntry}
    (hclc : (clauseClassifyL doms c).1 = reduceRemaining (clauseRemaining f c))
    (hokc : WatchLitsOK (clauseClassifyL doms c).2)
    (hok : WatchLitsOK e) :
    (match watchStep original doms f (frameDomainArray f)
        (sumsOfArray (frameDomainArray f)) c e with
     | .skip => 2 ≤ (clauseRemaining f c).length
     | .go cl e' => WatchLitsOK e' ∧ cl = reduceRemaining (clauseRemaining f c) ∧
         (cl = some none ∨ ∃ l, cl = some (some l) ∧ productive l f = false)
     | .stop ev cl e' => WatchLitsOK e' ∧
         cl = reduceRemaining (clauseRemaining f c) ∧
         ((cl = none ∧ ev = .conflict [c]) ∨
          ∃ l, cl = some (some l) ∧ productive l f = true ∧
            ev = .implied l c false (!(original.contains c)))) := by
  unfold watchStep
  cases e with
  | none =>
      dsimp only
      exact watchClassifyStep_spec hclc hokc
  | some p =>
      obtain ⟨i, j, li, lj⟩ := p
      dsimp only
      by_cases hskip : litsClearB (frameDomainArray f) (sumsOfArray (frameDomainArray f))
          c i j li lj = true
      · rw [if_pos hskip]
        dsimp only
        obtain ⟨hci, hcj, hp₁, hp₂⟩ := litsClearB_spec hskip
        exact two_le_clauseRemaining_of_litsClear hok hci hcj hp₁ hp₂
      · rw [if_neg hskip]
        exact watchClassifyStep_spec hclc hokc

/-- **THE SELF-VALIDATING FAST PASS**: walk the database with its watch
entries, skipping clauses whose recorded literals are still present and
possible and reclassifying the rest. -/
def scanWatch2Aux (original : List Clause) (doms : List Domain) (f : BranchFrame)
    (arr : Array Domain) (sums : Array SlotSum) :
    List Clause → List (Option WatchEntry) →
      PruningEvent × List (Option WatchEntry) × WatchWork
  | [], _ => (.stable, [], {})
  | c :: rest, es =>
      match watchStep original doms f arr sums c (es.headD none) with
      | .stop ev _ e' =>
          (ev, e' :: es.tail, if (es.headD none).isSome then { rechecks := 1 } else { classifies := 1 })
      | .skip =>
          let q := scanWatch2Aux original doms f arr sums rest es.tail
          (q.1, es.headD none :: q.2.1, { q.2.2 with skips := q.2.2.skips + 1 })
      | .go _ e' =>
          let q := scanWatch2Aux original doms f arr sums rest es.tail
          (q.1, e' :: q.2.1,
           if (es.headD none).isSome then { q.2.2 with rechecks := q.2.2.rechecks + 1 }
           else { q.2.2 with classifies := q.2.2.classifies + 1 })

/-- **THE FAST-PASS SPEC**: at any entry list satisfying the per-entry
invariant (no alignment or database assumption), the self-validating pass
returns EXACTLY the certified `scanDatabase` event (same order, same early
exit, same payloads) and keeps the invariant. -/
theorem scanWatch2Aux_spec (original : List Clause) (f : BranchFrame) :
    ∀ (db : List Clause) (es : List (Option WatchEntry)),
      WatchLitsEntriesOK es →
      (scanWatch2Aux original (Frame.domains f) f (frameDomainArray f)
        (sumsOfArray (frameDomainArray f)) db es).1 = scanDatabase original f db ∧
      WatchLitsEntriesOK
        (scanWatch2Aux original (Frame.domains f) f (frameDomainArray f)
          (sumsOfArray (frameDomainArray f)) db es).2.1 := by
  intro db
  induction db with
  | nil =>
      intro es _
      rw [scanWatch2Aux]
      refine ⟨rfl, ?_⟩
      intro j e he
      simp at he
  | cons c rest ih =>
      intro es hok
      have hhead : WatchLitsOK (es.headD none) := by
        cases es with
        | nil => exact trivial
        | cons e es' => exact hok 0 e (by simp)
      have htail : WatchLitsEntriesOK es.tail := by
        cases es with
        | nil => exact fun j e he => by simp at he
        | cons e es' => exact WatchLitsEntriesOK.tail hok
      obtain ⟨hev, hent⟩ := ih es.tail htail
      have hws := watchStep_spec (original := original) (doms := Frame.domains f) (f := f)
        (c := c) (e := es.headD none) (clauseClassifyL_fst f c) (clauseClassifyL_snd_ok f c)
        hhead
      rw [scanWatch2Aux]
      cases hs : watchStep original (Frame.domains f) f (frameDomainArray f)
          (sumsOfArray (frameDomainArray f)) c (es.headD none) with
      | stop ev cl e' =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          obtain ⟨hoke', hcl, hstopshape⟩ := hws
          refine ⟨?_, WatchLitsEntriesOK.cons_head hoke' htail⟩
          rw [scanDatabase]
          cases hr : clauseRemaining f c with
          | nil =>
              rw [hr] at hcl
              dsimp only [reduceRemaining] at hcl
              rcases hstopshape with ⟨hcn, hev'⟩ | ⟨l, hsome, _, _⟩
              · rw [hev']
              · exact absurd (hcl.symm.trans hsome) (by simp)
          | cons x xs =>
              cases xs with
              | nil =>
                  rw [hr] at hcl
                  dsimp only [reduceRemaining] at hcl
                  dsimp only
                  rcases hstopshape with ⟨hcn, _⟩ | ⟨l, hsome, hprod, hev'⟩
                  · exact absurd (hcl.symm.trans hcn) (by simp)
                  · have hlx : l = x :=
                      (Option.some.inj (Option.some.inj (hcl.symm.trans hsome))).symm
                    subst hlx
                    rw [hprod, hev']
                    simp only [if_pos trivial]
              | cons y ys =>
                  rw [hr] at hcl
                  dsimp only [reduceRemaining] at hcl
                  rcases hstopshape with ⟨hcn, _⟩ | ⟨l, hsome, _, _⟩
                  · exact absurd (hcl.symm.trans hcn) (by simp)
                  · exact absurd (hcl.symm.trans hsome) (by simp)
      | skip =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          refine ⟨?_, WatchLitsEntriesOK.cons_head hhead hent⟩
          rw [scanDatabase]
          cases hr : clauseRemaining f c with
          | nil => rw [hr] at hws; simp at hws
          | cons x xs =>
              cases xs with
              | nil => rw [hr] at hws; simp at hws
              | cons y ys => exact hev
      | go cl e' =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          obtain ⟨hoke', hcl, hclshape⟩ := hws
          refine ⟨?_, WatchLitsEntriesOK.cons_head hoke' hent⟩
          rw [scanDatabase]
          cases hr : clauseRemaining f c with
          | nil =>
              rw [hr] at hcl
              dsimp only [reduceRemaining] at hcl
              rcases hclshape with h | ⟨l, h, _⟩
              · exact absurd (hcl.symm.trans h) (by simp)
              · exact absurd (hcl.symm.trans h) (by simp)
          | cons x xs =>
              cases xs with
              | nil =>
                  rw [hr] at hcl
                  dsimp only [reduceRemaining] at hcl
                  dsimp only
                  rcases hclshape with h | ⟨l, hl, hprod⟩
                  · exact absurd (hcl.symm.trans h) (by simp)
                  · have hlx : l = x :=
                      (Option.some.inj (Option.some.inj (hcl.symm.trans hl))).symm
                    subst hlx
                    rw [hprod]
                    exact hev
              | cons y ys => exact hev

/-- The value-carried index: the self-validating entries and the last scan's
work counters. No database field, no basis, no guard state. -/
structure WatchIndex where
  /-- The recorded watch entries (positional, arbitrary alignment). -/
  entries : List (Option WatchEntry)
  /-- Last-scan work counters (measurement data). -/
  work : WatchWork := {}
  /-- The per-entry distinctness invariant. -/
  ok : WatchLitsEntriesOK entries

/-- The empty index: the first scan classifies and records everything. -/
def WatchIndex.init : WatchIndex where
  entries := []
  ok := by
    intro j e he
    simp at he

/-- **THE UNCONDITIONAL WATCHED SCAN**: the self-validating pass over the
aligned entries. Every clause is either re-validated and skipped or classified
exactly like the reference scan; the returned index carries its invariant. -/
def scanDatabaseWatch2 (original : List Clause) (f : BranchFrame)
    (idx : WatchIndex) (db : List Clause) : PruningEvent × WatchIndex :=
  let doms := Frame.domains f
  let arr := frameDomainArray f
  let sums := sumsOfArray arr
  let q := scanWatch2Aux original doms f arr sums db (alignEntries db idx.entries)
  (q.1, { entries := q.2.1, work := q.2.2,
          ok := (scanWatch2Aux_spec original f db (alignEntries db idx.entries)
            (alignEntries_ok db idx.ok)).2 })

/-- **EVENT EQUALITY (unconditional)**: the self-validating scan returns
EXACTLY the certified `scanDatabase` event, on every index, frame and
database. -/
theorem scanDatabaseWatch2_fst_eq (original : List Clause) (f : BranchFrame)
    (idx : WatchIndex) (db : List Clause) :
    (scanDatabaseWatch2 original f idx db).1 = scanDatabase original f db := by
  unfold scanDatabaseWatch2
  exact (scanWatch2Aux_spec original f db (alignEntries db idx.entries)
    (alignEntries_ok db idx.ok)).1

/-- Same event as the wired executable oracle `scanDatabaseFast`
(`DbScanIndex.lean`), by `scanDatabaseFast_eq`. -/
theorem scanDatabaseWatch2_fst_eq_fast (original : List Clause) (f : BranchFrame)
    (idx : WatchIndex) (db : List Clause) :
    (scanDatabaseWatch2 original f idx db).1 = scanDatabaseFast original f db := by
  rw [scanDatabaseWatch2_fst_eq, scanDatabaseFast_eq]

end LeanFzn.Solver.Propagation
