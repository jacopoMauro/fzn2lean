/-
File: LeanFzn/Solver/Propagation/VersionWatch.lean

Purpose (PLAN §3.4, W1 versioned invalidation): the VERSION-KEYED watched
clause index. This is the W1 variant that consumes the dispatcher-threaded
per-slot version vector (`SlotVersions.lean`) instead of re-reading domains.

An entry records the two watched POSITIONS, the two watched LITERALS, the
version stamps of their slots at recording time, and the database generation.
The skip test is three integer comparisons (generation and the two stamps) —
no clause read, no domain read. The steady-state per-clause cost is therefore
the oracle's classification cost for the few clauses that must be
reclassified plus an O(1) stamp test for the rest.

Soundness bridge:

* `domain_eq_of_version_eq` (SlotVersions) — equal stamps between a sync's
  endpoints ⇒ equal slot domains;
* `literalImpossible_congr` — possibility depends only on the literal's slot
  domain;
* `two_le_clauseRemaining_of_vEntry` — a valid entry whose stamps still match
  certifies two remaining literals (the existing
  `two_le_length_filter` machinery);
* `VWatchOK.bump` — the index invariant transports across one frame sync;
* `scanWatchVAux_spec` — at any `VWatchOK` index the versioned pass returns
  EXACTLY the certified `scanDatabase` event and keeps the invariant.

Database generations (`VersionWatch.gen`): the certified wrapper
(`scanDatabaseWatchV`) bumps the generation and resets the entry list to
`none` whenever the database length changes. The measured dispatcher policy
(`scanDatabaseWatchVPrepend`) instead exploits the certified runtime fact
that the only database mutation is a PREPEND: old entries stay aligned with
the preserved tail (`VWatchOK.prepend`) and the generation is kept. A
version-stale entry is re-validated from the two slot summaries; when both
recorded literals are still possible it is refreshed in place (`.refresh`,
no clause read and no reclassification), so only a genuinely dead watch pays
the full classification.

MEASURED (2026-10-24, `tests_heur_timing --watch 46 300000` /
`--watch-battery 400000`; oracle = the wired `scanDatabaseFast`, same states,
0 event disagreements):

* FBDk04: oracle 899-932 ms vs versioned (prepend+refresh) 1349-1380 ms
  (1.5x), self-validating 2313-2369 ms. Reset-only versioned: 2158 ms.
  8.93M version fast-skips, 156k rechecks, 668k classifies, 3114 database
  length changes; `sync` (frameEvents + bumpEvents) is 18-19 ms total.
* 43-instance battery: oracle 14-15 ms vs versioned 25 ms, self-validating
  138 ms.

The residual is per-clause bookkeeping, not invalidation: the entry list is
rebuilt by pure recursion (one `Option VWatchEntry` cons per visited clause,
13.8M per FBDk04 run) and the classification of the ~0.8M non-skipped clauses
goes through `clauseClassifyFast` plus a second first-two-positions scan for
the entry. The domain-version stamp is also coarser than the oracle's
summary test: a narrowing that keeps the watched literal possible still
moves the stamp, which the `.refresh` path absorbs with two O(1) summary
tests. On the small battery the oracle's summary classification of the same
clauses is simply cheaper than maintaining the entry list. The module is
therefore kept UNWIRED; `nextPruningEventSched` still uses
`scanDatabaseFast`, and the public measurements are unchanged. E2's cache
keying can reuse `SlotVersions`/`VersionWatch.sync` as a follow-up.

DAG: ClauseWatch + SlotVersions -> VersionWatch.
-/
import LeanFzn.Legacy.Solver.Propagation.ClauseWatch
import LeanFzn.Legacy.Solver.Propagation.SlotVersions
open LeanFzn.Semantics LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

namespace LeanFzn.Solver.Propagation

/-- A version-keyed watch entry: two distinct clause positions, the literals
recorded there, the version stamps of their slots, and the database
generation. -/
structure VWatchEntry where
  /-- first watched clause position -/
  i : Nat
  /-- second watched clause position (strictly greater) -/
  j : Nat
  /-- literal recorded at position `i` -/
  li : Literal
  /-- literal recorded at position `j` -/
  lj : Literal
  /-- version stamp of `li`'s slot -/
  vi : Nat
  /-- version stamp of `lj`'s slot -/
  vj : Nat
  /-- database generation this entry was recorded at -/
  gen : Nat
  deriving Repr

/-- **ENTRY VALIDITY (version-keyed)**: the clause carries the recorded
literals at the recorded positions, the stamps are not in the future, and
whenever the current stamps still equal the recorded ones both literals are
possible at the frame. (The `≤` halves make the implication stable under
`bumpEvents`, whose counters only grow.) -/
def VEntryOK (v : SlotVersions) (f : BranchFrame) (c : Clause)
    (e : VWatchEntry) : Prop :=
  e.i < e.j ∧
  c[e.i]? = some e.li ∧ c[e.j]? = some e.lj ∧
  e.vi ≤ v.getD e.li.atom.slot 0 ∧ e.vj ≤ v.getD e.lj.atom.slot 0 ∧
  (v.getD e.li.atom.slot 0 = e.vi → v.getD e.lj.atom.slot 0 = e.vj →
    literalImpossible f e.li = false ∧ literalImpossible f e.lj = false)

/-- Refresh an entry's version stamps to the current vector (positions and
literals unchanged). -/
def VWatchEntry.refresh (v : SlotVersions) (e : VWatchEntry) : VWatchEntry :=
  { e with vi := v.getD e.li.atom.slot 0, vj := v.getD e.lj.atom.slot 0 }

/-- **THE ALIGNED INDEX INVARIANT**: every aligned `some` entry is valid. -/
def VWatchOK (v : SlotVersions) (f : BranchFrame) (db : List Clause)
    (es : List (Option VWatchEntry)) : Prop :=
  ∀ (j : Nat) (c : Clause) (e : VWatchEntry),
    db[j]? = some c → es[j]? = some (some e) → VEntryOK v f c e

theorem VWatchOK.tail {v : SlotVersions} {f : BranchFrame} {c : Clause}
    {e : Option VWatchEntry} {rest : List Clause}
    {es : List (Option VWatchEntry)}
    (h : VWatchOK v f (c :: rest) (e :: es)) : VWatchOK v f rest es :=
  fun j c' e' hj he => h (j + 1) c' e' (by simpa using hj) (by simpa using he)

theorem VWatchOK.cons_head {v : SlotVersions} {f : BranchFrame} {c : Clause}
    {e : Option VWatchEntry} {rest : List Clause}
    {es : List (Option VWatchEntry)}
    (h0 : ∀ en, e = some en → VEntryOK v f c en)
    (htail : VWatchOK v f rest es) :
    VWatchOK v f (c :: rest) (e :: es) := by
  intro j c' e' hj he
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj he
      subst hj
      exact h0 e' he
  | succ k => exact htail k c' e' (by simpa using hj) (by simpa using he)

/-- A reset entry list (all `none`) satisfies the invariant vacuously. -/
theorem VWatchOK.reset (v : SlotVersions) (f : BranchFrame) (db : List Clause) :
    VWatchOK v f db (List.replicate db.length none) := by
  intro j c e _ he
  by_cases hj : j < db.length
  · rw [List.getElem?_replicate_of_lt hj] at he
    exact absurd he (by simp)
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)] at he
    exact absurd he (by simp)

/-- **PREPEND ALIGNMENT**: prepending `k` database clauses (the certified
runtime's only database mutation) shifts the entry list by `k` `none`s and
keeps the invariant, because the old entries still describe the preserved
tail. -/
theorem VWatchOK.prepend (pre : List Clause) {v : SlotVersions} {f : BranchFrame}
    {db : List Clause} {es : List (Option VWatchEntry)}
    (h : VWatchOK v f db es) :
    VWatchOK v f (pre ++ db) (List.replicate pre.length none ++ es) := by
  intro j c e hj he
  rw [List.getElem?_append, List.length_replicate] at he
  by_cases hjk : j < pre.length
  · rw [if_pos hjk] at he
    rw [List.getElem?_replicate_of_lt hjk] at he
    exact absurd he (by simp)
  · rw [if_neg hjk] at he
    rw [List.getElem?_append, if_neg hjk] at hj
    exact h (j - pre.length) c e hj he

/-- `literalImpossible` depends only on the literal's own slot domain. -/
theorem literalImpossible_congr {f g : BranchFrame} {l : Literal}
    (h : (Frame.domains f).getD l.atom.slot Dom.empty =
      (Frame.domains g).getD l.atom.slot Dom.empty) :
    literalImpossible f l = literalImpossible g l := by
  unfold literalImpossible
  rw [h]

/-- **THE BRIDGE**: a valid version-keyed entry whose stamps still match the
current vector certifies at least two remaining literals. -/
theorem two_le_clauseRemaining_of_vEntry {v : SlotVersions} {f : BranchFrame}
    {c : Clause} {e : VWatchEntry} (hok : VEntryOK v f c e)
    (hvi : v.getD e.li.atom.slot 0 = e.vi)
    (hvj : v.getD e.lj.atom.slot 0 = e.vj) :
    2 ≤ (clauseRemaining f c).length := by
  obtain ⟨hij, hci, hcj, _, _, hp⟩ := hok
  obtain ⟨hp1, hp2⟩ := hp hvi hvj
  obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp hci
  obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hcj
  have hp1' : literalImpossible f (c[e.i]'hi) = false := by
    rw [show c[e.i]'hi = e.li from hgeti]
    exact hp1
  have hp2' : literalImpossible f (c[e.j]'hj) = false := by
    rw [show c[e.j]'hj = e.lj from hgetj]
    exact hp2
  have := two_le_length_filter (l := c) (p := fun l => !literalImpossible f l)
    hi hj (Nat.ne_of_lt hij) (by simp [hp1']) (by simp [hp2'])
  simpa [clauseRemaining] using this

/-- **TRANSPORT ACROSS ONE SYNC**: the invariant survives a `bumpEvents` sync
from the recorded frame to the current one, for any `VWatchOK` index. -/
theorem VWatchOK.bump {stv v : SlotVersions} {stf f : BranchFrame}
    {db : List Clause} {es : List (Option VWatchEntry)}
    (hok : VWatchOK stv stf db es)
    (hsync : v = stv.bumpEvents (frameEvents stf f))
    (hsizef : stv.size = (Frame.domains stf).length)
    (hsizeg : v.size = (Frame.domains f).length) :
    VWatchOK v f db es := by
  subst hsync
  intro j c e hdb hes
  obtain ⟨hij, hci, hcj, hlei, hlej, hp⟩ := hok j c e hdb hes
  have hgei := bumpEvents_getD_ge stv (frameEvents stf f) e.li.atom.slot
  have hgej := bumpEvents_getD_ge stv (frameEvents stf f) e.lj.atom.slot
  refine ⟨hij, hci, hcj, Nat.le_trans hlei hgei, Nat.le_trans hlej hgej, ?_⟩
  intro hvi hvj
  have heqi : stv.getD e.li.atom.slot 0 = e.vi := by omega
  have heqj : stv.getD e.lj.atom.slot 0 = e.vj := by omega
  obtain ⟨hp1, hp2⟩ := hp heqi heqj
  have hdomi : (Frame.domains stf).getD e.li.atom.slot Dom.empty =
      (Frame.domains f).getD e.li.atom.slot Dom.empty :=
    domain_eq_of_version_eq (v := stv) (f := stf) (g := f) hsizef hsizeg (by omega)
  have hdomj : (Frame.domains stf).getD e.lj.atom.slot Dom.empty =
      (Frame.domains f).getD e.lj.atom.slot Dom.empty :=
    domain_eq_of_version_eq (v := stv) (f := stf) (g := f) hsizef hsizeg (by omega)
  exact ⟨by rw [← literalImpossible_congr hdomi]; exact hp1,
         by rw [← literalImpossible_congr hdomj]; exact hp2⟩

/-! ### Recording: the first two possible positions under the fast test -/

/-- First position whose literal is possible under the summary-driven test,
together with that literal. -/
def remIdxFirstLit (a : Array Domain) (sums : Array SlotSum) :
    List Literal → Nat → Option (Nat × Literal)
  | [], _ => none
  | l :: ls, idx =>
      if literalImpossibleFast a sums l = true then
        remIdxFirstLit a sums ls (idx + 1)
      else some (idx, l)

/-- The first two positions whose literals are possible under the fast test,
with the literals themselves. -/
def remIdxFirstTwoLits (a : Array Domain) (sums : Array SlotSum) :
    List Literal → Nat → Option (Nat × Literal × Nat × Literal)
  | [], _ => none
  | l :: ls, idx =>
      if literalImpossibleFast a sums l = true then
        remIdxFirstTwoLits a sums ls (idx + 1)
      else
        match remIdxFirstLit a sums ls (idx + 1) with
        | some (j, lj) => some (idx, l, j, lj)
        | none => none

theorem remIdxFirstLit_spec {a : Array Domain} {sums : Array SlotSum}
    {lits : List Literal} {idx k : Nat} {lk : Literal}
    (h : remIdxFirstLit a sums lits idx = some (k, lk)) :
    ∃ t, ∃ ht : t < lits.length, k = idx + t ∧ lits[t]'ht = lk ∧
      literalImpossibleFast a sums lk = false := by
  induction lits generalizing idx with
  | nil => simp [remIdxFirstLit] at h
  | cons l ls ih =>
      by_cases himp : literalImpossibleFast a sums l = true
      · rw [remIdxFirstLit, if_pos himp] at h
        obtain ⟨t, ht, hk, hl, hp⟩ := ih h
        exact ⟨t + 1, by simpa using ht, by omega, by simpa using hl,
          by simpa using hp⟩
      · rw [remIdxFirstLit, if_neg himp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨0, by simp, by omega, rfl, by simpa using himp⟩

theorem remIdxFirstTwoLits_spec {a : Array Domain} {sums : Array SlotSum}
    {lits : List Literal} {idx i j : Nat} {li lj : Literal}
    (h : remIdxFirstTwoLits a sums lits idx = some (i, li, j, lj)) :
    i < j ∧
    (∃ ti, ∃ hti : ti < lits.length, i = idx + ti ∧ lits[ti]'hti = li ∧
      literalImpossibleFast a sums li = false) ∧
    (∃ tj, ∃ htj : tj < lits.length, j = idx + tj ∧ lits[tj]'htj = lj ∧
      literalImpossibleFast a sums lj = false) := by
  induction lits generalizing idx with
  | nil => simp [remIdxFirstTwoLits] at h
  | cons l ls ih =>
      by_cases himp : literalImpossibleFast a sums l = true
      · rw [remIdxFirstTwoLits, if_pos himp] at h
        obtain ⟨hij, hi, hj⟩ := ih h
        obtain ⟨ti, hti, hik, hli, hpi⟩ := hi
        obtain ⟨tj, htj, hjk, hlj, hpj⟩ := hj
        exact ⟨hij, ⟨ti + 1, by simpa using hti, by omega, by simpa using hli,
            by simpa using hpi⟩,
          ⟨tj + 1, by simpa using htj, by omega, by simpa using hlj,
            by simpa using hpj⟩⟩
      · rw [remIdxFirstTwoLits, if_neg himp] at h
        cases hf : remIdxFirstLit a sums ls (idx + 1) with
        | none => rw [hf] at h; simp at h
        | some p =>
            obtain ⟨k, lk⟩ := p
            rw [hf] at h
            dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            obtain ⟨t, ht, hk, hl, hp⟩ := remIdxFirstLit_spec hf
            exact ⟨by omega,
              ⟨0, by simp, by omega, rfl, by simpa using himp⟩,
              ⟨t + 1, by simpa using ht, by omega, by simpa using hl,
                by simpa using hp⟩⟩

/-- Classification AND the version-keyed entry: the first component is the
wired fast classifier (`clauseClassifyFast`), the second records the first two
possible literals when at least two remain. -/
def clauseClassifyVF (a : Array Domain) (sums : Array SlotSum)
    (v : SlotVersions) (gen : Nat) (c : Clause) :
    Option (Option Literal) × Option VWatchEntry :=
  match clauseClassifyFast a sums c none with
  | some none =>
      match remIdxFirstTwoLits a sums c 0 with
      | some (i, li, j, lj) =>
          (some none,
            some ⟨i, j, li, lj, v.getD li.atom.slot 0,
              v.getD lj.atom.slot 0, gen⟩)
      | none => (some none, none)
  | cl => (cl, none)

theorem clauseClassifyVF_fst (a : Array Domain) (sums : Array SlotSum)
    (v : SlotVersions) (gen : Nat) (c : Clause) :
    (clauseClassifyVF a sums v gen c).1 = clauseClassifyFast a sums c none := by
  unfold clauseClassifyVF
  cases h : clauseClassifyFast a sums c none with
  | none => rfl
  | some cl =>
      cases cl with
      | some l => rfl
      | none =>
          cases htwo : remIdxFirstTwoLits a sums c 0 with
          | none => rfl
          | some p =>
              obtain ⟨i, li, j, lj⟩ := p
              rfl

theorem clauseClassifyVF_snd_ok {a : Array Domain} {sums : Array SlotSum}
    {v : SlotVersions} {gen : Nat} {f : BranchFrame} {c : Clause}
    (ha : ∀ l, literalImpossibleFast a sums l = literalImpossible f l) :
    ∀ e, (clauseClassifyVF a sums v gen c).2 = some e → VEntryOK v f c e := by
  intro e he
  unfold clauseClassifyVF at he
  cases hcl : clauseClassifyFast a sums c none with
  | none => rw [hcl] at he; exact absurd he (by simp)
  | some cl =>
      cases cl with
      | some l => rw [hcl] at he; exact absurd he (by simp)
      | none =>
          cases htwo : remIdxFirstTwoLits a sums c 0 with
          | none => rw [hcl, htwo] at he; exact absurd he (by simp)
          | some p =>
              obtain ⟨i, li, j, lj⟩ := p
              rw [hcl, htwo] at he
              simp only [Option.some.injEq] at he
              subst he
              obtain ⟨hij, hi, hj⟩ := remIdxFirstTwoLits_spec htwo
              obtain ⟨ti, hti, hik, hli, hpi⟩ := hi
              obtain ⟨tj, htj, hjk, hlj, hpj⟩ := hj
              have hci : c[i]? = some li := by
                rw [hik, Nat.zero_add, List.getElem?_eq_getElem hti, hli]
              have hcj : c[j]? = some lj := by
                rw [hjk, Nat.zero_add, List.getElem?_eq_getElem htj, hlj]
              refine ⟨by omega, hci, hcj, Nat.le_refl _,
                Nat.le_refl _, ?_⟩
              intro _ _
              refine ⟨?_, ?_⟩
              · rw [← ha]; exact hpi
              · rw [← ha]; exact hpj

/-! ### The version-keyed scan -/

/-- The per-clause result of the version-keyed fast pass. -/
inductive VStepResult where
  | stop (ev : PruningEvent) (e : Option VWatchEntry)
  | skip
  /-- versions moved but both recorded literals are still possible: keep the
  entry with refreshed stamps. -/
  | refresh (e : VWatchEntry)
  | go (e : Option VWatchEntry)

/-- Classification step (no skip test). -/
def vWatchClassifyStep (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum) (v : SlotVersions) (gen : Nat)
    (c : Clause) : VStepResult :=
  match clauseClassifyVF a sums v gen c with
  | (cl, e') =>
      match cl with
      | none => .stop (.conflict [c]) e'
      | some none => .go e'
      | some (some l) =>
          if productiveFast l f then
            .stop (.implied l c false (!(original.contains c))) e'
          else .go e'

/-- One clause: skip when the entry's generation is current and both watch
slot stamps are unchanged. When the generation is current but a stamp moved,
re-validate the two recorded literals against the slot summaries: if both are
still possible the clause is refreshed in place (no clause/domain re-read,
no reclassification); otherwise classify and re-record. A stale generation
always reclassifies. -/
def vWatchStep (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum) (v : SlotVersions) (gen : Nat)
    (c : Clause) (e : Option VWatchEntry) : VStepResult :=
  match e with
  | some en =>
      if en.gen == gen then
        if v.getD en.li.atom.slot 0 == en.vi && v.getD en.lj.atom.slot 0 == en.vj then
          .skip
        else if literalImpossibleFast a sums en.li = false &&
            literalImpossibleFast a sums en.lj = false then
          .refresh (en.refresh v)
        else vWatchClassifyStep original f a sums v gen c
      else vWatchClassifyStep original f a sums v gen c
  | none => vWatchClassifyStep original f a sums v gen c

theorem vWatchClassifyStep_spec {original : List Clause} {f : BranchFrame}
    {a : Array Domain} {sums : Array SlotSum} {v : SlotVersions} {gen : Nat}
    {c : Clause}
    (hclc : (clauseClassifyVF a sums v gen c).1 =
      reduceRemaining (clauseRemaining f c))
    (hokc : ∀ en, (clauseClassifyVF a sums v gen c).2 = some en →
      VEntryOK v f c en) :
    (match vWatchClassifyStep original f a sums v gen c with
     | .skip => False
     | .refresh e' => False
     | .go e' => (∀ en, e' = some en → VEntryOK v f c en) ∧
         (clauseClassifyVF a sums v gen c).1 = reduceRemaining (clauseRemaining f c) ∧
         ((clauseClassifyVF a sums v gen c).1 = some none ∨
          ∃ l, (clauseClassifyVF a sums v gen c).1 = some (some l) ∧
            productiveFast l f = false)
     | .stop ev e' => (∀ en, e' = some en → VEntryOK v f c en) ∧
         (clauseClassifyVF a sums v gen c).1 = reduceRemaining (clauseRemaining f c) ∧
         (((clauseClassifyVF a sums v gen c).1 = none ∧ ev = .conflict [c]) ∨
          ∃ l, (clauseClassifyVF a sums v gen c).1 = some (some l) ∧
            productiveFast l f = true ∧
            ev = .implied l c false (!(original.contains c)))) := by
  unfold vWatchClassifyStep
  cases hp : clauseClassifyVF a sums v gen c with
  | mk cl e' =>
      dsimp only
      have hcl := hclc
      rw [hp] at hcl
      have hok' : ∀ en, e' = some en → VEntryOK v f c en := by
        intro en hen
        exact hokc en (by rw [hp]; exact hen)
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
              by_cases hprod : productiveFast l f = true
              · rw [if_pos hprod]
                dsimp only
                exact ⟨hok', hcl, Or.inr ⟨l, rfl, hprod, rfl⟩⟩
              · rw [if_neg hprod]
                dsimp only
                exact ⟨hok', hcl,
                  Or.inr ⟨l, rfl, Bool.eq_false_iff.mpr hprod⟩⟩

/-- **THE ONE-CLAUSE SPEC**: a skip certifies two remaining literals, a
refresh keeps the entry valid at the current vector, classification equals the
reference classification with a valid fresh entry, and a stop carries exactly
the reference event. -/
theorem vWatchStep_spec {original : List Clause} {f : BranchFrame}
    {a : Array Domain} {sums : Array SlotSum} {v : SlotVersions} {gen : Nat}
    {c : Clause} {e : Option VWatchEntry}
    (ha : ∀ l, literalImpossibleFast a sums l = literalImpossible f l)
    (hclc : (clauseClassifyVF a sums v gen c).1 =
      reduceRemaining (clauseRemaining f c))
    (hokc : ∀ en, (clauseClassifyVF a sums v gen c).2 = some en →
      VEntryOK v f c en)
    (hok : ∀ en, e = some en → VEntryOK v f c en) :
    (match vWatchStep original f a sums v gen c e with
     | .skip => 2 ≤ (clauseRemaining f c).length
     | .refresh e' => VEntryOK v f c e' ∧
         e'.vi = v.getD e'.li.atom.slot 0 ∧ e'.vj = v.getD e'.lj.atom.slot 0
     | .go e' => (∀ en, e' = some en → VEntryOK v f c en) ∧
         (clauseClassifyVF a sums v gen c).1 = reduceRemaining (clauseRemaining f c) ∧
         ((clauseClassifyVF a sums v gen c).1 = some none ∨
          ∃ l, (clauseClassifyVF a sums v gen c).1 = some (some l) ∧
            productiveFast l f = false)
     | .stop ev e' => (∀ en, e' = some en → VEntryOK v f c en) ∧
         (clauseClassifyVF a sums v gen c).1 = reduceRemaining (clauseRemaining f c) ∧
         (((clauseClassifyVF a sums v gen c).1 = none ∧ ev = .conflict [c]) ∨
          ∃ l, (clauseClassifyVF a sums v gen c).1 = some (some l) ∧
            productiveFast l f = true ∧
            ev = .implied l c false (!(original.contains c)))) := by
  unfold vWatchStep
  cases e with
  | none =>
      dsimp only
      cases h : vWatchClassifyStep original f a sums v gen c with
      | skip =>
          have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
          rw [h] at hspec
          exact False.elim hspec
      | refresh e' =>
          have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
          rw [h] at hspec
          exact False.elim hspec
      | go e' =>
          have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
          rw [h] at hspec
          exact hspec
      | stop ev e' =>
          have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
          rw [h] at hspec
          exact hspec
  | some en =>
      dsimp only
      by_cases hgen : (en.gen == gen) = true
      · rw [if_pos hgen]
        by_cases hstamps : (v.getD en.li.atom.slot 0 == en.vi &&
            v.getD en.lj.atom.slot 0 == en.vj) = true
        · rw [if_pos hstamps]
          dsimp only
          rw [Bool.and_eq_true] at hstamps
          obtain ⟨hvi, hvj⟩ := hstamps
          have hvi' : v.getD en.li.atom.slot 0 = en.vi := beq_iff_eq.mp hvi
          have hvj' : v.getD en.lj.atom.slot 0 = en.vj := beq_iff_eq.mp hvj
          exact two_le_clauseRemaining_of_vEntry (hok en rfl) hvi' hvj'
        · rw [if_neg hstamps]
          by_cases hposs : (literalImpossibleFast a sums en.li = false &&
              literalImpossibleFast a sums en.lj = false) = true
          · rw [if_pos hposs]
            rw [Bool.and_eq_true] at hposs
            obtain ⟨hpi, hpj⟩ := hposs
            have hpi' : literalImpossibleFast a sums en.li = false :=
              of_decide_eq_true hpi
            have hpj' : literalImpossibleFast a sums en.lj = false :=
              of_decide_eq_true hpj
            obtain ⟨hij, hci, hcj, _, _, _⟩ := hok en rfl
            refine ⟨⟨hij, hci, hcj, Nat.le_refl _, Nat.le_refl _, ?_⟩, rfl, rfl⟩
            intro _ _
            exact ⟨by rw [← ha]; simpa [VWatchEntry.refresh] using hpi',
                   by rw [← ha]; simpa [VWatchEntry.refresh] using hpj'⟩
          · rw [if_neg hposs]
            cases h : vWatchClassifyStep original f a sums v gen c with
            | skip =>
                have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
                rw [h] at hspec
                exact False.elim hspec
            | refresh e' =>
                have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
                rw [h] at hspec
                exact False.elim hspec
            | go e' =>
                have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
                rw [h] at hspec
                exact hspec
            | stop ev e' =>
                have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
                rw [h] at hspec
                exact hspec
      · rw [if_neg hgen]
        cases h : vWatchClassifyStep original f a sums v gen c with
        | skip =>
            have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
            rw [h] at hspec
            exact False.elim hspec
        | refresh e' =>
            have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
            rw [h] at hspec
            exact False.elim hspec
        | go e' =>
            have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
            rw [h] at hspec
            exact hspec
        | stop ev e' =>
            have hspec := vWatchClassifyStep_spec (original := original) hclc hokc
            rw [h] at hspec
            exact hspec

/-- Per-scan work counters (measurement data; no proof role). -/
structure VWork where
  /-- Clauses skipped by the version test. -/
  skips : Nat := 0
  /-- Entry-carrying clauses reclassified. -/
  rechecks : Nat := 0
  /-- Entry-less clauses classified. -/
  classifies : Nat := 0
  /-- Version-stale entries revalidated from the slot summaries. -/
  refreshes : Nat := 0

/-- The fast-pass scan recursion. -/
def scanWatchVAux (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum) (v : SlotVersions) (gen : Nat) :
    List Clause → List (Option VWatchEntry) →
      PruningEvent × List (Option VWatchEntry) × VWork
  | [], _ => (.stable, [], {})
  | c :: rest, es =>
      match vWatchStep original f a sums v gen c (es.headD none) with
      | .stop ev e' =>
          (ev, e' :: es.tail,
            if (es.headD none).isSome then { rechecks := 1 } else { classifies := 1 })
      | .skip =>
          let q := scanWatchVAux original f a sums v gen rest es.tail
          (q.1, es.headD none :: q.2.1, { q.2.2 with skips := q.2.2.skips + 1 })
      | .refresh e' =>
          let q := scanWatchVAux original f a sums v gen rest es.tail
          (q.1, some e' :: q.2.1, { q.2.2 with refreshes := q.2.2.refreshes + 1 })
      | .go e' =>
          let q := scanWatchVAux original f a sums v gen rest es.tail
          (q.1, e' :: q.2.1,
            if (es.headD none).isSome then { q.2.2 with rechecks := q.2.2.rechecks + 1 }
            else { q.2.2 with classifies := q.2.2.classifies + 1 })

/-- **THE SCAN SPEC (version-keyed)**: at any aligned index satisfying
`VWatchOK`, the version-keyed pass returns EXACTLY the certified
`scanDatabase` event (same order, same early exit, same payloads) and keeps
the invariant. -/
theorem scanWatchVAux_spec (original : List Clause) (f : BranchFrame)
    (a : Array Domain) (sums : Array SlotSum)
    (ha : ∀ l, literalImpossibleFast a sums l = literalImpossible f l) :
    ∀ (db : List Clause) (es : List (Option VWatchEntry)) (v : SlotVersions)
      (gen : Nat),
      VWatchOK v f db es →
      (scanWatchVAux original f a sums v gen db es).1 =
        scanDatabase original f db ∧
      VWatchOK v f db (scanWatchVAux original f a sums v gen db es).2.1 := by
  intro db
  induction db with
  | nil =>
      intro es v gen _
      rw [scanWatchVAux]
      refine ⟨rfl, ?_⟩
      intro j c e hj he
      simp at he
  | cons c rest ih =>
      intro es v gen hok
      have hhead : ∀ en, es.headD none = some en → VEntryOK v f c en := by
        intro en hen
        cases es with
        | nil => simp at hen
        | cons e es' =>
            exact hok 0 c en (by simp) (by simpa using hen)
      have htail : VWatchOK v f rest es.tail := by
        cases es with
        | nil => intro j c' e' _ he; simp at he
        | cons e es' => exact VWatchOK.tail hok
      obtain ⟨hev, hent⟩ := ih es.tail v gen htail
      have hws := vWatchStep_spec (original := original) (f := f) (a := a)
        (sums := sums) (v := v) (gen := gen) (c := c) (e := es.headD none)
        ha
        (by rw [clauseClassifyVF_fst]; exact clauseClassifyFast_none a sums f c (fun l _ => ha l))
        (clauseClassifyVF_snd_ok ha)
        hhead
      rw [scanWatchVAux]
      cases hs : vWatchStep original f a sums v gen c (es.headD none) with
      | stop ev e' =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          obtain ⟨hoke', hcl, hstopshape⟩ := hws
          refine ⟨?_, VWatchOK.cons_head hoke' htail⟩
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
                    rw [← productiveFast_eq, hprod, hev']
                    simp only [if_pos trivial]
              | cons y ys =>
                  rw [hr] at hcl
                  dsimp only [reduceRemaining] at hcl
                  rcases hstopshape with ⟨hcn, _⟩ | ⟨l, hsome, _, _⟩
                  · exact absurd (hcl.symm.trans hcn) (by simp)
                  · exact absurd (hcl.symm.trans hsome) (by simp)
      | refresh e' =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          obtain ⟨hoke', hvi, hvj⟩ := hws
          have h2 : 2 ≤ (clauseRemaining f c).length :=
            two_le_clauseRemaining_of_vEntry hoke' hvi.symm hvj.symm
          refine ⟨?_, VWatchOK.cons_head (fun en hen => ?_) hent⟩
          · rw [scanDatabase]
            cases hr : clauseRemaining f c with
            | nil => rw [hr] at h2; simp at h2
            | cons x xs =>
                cases xs with
                | nil => rw [hr] at h2; simp at h2
                | cons y ys => exact hev
          · rw [Option.some.injEq] at hen
            subst hen
            exact hoke'
      | skip =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          refine ⟨?_, VWatchOK.cons_head hhead hent⟩
          rw [scanDatabase]
          cases hr : clauseRemaining f c with
          | nil => rw [hr] at hws; simp at hws
          | cons x xs =>
              cases xs with
              | nil => rw [hr] at hws; simp at hws
              | cons y ys => exact hev
      | go e' =>
          dsimp only
          rw [hs] at hws
          dsimp only at hws
          obtain ⟨hoke', hcl, hclshape⟩ := hws
          refine ⟨?_, VWatchOK.cons_head hoke' hent⟩
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
                    rw [← productiveFast_eq, hprod]
                    exact hev
              | cons y ys => exact hev

/-! ### The threaded state and the reset-on-database-change wrapper -/

/-- The value-carried versioned watch state: the entry list together with the
version vector, the frame it was synced at, the database generation and the
database length it was recorded for. -/
structure VersionWatch where
  /-- the recorded watch entries (positional, aligned with the database) -/
  entries : List (Option VWatchEntry)
  /-- the per-slot version vector at `vframe` -/
  versions : SlotVersions
  /-- the frame at which `versions` was last synced -/
  vframe : BranchFrame
  /-- database generation (`+1` per observed database-length change) -/
  gen : Nat
  /-- database length at the last scan -/
  dbLen : Nat
  /-- last-scan work counters (measurement data) -/
  work : VWork := {}

/-- The empty state at a frame: all counters start at zero. -/
def VersionWatch.init (f : BranchFrame) : VersionWatch where
  entries := []
  versions := (List.replicate (Frame.domains f).length 0).toArray
  vframe := f
  gen := 0
  dbLen := 0

/-- Sync the version vector from `vframe` to `f` by the E0 events. A width
change (which the dispatcher never performs) conservatively restarts the
vector at zero. -/
def VersionWatch.sync (st : VersionWatch) (f : BranchFrame) : SlotVersions :=
  if st.versions.size = (Frame.domains f).length then
    st.versions.bumpEvents (frameEvents st.vframe f)
  else
    (List.replicate (Frame.domains f).length 0).toArray

/-- The synced vector always has the frame's width (the vector never changes
length across a sync). -/
theorem VersionWatch.sync_size (st : VersionWatch) (f : BranchFrame) :
    (st.sync f).size = (Frame.domains f).length := by
  unfold VersionWatch.sync
  split
  · rw [bumpEvents_size]; assumption
  · simp

/-- **THE VERSIONED SCAN**: sync the version vector, reset the entries when
the database length changed (generation bump), and run the version-keyed
pass. The returned state carries the synced vector and frame. -/
def scanDatabaseWatchV (original : List Clause) (f : BranchFrame)
    (st : VersionWatch) (db : List Clause) : PruningEvent × VersionWatch :=
  let gen := if db.length == st.dbLen then st.gen else st.gen + 1
  let es := if db.length == st.dbLen then st.entries
    else List.replicate db.length none
  let v := st.sync f
  let a := frameDomainArray f
  let q := scanWatchVAux original f a (sumsOfArray a) v gen db es
  (q.1, { entries := q.2.1, versions := v, vframe := f, gen := gen,
          dbLen := db.length, work := q.2.2 })

/-- The entry list the wrapper hands to the fast pass. -/
def VersionWatch.entriesFor (st : VersionWatch) (db : List Clause) :
    List (Option VWatchEntry) :=
  if db.length == st.dbLen then st.entries else List.replicate db.length none

/-- **PREPEND-AWARE SCAN (database extensions only)**: when the database
grew, the certified runtime only PREPENDS learned clauses, so the old entries
stay aligned with the preserved tail (`replicate k none ++ entries`). A
shrink still resets. The generation is left unchanged on an extension: the
entries still describe the same clauses. (The reset policy above is the
unconditional wrapper; this one is the dispatcher policy, whose soundness
needs the extension fact `db = pre ++ old` at the call site.) -/
def scanDatabaseWatchVPrepend (original : List Clause) (f : BranchFrame)
    (st : VersionWatch) (db : List Clause) : PruningEvent × VersionWatch :=
  let v := st.sync f
  let a := frameDomainArray f
  let es := if st.dbLen ≤ db.length then
      List.replicate (db.length - st.dbLen) none ++ st.entries
    else List.replicate db.length none
  let q := scanWatchVAux original f a (sumsOfArray a) v st.gen db es
  (q.1, { entries := q.2.1, versions := v, vframe := f, gen := st.gen,
          dbLen := db.length, work := q.2.2 })

/-- **EVENT EQUALITY (versioned scan)**: for any entry list satisfying the
versioned index invariant at the synced vector, the wrapper returns exactly
the certified `scanDatabase` event. -/
theorem scanDatabaseWatchV_fst_eq (original : List Clause) (f : BranchFrame)
    (st : VersionWatch) (db : List Clause)
    (hok : VWatchOK (st.sync f) f db (st.entriesFor db)) :
    (scanDatabaseWatchV original f st db).1 = scanDatabase original f db := by
  unfold scanDatabaseWatchV
  unfold VersionWatch.entriesFor at hok
  have ha : ∀ l, literalImpossibleFast (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) l = literalImpossible f l :=
    fun l => (literalImpossibleFast_eq (frameDomainArray f) l).trans
      (literalImpossibleArr_eq f l)
  by_cases hlen : (db.length == st.dbLen) = true
  · simp only [if_pos hlen] at hok ⊢
    exact (scanWatchVAux_spec original f (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) ha db st.entries (st.sync f) st.gen hok).1
  · simp only [if_neg hlen] at hok ⊢
    exact (scanWatchVAux_spec original f (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) ha db (List.replicate db.length none)
      (st.sync f) (st.gen + 1) hok).1

/-- **EVENT EQUALITY (prepend-aware scan)**: under the same entry invariant
the prepend-aligned wrapper returns exactly the certified event. -/
theorem scanDatabaseWatchVPrepend_fst_eq (original : List Clause) (f : BranchFrame)
    (st : VersionWatch) (db : List Clause)
    (hok : VWatchOK (st.sync f) f db
      (if st.dbLen ≤ db.length then
        List.replicate (db.length - st.dbLen) none ++ st.entries
      else List.replicate db.length none)) :
    (scanDatabaseWatchVPrepend original f st db).1 = scanDatabase original f db := by
  unfold scanDatabaseWatchVPrepend
  have ha : ∀ l, literalImpossibleFast (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) l = literalImpossible f l :=
    fun l => (literalImpossibleFast_eq (frameDomainArray f) l).trans
      (literalImpossibleArr_eq f l)
  by_cases hlen : st.dbLen ≤ db.length
  · simp only [if_pos hlen] at hok ⊢
    exact (scanWatchVAux_spec original f (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) ha db
      (List.replicate (db.length - st.dbLen) none ++ st.entries)
      (st.sync f) st.gen hok).1
  · simp only [if_neg hlen] at hok ⊢
    exact (scanWatchVAux_spec original f (frameDomainArray f)
      (sumsOfArray (frameDomainArray f)) ha db (List.replicate db.length none)
      (st.sync f) st.gen hok).1

end LeanFzn.Solver.Propagation
