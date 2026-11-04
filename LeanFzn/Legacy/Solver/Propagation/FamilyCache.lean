/-
File: LeanFzn/Solver/Propagation/FamilyCache.lean

Purpose (PLAN §6, task E2 — incremental family summaries; the linear
min/max contribution family):

  The linear propagators `propLinLe2`/`propLinEq2` re-read, at every
  sweep position, the integer extrema of every *other* slot of the
  constraint (`domMinI`/`domMaxI` of the full domain lists). On 1HZ5
  (169 wide real-domain slots) that is the measured ~0.6 s per step.
  This module builds the module-level cache for exactly that cost: one
  `SlotEntry` per constraint slot holding

  * the domain snapshot the extrema were read from (the cache KEY),
  * the extrema themselves (`SlotSummary` — "min/max with their
    achieving values"), computed in ONE pass per slot.

  The cached run `propLinLe2Cached cache st coeffs is b` /
  `propLinEq2Cached` reads the extrema from the cache instead of
  rescanning the domains, is PROVED equal to the reference run under
  the validity predicate `CacheValid cache st` ("every stored entry is
  keyed by the slot's current domain and its summary is that domain's
  summary"), and the update operations (`touch` per changed slot,
  `touchSlots` for a batch/restoration, `invalidateSlot` conservative
  drop, `rebuild` from scratch) re-establish validity with the frame
  laws `touch_valid`/`touchSlots_valid`/`invalidateSlot_valid` plus
  coverage laws.

  The stale-reason obligation `StaleReasonOK` records what a cached
  explained outcome needs BEYOND a correct bound: the reason data must
  pin the emitted literal at the historical state where it was
  recorded (fields `hist_valid`/`hist_emits`), the head must still be
  entailed at the CURRENT box (`head_entailed` — the stale part), and
  the clause must be entailed by the constraint (`reason_entailed`).
  `staleReasonOK_of_valid` inhabits the schema from `CacheValid`, so
  it is not vacuous, and the machine-checked witness
  `stale_head_not_entailed` shows the strictness: with a stale entry
  the cached run emits a literal that is NOT entailed at the current
  state while all historical fields hold. That is the precise reason a
  cached bound alone is not enough.

  ROUTE: `propLinLe2Cached_eq` transfers the complete reference
  package (`propLinLe2_safe`, `propLinLe2_reason_valid`,
  `propLinLe2_entitled`) to the cached run, so the certified
  consumer obligations are unchanged once the cache invariant is
  threaded.

Design notes:

  * The cached kernels mirror the reference `linDeduceLe`/`linDeduceEq`
    arm-by-arm, but the `linSweep` fold is REUSED verbatim
    (`Fam/Lin.lean` is parameterized over the per-position kernel):
    the sweep congruence `linSweep_local` does the transport.
  * Extrema, not contributions-of-pairs, are cached: the contribution
    of a pair `(c, m)` is `c·mn` (c ≥ 0) or `c·mx` (c < 0) and the
    cause is built from the same extremum, so one per-slot summary
    serves every occurrence of a (duplicated) slot — and the cause
    pins and the summed extremum stay definitionally consistent, the
    property whose loss is exactly the stale-reason hazard.
  * The wiring lookup here is keyed lookup (`findSlot?`); the
    positional refinement `rebuild_getElem?`/`rebuild_get?_key` states
    the O(1) slot-indexed table the runtime wiring should use.

DAG:
  LeanFzn.Solver.Propagation.Proofs.Fam.Lin -> FamilyCache (this module)
  -> (future, coordinator-owned wiring) the scheduler state
     (`PropScheduler` gaining a cache field aligned with the propagator
     list, or `WorkQueue.lean`'s per-unit records extended for summary
     reuse; `EventContract.lean`'s `frameEvents` drives
     `touch`/`touchSlots`).

This module is proof-only: it does not wire the runtime and adds no
public assumption. No `sorry`/`admit`/custom axiom/`native_decide`/
`unsafe`; every verified profile here uses only the audit allowlist
(`propext`, `Quot.sound`, `Classical.choice`).
-/
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
  LeanFzn.Solver.Reference
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## 1. The per-slot extrema summary

`minContrib`/`maxContrib` and the cause constructors of `Fam/Lin.lean`
read a slot's domain only through `domMinI`/`domMaxI`. The summary below
is the cacheable projection; `summaryOfDomain` is its one-pass
computation (the intended runtime key is the D2 `Dom`/`SlotSum`
versioned summary — this proof model keeps the full domain as the key
and derives the summary, see the ledger at the end). -/

/-- The extrema of a slot's integer view: the exact data every linear
    contribution/cause read consumes. -/
structure SlotSummary where
  /-- The integer minimum of the domain (none for empty/unnamed sorts). -/
  minI : Option Int
  /-- The integer maximum of the domain. -/
  maxI : Option Int
  deriving Repr

/-- The summary of a domain: its two integer extrema. -/
def summaryOfDomain (d : Domain) : SlotSummary := ⟨domMinI d, domMaxI d⟩

/-- Projection of the summary computation. -/
theorem summaryOfDomain_min (d : Domain) : (summaryOfDomain d).minI = domMinI d :=
  rfl

/-- Projection of the summary computation. -/
theorem summaryOfDomain_max (d : Domain) : (summaryOfDomain d).maxI = domMaxI d :=
  rfl

/-! ## 2. The contribution/cause selectors as functions of the extrema

Structurally identical to `minContrib`/`maxContrib`/`linCauseMinPair`/
`linCauseMaxPair` with the domain reads replaced by explicit extrema;
the `_eq` bridges are definitional. -/

/-- `minContrib` as a function of the extrema. -/
def minContribOf (mn mx : Option Int) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  match mn, mx with
  | some a, some b =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * a) else some (p.2, p.1, p.1 * b)
  | _, _ => none

/-- The reference `minContrib` is the extrema-selector at the current
    domain's extrema. -/
theorem minContrib_eq_minContribOf (st : State) (p : Int × Nat) :
    minContrib st p = minContribOf (domMinI (st.domains.getD p.2 Dom.empty))
      (domMaxI (st.domains.getD p.2 Dom.empty)) p :=
  rfl

/-- `maxContrib` as a function of the extrema (the dual selection). -/
def maxContribOf (mn mx : Option Int) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  match mn, mx with
  | some a, some b =>
      if p.1 ≥ 0 then some (p.2, p.1, p.1 * b) else some (p.2, p.1, p.1 * a)
  | _, _ => none

/-- The reference `maxContrib` is the extrema-selector at the current
    domain's extrema. -/
theorem maxContrib_eq_maxContribOf (st : State) (p : Int × Nat) :
    maxContrib st p = maxContribOf (domMinI (st.domains.getD p.2 Dom.empty))
      (domMaxI (st.domains.getD p.2 Dom.empty)) p :=
  rfl

/-- `linCauseMinPair` as a function of the extrema. -/
def linCauseMinOf (mn mx : Option Int) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then mn.map fun a => posLe p.2 (a - 1)
  else if p.1 < 0 then mx.map fun b => negLe p.2 b
  else none

/-- The reference min-cause constructor is the extrema-selector at the
    current domain's extrema. -/
theorem linCauseMinPair_eq_linCauseMinOf (st : State) (p : Int × Nat) :
    linCauseMinPair st p = linCauseMinOf (domMinI (st.domains.getD p.2 Dom.empty))
      (domMaxI (st.domains.getD p.2 Dom.empty)) p :=
  rfl

/-- `linCauseMaxPair` as a function of the extrema. -/
def linCauseMaxOf (mn mx : Option Int) (p : Int × Nat) : Option Literal :=
  if p.1 > 0 then mx.map fun b => negLe p.2 b
  else if p.1 < 0 then mn.map fun a => posLe p.2 (a - 1)
  else none

/-- The reference max-cause constructor is the extrema-selector at the
    current domain's extrema. -/
theorem linCauseMaxPair_eq_linCauseMaxOf (st : State) (p : Int × Nat) :
    linCauseMaxPair st p = linCauseMaxOf (domMinI (st.domains.getD p.2 Dom.empty))
      (domMaxI (st.domains.getD p.2 Dom.empty)) p :=
  rfl

/-! ## 3. The generic contribution fold

`sumMin`/`sumMax` folded over the selectors; the cached sums are
`sumContrib` over cache lookups, and the congruence/instance lemmas
below are the only fold machinery the equivalence needs. -/

/-- The `sumMin` fold shape, parameterized by the per-pair selector. -/
def sumContrib (g : Int × Nat → Option (Nat × Int × Int)) :
    List (Int × Nat) → Option Int
  | [] => none
  | p :: rest =>
      match g p with
      | none => sumContrib g rest
      | some t =>
          match sumContrib g rest with
          | none => some t.2.2
          | some s => some (s + t.2.2)

/-- `sumContrib` respects a pointwise-equal selector on a list. -/
theorem sumContrib_congr {g1 g2 : Int × Nat → Option (Nat × Int × Int)}
    (ps : List (Int × Nat)) (h : ∀ p ∈ ps, g1 p = g2 p) :
    sumContrib g1 ps = sumContrib g2 ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hp := h p (List.mem_cons_self ..)
      have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [sumContrib, hp, hr]

/-- The reference min-sum is the fold over `minContrib`. -/
theorem sumMin_eq_sumContrib (st : State) (ps : List (Int × Nat)) :
    sumMin st ps = sumContrib (fun p => minContrib st p) ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      simp only [sumMin, sumContrib]
      rw [ih]
      rfl

/-- The reference max-sum is the fold over `maxContrib`. -/
theorem sumMax_eq_sumContrib (st : State) (ps : List (Int × Nat)) :
    sumMax st ps = sumContrib (fun p => maxContrib st p) ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      simp only [sumMax, sumContrib]
      rw [ih]
      rfl

/-! ## 4. The cache record and its validity predicate

One entry per constraint slot: the frozen domain snapshot (the key) and
the extrema summary read from it. `Valid` is exactly the task's
validity predicate, conjoined key-currency: the entry's stored
contribution (its summary) is the extrema of its stored domain, and the
stored domain is the slot's CURRENT domain, so the stored contribution
equals the current `minContrib`/`maxContrib` (the `stored_*_eq`
lemmas). -/

/-- One cached slot summary keyed by the domain it was computed from. -/
structure SlotEntry where
  /-- The slot this entry summarizes. -/
  slot : Nat
  /-- The domain snapshot the summary was read from (the cache key). -/
  dom : Domain
  /-- The recorded extrema of `dom`. -/
  summary : SlotSummary
  deriving Repr

/-- Entry validity at a state: the key is the slot's current domain and
    the stored summary is that stored domain's summary. -/
def SlotEntry.Valid (e : SlotEntry) (st : State) : Prop :=
  e.dom = st.domains.getD e.slot Dom.empty ∧ e.summary = summaryOfDomain e.dom

/-- The fresh entry for a slot: snapshot plus one-pass summary. -/
def SlotEntry.ofState (st : State) (s : Nat) : SlotEntry :=
  { slot := s, dom := st.domains.getD s Dom.empty,
    summary := summaryOfDomain (st.domains.getD s Dom.empty) }

/-- A freshly computed entry is valid. -/
theorem SlotEntry.ofState_valid (st : State) (s : Nat) :
    (SlotEntry.ofState st s).Valid st :=
  ⟨rfl, rfl⟩

/-- A finite list of per-slot entries; one entry per constraint slot is
    enough, duplicated slots share their entry (the selectors are
    functions of the extrema and the coefficient only). -/
structure LinCache where
  /-- The stored entries (keyed by `slot`; first match wins). -/
  entries : List SlotEntry
  deriving Repr

/-- The cache is valid at a state when every entry is. -/
def CacheValid (cache : LinCache) (st : State) : Prop :=
  ∀ e ∈ cache.entries, e.Valid st

/-- Keyed lookup: the first entry recorded for the slot. -/
def LinCache.findSlot? (cache : LinCache) (s : Nat) : Option SlotEntry :=
  cache.entries.find? fun e => e.slot == s

/-- Coverage of a slot: some entry is keyed to it. -/
def LinCache.CoversSlot (cache : LinCache) (s : Nat) : Prop :=
  ∃ e ∈ cache.entries, e.slot = s

/-- Coverage of a slot list: every constraint slot is covered. -/
def LinCache.Covers (cache : LinCache) (is : List Nat) : Prop :=
  ∀ s ∈ is, cache.CoversSlot s

/-! ### Validity projections and the stored-contribution spellings -/

/-- The stored minimum is the stored domain's minimum. -/
theorem SlotEntry.summary_min {e : SlotEntry} {st : State} (hv : e.Valid st) :
    e.summary.minI = domMinI e.dom := by
  rw [hv.2, summaryOfDomain_min]

/-- The stored maximum is the stored domain's maximum. -/
theorem SlotEntry.summary_max {e : SlotEntry} {st : State} (hv : e.Valid st) :
    e.summary.maxI = domMaxI e.dom := by
  rw [hv.2, summaryOfDomain_max]

/-- The stored minimum is the CURRENT domain's minimum. -/
theorem SlotEntry.summary_min_current {e : SlotEntry} {st : State}
    (hv : e.Valid st) : e.summary.minI = domMinI (st.domains.getD e.slot Dom.empty) := by
  rw [SlotEntry.summary_min hv, hv.1]

/-- The stored maximum is the CURRENT domain's maximum. -/
theorem SlotEntry.summary_max_current {e : SlotEntry} {st : State}
    (hv : e.Valid st) : e.summary.maxI = domMaxI (st.domains.getD e.slot Dom.empty) := by
  rw [SlotEntry.summary_max hv, hv.1]

/-! ### The entry selectors and their agreement with the reference reads -/

/-- The entry's min-contribution for coefficient `c`. -/
def SlotEntry.contribMin (e : SlotEntry) (c : Int) : Option (Nat × Int × Int) :=
  minContribOf e.summary.minI e.summary.maxI (c, e.slot)

/-- The entry's max-contribution for coefficient `c`. -/
def SlotEntry.contribMax (e : SlotEntry) (c : Int) : Option (Nat × Int × Int) :=
  maxContribOf e.summary.minI e.summary.maxI (c, e.slot)

/-- The entry's min-cause for coefficient `c`. -/
def SlotEntry.causeMin (e : SlotEntry) (c : Int) : Option Literal :=
  linCauseMinOf e.summary.minI e.summary.maxI (c, e.slot)

/-- The entry's max-cause for coefficient `c`. -/
def SlotEntry.causeMax (e : SlotEntry) (c : Int) : Option Literal :=
  linCauseMaxOf e.summary.minI e.summary.maxI (c, e.slot)

/-- **The stored contribution equals the contribution of the stored
    domain** (the task's validity spelling): the entry's min-valuated
    contribution is `minContrib` at the stored extrema. -/
theorem SlotEntry.stored_minContrib_eq_dom {e : SlotEntry} {st : State} {c : Int}
    (hv : e.Valid st) :
    minContribOf e.summary.minI e.summary.maxI (c, e.slot) =
      minContribOf (domMinI e.dom) (domMaxI e.dom) (c, e.slot) := by
  rw [SlotEntry.summary_min hv, SlotEntry.summary_max hv]

/-- The dual for the max-valuated contribution. -/
theorem SlotEntry.stored_maxContrib_eq_dom {e : SlotEntry} {st : State} {c : Int}
    (hv : e.Valid st) :
    maxContribOf e.summary.minI e.summary.maxI (c, e.slot) =
      maxContribOf (domMinI e.dom) (domMaxI e.dom) (c, e.slot) := by
  rw [SlotEntry.summary_min hv, SlotEntry.summary_max hv]

/-- **The stored contribution equals the CURRENT state's
    `minContrib`** for the entry's slot. -/
theorem SlotEntry.stored_minContrib_eq {e : SlotEntry} {st : State} {c : Int}
    (hv : e.Valid st) :
    minContribOf e.summary.minI e.summary.maxI (c, e.slot) =
      minContrib st (c, e.slot) := by
  rw [minContrib_eq_minContribOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1]

/-- The dual for `maxContrib`. -/
theorem SlotEntry.stored_maxContrib_eq {e : SlotEntry} {st : State} {c : Int}
    (hv : e.Valid st) :
    maxContribOf e.summary.minI e.summary.maxI (c, e.slot) =
      maxContrib st (c, e.slot) := by
  rw [maxContrib_eq_maxContribOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1]

/-- The entry's min-contribution selector agrees with the reference
    `minContrib` at any pair `p` on the entry's slot. -/
theorem SlotEntry.contribMin_eq {e : SlotEntry} {st : State} {p : Int × Nat}
    (hv : e.Valid st) (hk : e.slot = p.2) :
    e.contribMin p.1 = minContrib st p := by
  unfold SlotEntry.contribMin
  rw [minContrib_eq_minContribOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1, hk]

/-- The entry's max-contribution selector agrees with the reference
    `maxContrib`. -/
theorem SlotEntry.contribMax_eq {e : SlotEntry} {st : State} {p : Int × Nat}
    (hv : e.Valid st) (hk : e.slot = p.2) :
    e.contribMax p.1 = maxContrib st p := by
  unfold SlotEntry.contribMax
  rw [maxContrib_eq_maxContribOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1, hk]

/-- The entry's min-cause selector agrees with the reference
    `linCauseMinPair`. -/
theorem SlotEntry.causeMin_eq {e : SlotEntry} {st : State} {p : Int × Nat}
    (hv : e.Valid st) (hk : e.slot = p.2) :
    e.causeMin p.1 = linCauseMinPair st p := by
  unfold SlotEntry.causeMin
  rw [linCauseMinPair_eq_linCauseMinOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1, hk]

/-- The entry's max-cause selector agrees with the reference
    `linCauseMaxPair`. -/
theorem SlotEntry.causeMax_eq {e : SlotEntry} {st : State} {p : Int × Nat}
    (hv : e.Valid st) (hk : e.slot = p.2) :
    e.causeMax p.1 = linCauseMaxPair st p := by
  unfold SlotEntry.causeMax
  rw [linCauseMaxPair_eq_linCauseMaxOf, SlotEntry.summary_min hv,
    SlotEntry.summary_max hv, hv.1, hk]

/-! ### Lookup lemmas -/

/-- A found entry is a member of the entry list. -/
theorem LinCache.findSlot?_mem {cache : LinCache} {s : Nat} {e : SlotEntry}
    (h : cache.findSlot? s = some e) : e ∈ cache.entries := by
  have h' : cache.entries.find? (fun x => x.slot == s) = some e := h
  exact List.mem_of_find?_eq_some h'

/-- A found entry is keyed to the queried slot. -/
theorem LinCache.findSlot?_key {cache : LinCache} {s : Nat} {e : SlotEntry}
    (h : cache.findSlot? s = some e) : e.slot = s := by
  have h' : cache.entries.find? (fun x => x.slot == s) = some e := h
  have hk := List.find?_some h'
  exact beq_iff_eq.mp hk

/-- A list member keyed to `s` is found by the slot lookup. -/
private theorem find?_exists_of_mem_slot {l : List SlotEntry} {s : Nat}
    {e : SlotEntry} (he : e ∈ l) (hke : e.slot = s) :
    ∃ e', l.find? (fun x => x.slot == s) = some e' := by
  induction l with
  | nil => cases he
  | cons x xs ih =>
      cases hc : (x.slot == s) with
      | true => exact ⟨x, by simp [List.find?, hc]⟩
      | false =>
          rcases List.mem_cons.mp he with rfl | he
          · rw [hke] at hc
            rw [beq_iff_eq.mpr rfl] at hc
            cases hc
          · obtain ⟨e', he'⟩ := ih he
            exact ⟨e', by simp [List.find?, hc, he']⟩

/-- A covered slot has a found entry. -/
theorem LinCache.findSlot?_exists {cache : LinCache} {s : Nat}
    (hcov : cache.CoversSlot s) : ∃ e, cache.findSlot? s = some e := by
  obtain ⟨e0, he0, hs0⟩ := hcov
  exact find?_exists_of_mem_slot he0 hs0

/-! ### The cache-level selectors and their agreement lemmas -/

/-- Cached min-contribution for a pair. -/
def LinCache.minAt (cache : LinCache) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  (cache.findSlot? p.2).bind fun e => e.contribMin p.1

/-- Cached max-contribution for a pair. -/
def LinCache.maxAt (cache : LinCache) (p : Int × Nat) :
    Option (Nat × Int × Int) :=
  (cache.findSlot? p.2).bind fun e => e.contribMax p.1

/-- Cached min-cause for a pair. -/
def LinCache.causeMinAt (cache : LinCache) (p : Int × Nat) : Option Literal :=
  (cache.findSlot? p.2).bind fun e => e.causeMin p.1

/-- Cached max-cause for a pair. -/
def LinCache.causeMaxAt (cache : LinCache) (p : Int × Nat) : Option Literal :=
  (cache.findSlot? p.2).bind fun e => e.causeMax p.1

/-- The cached min-contribution equals the reference `minContrib` when
    the cache is valid and the pair's slot is covered. -/
theorem LinCache.minAt_eq {cache : LinCache} {st : State} {p : Int × Nat}
    (hv : CacheValid cache st) (hcov : cache.CoversSlot p.2) :
    cache.minAt p = minContrib st p := by
  obtain ⟨e, he⟩ := cache.findSlot?_exists hcov
  unfold LinCache.minAt
  rw [he]
  exact SlotEntry.contribMin_eq (hv e (cache.findSlot?_mem he))
    (LinCache.findSlot?_key he)

/-- The cached max-contribution equals the reference `maxContrib`. -/
theorem LinCache.maxAt_eq {cache : LinCache} {st : State} {p : Int × Nat}
    (hv : CacheValid cache st) (hcov : cache.CoversSlot p.2) :
    cache.maxAt p = maxContrib st p := by
  obtain ⟨e, he⟩ := cache.findSlot?_exists hcov
  unfold LinCache.maxAt
  rw [he]
  exact SlotEntry.contribMax_eq (hv e (cache.findSlot?_mem he))
    (LinCache.findSlot?_key he)

/-- The cached min-cause equals the reference `linCauseMinPair`. -/
theorem LinCache.causeMinAt_eq {cache : LinCache} {st : State} {p : Int × Nat}
    (hv : CacheValid cache st) (hcov : cache.CoversSlot p.2) :
    cache.causeMinAt p = linCauseMinPair st p := by
  obtain ⟨e, he⟩ := cache.findSlot?_exists hcov
  unfold LinCache.causeMinAt
  rw [he]
  exact SlotEntry.causeMin_eq (hv e (cache.findSlot?_mem he))
    (LinCache.findSlot?_key he)

/-- The cached max-cause equals the reference `linCauseMaxPair`. -/
theorem LinCache.causeMaxAt_eq {cache : LinCache} {st : State} {p : Int × Nat}
    (hv : CacheValid cache st) (hcov : cache.CoversSlot p.2) :
    cache.causeMaxAt p = linCauseMaxPair st p := by
  obtain ⟨e, he⟩ := cache.findSlot?_exists hcov
  unfold LinCache.causeMaxAt
  rw [he]
  exact SlotEntry.causeMax_eq (hv e (cache.findSlot?_mem he))
    (LinCache.findSlot?_key he)

/-! ### Cache-level sums, cause lists, and the completeness guard -/

/-- The cached min-sum fold. -/
def LinCache.sumMinC (cache : LinCache) (ps : List (Int × Nat)) : Option Int :=
  sumContrib cache.minAt ps

/-- The cached max-sum fold. -/
def LinCache.sumMaxC (cache : LinCache) (ps : List (Int × Nat)) : Option Int :=
  sumContrib cache.maxAt ps

/-- The cached min-cause list. -/
def LinCache.causesMin (cache : LinCache) (rest : List (Int × Nat)) : Clause :=
  rest.filterMap cache.causeMinAt

/-- The cached max-cause list. -/
def LinCache.causesMax (cache : LinCache) (rest : List (Int × Nat)) : Clause :=
  rest.filterMap cache.causeMaxAt

/-- The cached min-sum equals the reference `sumMin`. -/
theorem LinCache.sumMinC_eq {cache : LinCache} {st : State}
    {ps : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ ps, cache.CoversSlot p.2) :
    cache.sumMinC ps = sumMin st ps := by
  unfold LinCache.sumMinC
  rw [sumMin_eq_sumContrib]
  exact sumContrib_congr ps (fun p hp => cache.minAt_eq hv (hcov p hp))

/-- The cached max-sum equals the reference `sumMax`. -/
theorem LinCache.sumMaxC_eq {cache : LinCache} {st : State}
    {ps : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ ps, cache.CoversSlot p.2) :
    cache.sumMaxC ps = sumMax st ps := by
  unfold LinCache.sumMaxC
  rw [sumMax_eq_sumContrib]
  exact sumContrib_congr ps (fun p hp => cache.maxAt_eq hv (hcov p hp))

/-- The cached min-cause list equals the reference `linCausesMin`. -/
theorem LinCache.causesMin_eq {cache : LinCache} {st : State}
    {rest : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    cache.causesMin rest = linCausesMin st rest := by
  unfold LinCache.causesMin linCausesMin
  exact lin2_filterMap_local fun p hp => cache.causeMinAt_eq hv (hcov p hp)

/-- The cached max-cause list equals the reference `linCausesMax`. -/
theorem LinCache.causesMax_eq {cache : LinCache} {st : State}
    {rest : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    cache.causesMax rest = linCausesMax st rest := by
  unfold LinCache.causesMax linCausesMax
  exact lin2_filterMap_local fun p hp => cache.causeMaxAt_eq hv (hcov p hp)

/-- The cached completeness guard equals the reference guard. -/
theorem LinCache.all_minAt_eq {cache : LinCache} {st : State}
    {rest : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    rest.all (fun p => (cache.minAt p).isSome) =
      rest.all (fun p => (minContrib st p).isSome) := by
  induction rest with
  | nil => rfl
  | cons p ps ih =>
      have hp := cache.minAt_eq hv (hcov p (List.mem_cons_self ..))
      have hr := ih (fun q hq => hcov q (List.mem_cons_of_mem _ hq))
      simp only [List.all_cons, hp, hr]

/-! ## 5. The cached kernels

The deduction kernels mirror `linDeduceLe`/`linDeduceEq` arm-by-arm
with the cache selectors in place of the domain reads (the `narrow`
calls still read the narrowed slot's CURRENT domain — that is the
storage the cache does not substitute). The `linSweep` fold is NOT
mirrored: it is reused verbatim from `Fam/Lin.lean` through
`linSweep_local`, so the reference loop structure (first-event exit,
`others` by position, duplicated-slot handling) is identical by
construction. -/

/-- `linGenArmHiMin` with cached causes. -/
def linGenArmHiMinC (cache : LinCache) (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowHi st m ((b - lr) / c)
      ([posLe m ((b - lr) / c)] ++ cache.causesMin rest)
  | none => .stable

/-- `linGenArmLoMin` with cached causes. -/
def linGenArmLoMinC (cache : LinCache) (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowLo st m (-((b - lr) / (-c)))
      ([negLe m (-((b - lr) / (-c)) - 1)] ++ cache.causesMin rest)
  | none => .stable

/-- `linGenArmLoMax` with cached causes. -/
def linGenArmLoMaxC (cache : LinCache) (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowLo st m (-((hr - b) / c))
      ([negLe m (-((hr - b) / c) - 1)] ++ cache.causesMax rest)
  | none => .stable

/-- `linGenArmHiMax` with cached causes. -/
def linGenArmHiMaxC (cache : LinCache) (st : State) (m : Nat) (b c : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowHi st m ((hr - b) / (-c))
      ([posLe m ((hr - b) / (-c))] ++ cache.causesMax rest)
  | none => .stable

/-- `linEqArmHiMin` with cached causes. -/
def linEqArmHiMinC (cache : LinCache) (st : State) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowHi st m (b - lr)
      ([posLe m (b - lr)] ++ cache.causesMin rest)
  | none => .stable

/-- `linEqArmLoMax` with cached causes. -/
def linEqArmLoMaxC (cache : LinCache) (st : State) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowLo st m (b - hr)
      ([negLe m (b - hr - 1)] ++ cache.causesMax rest)
  | none => .stable

/-- `linEqArmLoMin` with cached causes. -/
def linEqArmLoMinC (cache : LinCache) (st : State) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some lr => narrowLo st m (lr - b)
      ([negLe m (lr - b - 1)] ++ cache.causesMin rest)
  | none => .stable

/-- `linEqArmHiMax` with cached causes. -/
def linEqArmHiMaxC (cache : LinCache) (st : State) (m : Nat) (b : Int)
    (rest : List (Int × Nat)) : Option Int → PropagationResult
  | some hr => narrowHi st m (hr - b)
      ([posLe m (hr - b)] ++ cache.causesMax rest)
  | none => .stable

/-- The cached `int_lin_le` deduction kernel. -/
def linDeduceLeC (cache : LinCache) (st : State) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : PropagationResult :=
  if rest.all (fun p => (cache.minAt p).isSome) then
    if c = 1 then
      match cache.sumMinC rest with
      | some lr =>
          narrowHi st m (b - lr) ([posLe m (b - lr)] ++ cache.causesMin rest)
      | none => .stable
    else if c = -1 then
      match cache.sumMinC rest with
      | some lr =>
          narrowLo st m (lr - b) ([negLe m (lr - b - 1)] ++ cache.causesMin rest)
      | none => .stable
    else if c > 0 then
      match cache.sumMinC rest with
      | some lr => linGenArmHiMinC cache st m b c rest lr
      | none => .stable
    else if c < 0 then
      match cache.sumMinC rest with
      | some lr => linGenArmLoMinC cache st m b c rest lr
      | none => .stable
    else .stable
  else .stable

/-- The cached `int_lin_eq` deduction kernel. -/
def linDeduceEqC (cache : LinCache) (st : State) (b : Int) (m : Nat) (c : Int)
    (rest : List (Int × Nat)) : PropagationResult :=
  if rest.all (fun p => (cache.minAt p).isSome) then
    if c = 1 then
      firstEvent
        [ linEqArmHiMinC cache st m b rest (cache.sumMinC rest)
        , linEqArmLoMaxC cache st m b rest (cache.sumMaxC rest) ]
    else if c = -1 then
      firstEvent
        [ linEqArmLoMinC cache st m b rest (cache.sumMinC rest)
        , linEqArmHiMaxC cache st m b rest (cache.sumMaxC rest) ]
    else if c > 0 then
      firstEvent
        [ linGenArmHiMinC cache st m b c rest (cache.sumMinC rest)
        , linGenArmLoMaxC cache st m b c rest (cache.sumMaxC rest) ]
    else if c < 0 then
      firstEvent
        [ linGenArmLoMinC cache st m b c rest (cache.sumMinC rest)
        , linGenArmHiMaxC cache st m b c rest (cache.sumMaxC rest) ]
    else .stable
  else .stable

/-! ### The arm equivalences -/

/-- `linGenArmHiMinC` agrees with the reference arm. -/
theorem linGenArmHiMinC_eq {cache : LinCache} {st : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linGenArmHiMinC cache st m b c rest o = linGenArmHiMin st m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linGenArmHiMinC linGenArmHiMin
      rw [cache.causesMin_eq hv hcov]

/-- `linGenArmLoMinC` agrees with the reference arm. -/
theorem linGenArmLoMinC_eq {cache : LinCache} {st : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linGenArmLoMinC cache st m b c rest o = linGenArmLoMin st m b c rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linGenArmLoMinC linGenArmLoMin
      rw [cache.causesMin_eq hv hcov]

/-- `linGenArmLoMaxC` agrees with the reference arm. -/
theorem linGenArmLoMaxC_eq {cache : LinCache} {st : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linGenArmLoMaxC cache st m b c rest o = linGenArmLoMax st m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linGenArmLoMaxC linGenArmLoMax
      rw [cache.causesMax_eq hv hcov]

/-- `linGenArmHiMaxC` agrees with the reference arm. -/
theorem linGenArmHiMaxC_eq {cache : LinCache} {st : State} {m : Nat} {b c : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linGenArmHiMaxC cache st m b c rest o = linGenArmHiMax st m b c rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linGenArmHiMaxC linGenArmHiMax
      rw [cache.causesMax_eq hv hcov]

/-- `linEqArmHiMinC` agrees with the reference arm. -/
theorem linEqArmHiMinC_eq {cache : LinCache} {st : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linEqArmHiMinC cache st m b rest o = linEqArmHiMin st m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linEqArmHiMinC linEqArmHiMin
      rw [cache.causesMin_eq hv hcov]

/-- `linEqArmLoMaxC` agrees with the reference arm. -/
theorem linEqArmLoMaxC_eq {cache : LinCache} {st : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linEqArmLoMaxC cache st m b rest o = linEqArmLoMax st m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linEqArmLoMaxC linEqArmLoMax
      rw [cache.causesMax_eq hv hcov]

/-- `linEqArmLoMinC` agrees with the reference arm. -/
theorem linEqArmLoMinC_eq {cache : LinCache} {st : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linEqArmLoMinC cache st m b rest o = linEqArmLoMin st m b rest o := by
  cases o with
  | none => rfl
  | some lr =>
      unfold linEqArmLoMinC linEqArmLoMin
      rw [cache.causesMin_eq hv hcov]

/-- `linEqArmHiMaxC` agrees with the reference arm. -/
theorem linEqArmHiMaxC_eq {cache : LinCache} {st : State} {m : Nat} {b : Int}
    {rest : List (Int × Nat)} (o : Option Int) (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linEqArmHiMaxC cache st m b rest o = linEqArmHiMax st m b rest o := by
  cases o with
  | none => rfl
  | some hr =>
      unfold linEqArmHiMaxC linEqArmHiMax
      rw [cache.causesMax_eq hv hcov]

/-! ### The kernel equivalences -/

/-- **The cached `linLe` kernel is the reference kernel** at validity and
    coverage. -/
theorem linDeduceLeC_eq {cache : LinCache} {st : State} {b : Int} {m : Nat}
    {c : Int} {rest : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linDeduceLeC cache st b m c rest = linDeduceLe st b m c rest := by
  have hall := cache.all_minAt_eq hv hcov
  have hsum := cache.sumMinC_eq hv hcov
  have hcm := cache.causesMin_eq hv hcov
  have hhi : ∀ o, linGenArmHiMinC cache st m b c rest o =
      linGenArmHiMin st m b c rest o := fun o => linGenArmHiMinC_eq o hv hcov
  have hlo : ∀ o, linGenArmLoMinC cache st m b c rest o =
      linGenArmLoMin st m b c rest o := fun o => linGenArmLoMinC_eq o hv hcov
  unfold linDeduceLeC linDeduceLe
  rw [hall, hsum, hcm]
  simp only [hhi, hlo]
  rfl

/-- **The cached `linEq` kernel is the reference kernel** at validity and
    coverage. -/
theorem linDeduceEqC_eq {cache : LinCache} {st : State} {b : Int} {m : Nat}
    {c : Int} {rest : List (Int × Nat)} (hv : CacheValid cache st)
    (hcov : ∀ p ∈ rest, cache.CoversSlot p.2) :
    linDeduceEqC cache st b m c rest = linDeduceEq st b m c rest := by
  have hall := cache.all_minAt_eq hv hcov
  have hsum := cache.sumMinC_eq hv hcov
  have hmax := cache.sumMaxC_eq hv hcov
  have hcm := cache.causesMin_eq hv hcov
  have hcx := cache.causesMax_eq hv hcov
  have h1 : ∀ o, linEqArmHiMinC cache st m b rest o =
      linEqArmHiMin st m b rest o := fun o => linEqArmHiMinC_eq o hv hcov
  have h2 : ∀ o, linEqArmLoMaxC cache st m b rest o =
      linEqArmLoMax st m b rest o := fun o => linEqArmLoMaxC_eq o hv hcov
  have h3 : ∀ o, linEqArmLoMinC cache st m b rest o =
      linEqArmLoMin st m b rest o := fun o => linEqArmLoMinC_eq o hv hcov
  have h4 : ∀ o, linEqArmHiMaxC cache st m b rest o =
      linEqArmHiMax st m b rest o := fun o => linEqArmHiMaxC_eq o hv hcov
  have g1 : ∀ o, linGenArmHiMinC cache st m b c rest o =
      linGenArmHiMin st m b c rest o := fun o => linGenArmHiMinC_eq o hv hcov
  have g2 : ∀ o, linGenArmLoMaxC cache st m b c rest o =
      linGenArmLoMax st m b c rest o := fun o => linGenArmLoMaxC_eq o hv hcov
  have g3 : ∀ o, linGenArmLoMinC cache st m b c rest o =
      linGenArmLoMin st m b c rest o := fun o => linGenArmLoMinC_eq o hv hcov
  have g4 : ∀ o, linGenArmHiMaxC cache st m b c rest o =
      linGenArmHiMax st m b c rest o := fun o => linGenArmHiMaxC_eq o hv hcov
  unfold linDeduceEqC linDeduceEq
  rw [hall, hsum, hmax]
  simp only [h1, h2, h3, h4, g1, g2, g3, g4]

/-! ### The cached runs and the equivalence theorem -/

/-- The cached `int_lin_le` propagator: the reference sweep over the
    cached deduction kernel. -/
def propLinLe2Cached (cache : LinCache) (st : State) (coeffs : List Int)
    (is : List Nat) (b : Int) : PropagationResult :=
  match coeffs.zip is with
  | [] => .stable
  | ps => linSweep coeffs is (linDeduceLeC cache st b) (ps.zipIdx) 0

/-- The cached `int_lin_eq` propagator. -/
def propLinEq2Cached (cache : LinCache) (st : State) (coeffs : List Int)
    (is : List Nat) (b : Int) : PropagationResult :=
  match coeffs.zip is with
  | [] => .stable
  | ps => linSweep coeffs is (linDeduceEqC cache st b) (ps.zipIdx) 0

/-- **THE CACHED-RUN EQUIVALENCE (linLe)**: at cache validity and slot
    coverage the cached run equals the certified `propLinLe2` — the
    sweep transport through `linSweep_local` consumes only the kernel
    equivalence. -/
theorem propLinLe2Cached_eq {cache : LinCache} {st : State}
    {coeffs : List Int} {is : List Nat} {b : Int} (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s) :
    propLinLe2Cached cache st coeffs is b = propLinLe2 st coeffs is b := by
  unfold propLinLe2Cached propLinLe2
  cases hz : coeffs.zip is with
  | nil => rfl
  | cons p ps =>
      show linSweep coeffs is (linDeduceLeC cache st b) ((p :: ps).zipIdx) 0 =
           linSweep coeffs is (linDeduceLe st b) ((p :: ps).zipIdx) 0
      refine linSweep_local ((p :: ps).zipIdx) 0 ?_
      intro q hq rest hrest
      exact linDeduceLeC_eq hv (fun r hr => hcov r.2 (mem_zip_snd (hrest r hr)))

/-- **THE CACHED-RUN EQUIVALENCE (linEq)**. -/
theorem propLinEq2Cached_eq {cache : LinCache} {st : State}
    {coeffs : List Int} {is : List Nat} {b : Int} (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s) :
    propLinEq2Cached cache st coeffs is b = propLinEq2 st coeffs is b := by
  unfold propLinEq2Cached propLinEq2
  cases hz : coeffs.zip is with
  | nil => rfl
  | cons p ps =>
      show linSweep coeffs is (linDeduceEqC cache st b) ((p :: ps).zipIdx) 0 =
           linSweep coeffs is (linDeduceEq st b) ((p :: ps).zipIdx) 0
      refine linSweep_local ((p :: ps).zipIdx) 0 ?_
      intro q hq rest hrest
      exact linDeduceEqC_eq hv (fun r hr => hcov r.2 (mem_zip_snd (hrest r hr)))

/-! ### Transfer of the certified consumer obligations -/

/-- The complete safe triple for the cached `linLe` run. -/
theorem propLinLe2Cached_safe (cache : LinCache) (st : State)
    (coeffs : List Int) (is : List Nat) (b : Int)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s) :
    (∀ l r, propLinLe2Cached cache st coeffs is b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinLe2Cached cache st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinLe2Cached cache st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linLe coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  rw [propLinLe2Cached_eq hv hcov]
  exact propLinLe2_safe st coeffs is b hlen

/-- The complete safe triple for the cached `linEq` run. -/
theorem propLinEq2Cached_safe (cache : LinCache) (st : State)
    (coeffs : List Int) (is : List Nat) (b : Int)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s) :
    (∀ l r, propLinEq2Cached cache st coeffs is b = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propLinEq2Cached cache st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a → False) ∧
    (∀ c, propLinEq2Cached cache st coeffs is b = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.linEq coeffs is b).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  rw [propLinEq2Cached_eq hv hcov]
  exact propLinEq2_safe st coeffs is b hlen

/-- State-free reason validity transfers to the cached `linLe` run. -/
theorem propLinLe2Cached_reason_valid {problem : Problem DomConstraint Unit}
    {cache : LinCache} {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s)
    (hrun : propLinLe2Cached cache st coeffs is b = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rw [propLinLe2Cached_eq hv hcov] at hrun
  exact propLinLe2_reason_valid hprob hlen hrun

/-- State-free reason validity transfers to the cached `linEq` run. -/
theorem propLinEq2Cached_reason_valid {problem : Problem DomConstraint Unit}
    {cache : LinCache} {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.linEq coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s)
    (hrun : propLinEq2Cached cache st coeffs is b = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  rw [propLinEq2Cached_eq hv hcov] at hrun
  exact propLinEq2_reason_valid hprob hlen hrun

/-- The conflict entitlement transfers to the cached `linLe` run. -/
theorem propLinLe2Cached_entitled {problem : Problem DomConstraint Unit}
    {cache : LinCache} {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {cc : Clause}
    (hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s)
    (hrun : propLinLe2Cached cache st coeffs is b = .conflict cc)
    (a : Assignment) (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rw [propLinLe2Cached_eq hv hcov] at hrun
  exact propLinLe2_entitled hprob hlen hrun a ha

/-- The conflict entitlement transfers to the cached `linEq` run. -/
theorem propLinEq2Cached_entitled {problem : Problem DomConstraint Unit}
    {cache : LinCache} {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {cc : Clause}
    (hprob : DomConstraint.linEq coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s)
    (hrun : propLinEq2Cached cache st coeffs is b = .conflict cc)
    (a : Assignment) (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ cc, l.eval a = some true := by
  rw [propLinEq2Cached_eq hv hcov] at hrun
  exact propLinEq2_entitled hprob hlen hrun a ha

/-! ## 6. Update operations and their validity/coverage laws

The runtime contract the E2 ledger proposes: the scheduler owns one
`LinCache` per linear propagator (sitting next to the E1 queue records);
on every frame transition it recomputes the entries of the slots the
transition touched (`touch` per changed slot, `touchSlots` for a batch —
a restoration), or drops entries conservatively (`invalidateSlot`), or
rebuilds from scratch (`rebuild`). The laws below are exactly the
invariant preservation the threaded scheduler state needs. -/

/-- Fresh cache for a slot list: one snapshot+summary entry per slot. -/
def LinCache.rebuild (st : State) (is : List Nat) : LinCache :=
  { entries := is.map (SlotEntry.ofState st) }

/-- A fresh cache is valid. -/
theorem LinCache.rebuild_valid (st : State) (is : List Nat) :
    CacheValid (LinCache.rebuild st is) st := by
  intro e he
  rw [LinCache.rebuild, List.mem_map] at he
  obtain ⟨s, -, rfl⟩ := he
  exact SlotEntry.ofState_valid st s

/-- A fresh cache covers the slot list it was built from. -/
theorem LinCache.rebuild_covers (st : State) (is : List Nat) :
    (LinCache.rebuild st is).Covers is := by
  intro s hs
  refine ⟨SlotEntry.ofState st s, ?_, rfl⟩
  rw [LinCache.rebuild, List.mem_map]
  exact ⟨s, hs, rfl⟩

/-- The positional refinement bridge for an array/slot-indexed runtime
    table: the aligned entry of a rebuilt cache is the slot's fresh
    entry. -/
theorem LinCache.rebuild_getElem? (st : State) (is : List Nat) (i : Nat) :
    (LinCache.rebuild st is).entries[i]? =
      (is[i]?).map (SlotEntry.ofState st) := by
  simp [LinCache.rebuild, List.getElem?_map]

/-- The key of an aligned position: a found entry of a rebuilt cache is
    the fresh entry of the position's slot. -/
theorem LinCache.rebuild_get?_key {st : State} {is : List Nat} {i : Nat}
    {e : SlotEntry} (h : (LinCache.rebuild st is).entries[i]? = some e) :
    ∃ s, is[i]? = some s ∧ e = SlotEntry.ofState st s := by
  have h1 := LinCache.rebuild_getElem? st is i
  rw [h] at h1
  cases hi : is[i]? with
  | none => rw [hi] at h1; cases h1
  | some s =>
      rw [hi] at h1
      exact ⟨s, rfl, Option.some.inj h1⟩

/-- Per-slot recomputation after a domain change at slot `s`: the
    entries of slot `s` are rebuilt from the new state, the others are
    kept. -/
def LinCache.touch (cache : LinCache) (st : State) (s : Nat) : LinCache :=
  { entries := cache.entries.map fun e =>
      if e.slot == s then SlotEntry.ofState st s else e }

/-- **The touch law**: if the state change is confined to slot `s`
    (other slots' domains unchanged) and the cache was valid at the old
    state, the touched cache is valid at the new state. -/
theorem LinCache.touch_valid {cache : LinCache} {st st' : State} {s : Nat}
    (hv : CacheValid cache st)
    (hframe : ∀ e ∈ cache.entries, e.slot ≠ s →
      st'.domains.getD e.slot Dom.empty = st.domains.getD e.slot Dom.empty) :
    CacheValid (cache.touch st' s) st' := by
  intro e he
  rw [LinCache.touch, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  by_cases hs : e0.slot == s
  · rw [if_pos hs]
    exact SlotEntry.ofState_valid st' s
  · rw [if_neg hs]
    have hne : e0.slot ≠ s := fun h => hs (beq_iff_eq.mpr h)
    have hv0 : e0.Valid st := hv e0 he0
    unfold SlotEntry.Valid at hv0 ⊢
    exact ⟨hv0.1.trans (hframe e0 he0 hne).symm, hv0.2⟩

/-- Touch preserves coverage (slot numbers survive the map). -/
theorem LinCache.touch_covers {cache : LinCache} {st : State} {s : Nat}
    {s' : Nat} (hcov : cache.CoversSlot s') :
    (cache.touch st s).CoversSlot s' := by
  obtain ⟨e, he, hk⟩ := hcov
  refine ⟨if e.slot == s then SlotEntry.ofState st s else e, ?_, ?_⟩
  · rw [LinCache.touch, List.mem_map]
    exact ⟨e, he, rfl⟩
  · by_cases hs : e.slot == s
    · rw [if_pos hs]
      show s = s'
      exact (beq_iff_eq.mp hs).symm.trans hk
    · rw [if_neg hs]
      exact hk

/-- Batch update for a frame transition that changed several slots (a
    restoration/backjump): every entry of a slot in `ss` is rebuilt from
    the new state, the others are kept. -/
def LinCache.touchSlots (cache : LinCache) (st : State) (ss : List Nat) : LinCache :=
  { entries := cache.entries.map fun e =>
      if e.slot ∈ ss then SlotEntry.ofState st e.slot else e }

/-- **The batch-touch law**: validity at the new state needs the frame
    condition only for the entries whose slots are NOT in `ss` (those
    are the untouched ones). -/
theorem LinCache.touchSlots_valid {cache : LinCache} {st st' : State}
    {ss : List Nat} (hv : CacheValid cache st)
    (hframe : ∀ e ∈ cache.entries, e.slot ∉ ss →
      st'.domains.getD e.slot Dom.empty = st.domains.getD e.slot Dom.empty) :
    CacheValid (cache.touchSlots st' ss) st' := by
  intro e he
  rw [LinCache.touchSlots, List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  by_cases hs : e0.slot ∈ ss
  · rw [if_pos hs]
    exact SlotEntry.ofState_valid st' e0.slot
  · rw [if_neg hs]
    have hv0 : e0.Valid st := hv e0 he0
    unfold SlotEntry.Valid at hv0 ⊢
    exact ⟨hv0.1.trans (hframe e0 he0 hs).symm, hv0.2⟩

/-- Batch touch preserves coverage. -/
theorem LinCache.touchSlots_covers {cache : LinCache} {st : State}
    {ss : List Nat} {s' : Nat} (hcov : cache.CoversSlot s') :
    (cache.touchSlots st ss).CoversSlot s' := by
  obtain ⟨e, he, hk⟩ := hcov
  by_cases hs : e.slot ∈ ss
  · refine ⟨SlotEntry.ofState st e.slot, ?_, ?_⟩
    · rw [LinCache.touchSlots, List.mem_map]
      exact ⟨e, he, by rw [if_pos hs]⟩
    · show e.slot = s'
      exact hk
  · refine ⟨e, ?_, hk⟩
    rw [LinCache.touchSlots, List.mem_map]
    exact ⟨e, he, by rw [if_neg hs]⟩

/-- Conservative invalidation on restoration: drop every entry of the
    restored slot (coverage of the slot is lost and must be re-established
    by a later `touchSlots`/`rebuild` before the cached run is used). -/
def LinCache.invalidateSlot (cache : LinCache) (s : Nat) : LinCache :=
  { entries := cache.entries.filter fun e => !(e.slot == s) }

/-- Invalidation preserves validity (the kept entries are a subset). -/
theorem LinCache.invalidateSlot_valid {cache : LinCache} {st : State} {s : Nat}
    (hv : CacheValid cache st) : CacheValid (cache.invalidateSlot s) st := by
  intro e he
  obtain ⟨he0, -⟩ := List.mem_filter.mp he
  exact hv e he0

/-- ...and coverage of every OTHER slot. -/
theorem LinCache.invalidateSlot_covers_other {cache : LinCache} {s : Nat}
    {s' : Nat} (hne : s' ≠ s) (hcov : cache.CoversSlot s') :
    (cache.invalidateSlot s).CoversSlot s' := by
  obtain ⟨e, he, hk⟩ := hcov
  refine ⟨e, ?_, hk⟩
  rw [LinCache.invalidateSlot, List.mem_filter]
  refine ⟨he, ?_⟩
  cases hc : (e.slot == s) with
  | false => rfl
  | true => exact absurd (hk.symm.trans (beq_iff_eq.mp hc)) hne

/-! ## 7. The stale-reason obligation

`CacheValid` makes the cached run PROVABLY the reference run, so the
whole certified package transfers (section 5). But the reason `E1`-style
reuse wants is weaker: replay a recorded outcome whose data was
computed at an earlier state. A correct cached bound is NOT enough then:
the emitted literal's *reason* was fabricated at the historical state
(its pins are the historical domain-bound negations), so the outcome is
usable only when the reason data still entails the emitted literal at
the state where the reason is consumed.

`StaleReasonOK` below is that obligation as a Prop bundle. It records

* the problem and compiled-shape side conditions (`hprob`, `hlen`),
* `covers` — the emitted clause's pins are backed by entries,
* `hist_valid`/`hist_emits` — the recorded data was correct at the
  historical state and the historical run emits this explained outcome
  (so `Reason.Valid` holds OF THE HISTORICAL CLAUSE),
* `head_entailed` — **the piece a stale cache can lose**: the emitted
  literal is a consequence of the constraint at the CURRENT box,
* `reason_entailed` — the clause itself is entailed by the constraint
  (the state-free half of the reason; under `hist_valid` it transfers
  from the reference run, `propLinLe2Cached_reason_valid`).

`staleReasonOK_of_valid` inhabits the schema whenever `st = stHist` and
the cache is valid — so the schema is not vacuous — and the
machine-checked witness below shows that with a genuinely stale entry
the historical fields all hold while `head_entailed` FAILS: the cached
run then emits a literal that is not entailed at the current state.
The missing piece for the genuinely stale route is the monotonicity of
min-contribution sums under box inclusion (the `StaleBoundOK`
certificate, defined but not yet shown to imply `head_entailed`; no
proof is claimed here). -/

/-- **THE STALE-REASON OBLIGATION** (PLAN §6 E2): the certificate a
cached explained `linLe` outcome needs beyond "the bound is right". -/
structure StaleReasonOK (problem : Problem DomConstraint Unit) (cache : LinCache)
    (stHist st : State) (coeffs : List Int) (is : List Nat) (b : Int)
    (l : Literal) (r : Reason) : Prop where
  /-- The constraint belongs to the problem whose solutions are the
      consumer of the reason. -/
  hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints
  /-- The compiled shape (equal coefficient/slot lengths). -/
  hlen : coeffs.length = is.length
  /-- Every constraint slot has a cached entry (the clause's pins are
      backed by cache data). -/
  covers : ∀ s ∈ is, cache.CoversSlot s
  /-- The recorded data was correct at the historical state. -/
  hist_valid : CacheValid cache stHist
  /-- The historical run emits exactly this explained outcome (the
      reason data entails the literal at the historical state). -/
  hist_emits : propLinLe2Cached cache stHist coeffs is b = .implied l r
  /-- **The stale hazard**: the emitted literal is entailed by the
      constraint at every assignment fitting the CURRENT box.
      `CacheValid st` discharges it unconditionally
      (`staleReasonOK_of_valid`); the genuinely stale discharge needs
      `StaleBoundOK` plus the (unproved) monotonicity lemma. -/
  head_entailed : ∀ a, Core.Assignment.Fits st.domains a →
    (DomConstraint.linLe coeffs is b).SatisfiedBy a → l.eval a = some true
  /-- The reason clause is entailed by the constraint at every solution
      (the state-free half; the pins of the clause carry their own
      arithmetic, so this half is not the stale-sensitive one). -/
  reason_entailed : r.clause.EntailedBy problem DomConstraint.SatisfiedBy

/-- The monotonicity certificate the stale route would consume: every
    entry is valid at the historical state and each slot's CURRENT
    domain is included in the cached domain. Stock case: domains only
    shrink between two scheduler steps. The missing step is the
    monotonicity lemma `StaleBoundOK → head_entailed` (min-contribution
    sums are antitone in the box), which is NOT proved here. -/
def StaleBoundOK (cache : LinCache) (stHist st : State) : Prop :=
  ∀ e ∈ cache.entries, e.Valid stHist ∧
    ∀ v ∈ st.domains.getD e.slot Dom.empty, v ∈ e.dom

/-- **The strong route inhabits the schema**: at cache validity the
    obligation's fields are all discharged (the historical state is the
    current state). -/
theorem staleReasonOK_of_valid {problem : Problem DomConstraint Unit}
    {cache : LinCache} {st : State} {coeffs : List Int} {is : List Nat}
    {b : Int} {l : Literal} {r : Reason}
    (hprob : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) (hv : CacheValid cache st)
    (hcov : ∀ s ∈ is, cache.CoversSlot s)
    (hrun : propLinLe2Cached cache st coeffs is b = .implied l r) :
    StaleReasonOK problem cache st st coeffs is b l r := by
  have hrun' : propLinLe2 st coeffs is b = .implied l r :=
    (propLinLe2Cached_eq hv hcov).symm.trans hrun
  refine ⟨hprob, hlen, hcov, hv, hrun, ?_, ?_⟩
  · intro a hfit hcons
    exact (propLinLe2_safe st coeffs is b hlen).1 l r hrun' a hfit hcons
  · exact (propLinLe2_reason_valid hprob hlen hrun').1.1

/-! ### The stale witness: the schema's head entailment is genuinely lost

Current state: `x ∈ {0,5}`, `y ∈ {−3,5}`; historical state: `y ∈ {0}`.
The cache records the historical `y`-entry. The cached run at the
CURRENT state computes the rest min-sum from the STALE `mn(y) = 0`
(while the true current minimum is `−3`) and emits `x ≤ 2` with the
stale pin `y ≤ −1`. The historical fields of `StaleReasonOK` all hold
(the data was right at the historical state), but `x ≤ 2` is NOT
entailed by `x + y ≤ 2` at the current box: `x = 5, y = −3` satisfies
the constraint and falsifies the emitted literal. -/

/-- The historical state of the witness: `x ∈ {0,5}`, `y ∈ {0}`. -/
def staleHistSt : State where
  domains := [Dom.ofList [Value.int 0, Value.int 5], Dom.ofList [Value.int 0]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- The current state of the witness: `x ∈ {0,5}`, `y ∈ {−3,5}` (the
    `y`-domain was restored/grown — the stale direction). -/
def staleNowSt : State where
  domains := [Dom.ofList [Value.int 0, Value.int 5],
    Dom.ofList [Value.int (-3), Value.int 5]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- The witness cache: both entries recorded at the historical state. -/
def staleCache : LinCache := LinCache.rebuild staleHistSt [0, 1]

/-- The witness constraint's problem shell. -/
def staleProblem : Problem DomConstraint Unit where
  names := []
  domains := []
  constraints := [DomConstraint.linLe [1, 1] [0, 1] 2]
  objective := ()
  clauses := []

/-- The witness assignment `x = 5, y = −3`: a solution of the constraint
    inside the CURRENT box that falsifies the emitted bound `x ≤ 2`. -/
def staleWitness : Assignment := [Value.int 5, Value.int (-3)]

/-- The witness cache is valid at the historical state. -/
theorem staleCache_valid_hist : CacheValid staleCache staleHistSt :=
  LinCache.rebuild_valid staleHistSt [0, 1]

/-- ...and covers the constraint slots. -/
theorem staleCache_covers : staleCache.Covers [0, 1] :=
  LinCache.rebuild_covers staleHistSt [0, 1]

/-- ...but NOT valid at the current state: the `y`-entry is stale. -/
theorem staleCache_not_valid_now : ¬ CacheValid staleCache staleNowSt := by
  intro h
  have hy : (SlotEntry.ofState staleHistSt 1).Valid staleNowSt :=
    h (SlotEntry.ofState staleHistSt 1) (by
      rw [staleCache, LinCache.rebuild, List.mem_map]
      exact ⟨1, by simp, rfl⟩)
  have h1 := hy.1
  have hslot : (SlotEntry.ofState staleHistSt 1).slot = 1 := rfl
  have hhist : (SlotEntry.ofState staleHistSt 1).dom =
      Dom.ofList [Value.int 0] := rfl
  have hnow : staleNowSt.domains.getD 1 Dom.empty =
      Dom.ofList [Value.int (-3), Value.int 5] := rfl
  rw [hslot, hnow] at h1
  rw [hhist] at h1
  exact absurd h1 (by intro hc; cases hc)

/-- The cached run at the HISTORICAL state emits `x ≤ 2` with the pin
    `y ≤ −1` — sound there (`y ≥ 0` forces `x ≤ 2`). -/
theorem staleCache_hist_emits :
    propLinLe2Cached staleCache staleHistSt [1, 1] [0, 1] 2 =
      .implied (posLe 0 2) { clause := [posLe 0 2, posLe 1 (-1)] } :=
  rfl

/-- At the CURRENT state the same cached data emits `x ≤ 2` again — now
    UNSOUND: the rest min-sum is stale (`0` instead of `−3`). -/
theorem staleCache_now_emits :
    propLinLe2Cached staleCache staleNowSt [1, 1] [0, 1] 2 =
      .implied (posLe 0 2) { clause := [posLe 0 2, posLe 1 (-1)] } :=
  rfl

/-- The witness assignment fits the current box. -/
theorem stale_witness_fits :
    Core.Assignment.Fits staleNowSt.domains staleWitness := by
  refine ⟨rfl, ?_⟩
  intro slot value hv
  have hlt : slot < 2 := (List.getElem?_eq_some_iff.mp hv).1
  cases slot with
  | zero =>
      have h2 : staleWitness[0]? = some value := hv
      rw [show staleWitness[0]? = some (Value.int 5) from rfl] at h2
      injection h2 with h3
      rw [← h3]
      have hdom : staleNowSt.domains.getD 0 DomainLike.empty =
          Dom.ofList [Value.int 0, Value.int 5] := rfl
      rw [hdom]
      simp
  | succ n =>
      have hn : n = 0 := by omega
      subst hn
      have h2 : staleWitness[1]? = some value := hv
      rw [show staleWitness[1]? = some (Value.int (-3)) from rfl] at h2
      injection h2 with h3
      rw [← h3]
      have hdom : staleNowSt.domains.getD 1 DomainLike.empty =
          Dom.ofList [Value.int (-3), Value.int 5] := rfl
      rw [hdom]
      simp

/-- The witness assignment satisfies the constraint (`5 + (−3) = 2 ≤ 2`). -/
theorem stale_witness_satisfies :
    (DomConstraint.linLe [1, 1] [0, 1] 2).SatisfiedBy staleWitness := by
  have hd : dotProduct (intVals [1, 1])
      (List.map (fun i => staleWitness[i]!) [0, 1]) = some 2 := rfl
  show dotLe (intVals [1, 1])
    (List.map (fun i => staleWitness[i]!) [0, 1]) 2 = true
  unfold dotLe
  rw [hd]
  exact of_decide_eq_true rfl

/-- **THE STALENESS IS REAL**: the emitted head `x ≤ 2` is NOT entailed
    at the current box — the schema's `head_entailed` cannot be dropped
    and is not implied by the historical fields. -/
theorem stale_head_not_entailed :
    ¬ (∀ a, Core.Assignment.Fits staleNowSt.domains a →
        (DomConstraint.linLe [1, 1] [0, 1] 2).SatisfiedBy a →
        (posLe 0 2).eval a = some true) := by
  intro h
  have h1 := h staleWitness stale_witness_fits stale_witness_satisfies
  have h2 : (posLe 0 2).eval staleWitness = some false := rfl
  rw [h2] at h1
  cases h1

/-- The historical fields of the obligation hold at the witness while
    `head_entailed` fails: the schema rejects exactly the stale use. -/
theorem stale_witness_not_staleReasonOK :
    ¬ StaleReasonOK staleProblem staleCache staleHistSt staleNowSt
        [1, 1] [0, 1] 2 (posLe 0 2) { clause := [posLe 0 2, posLe 1 (-1)] } := by
  intro h
  exact stale_head_not_entailed h.head_entailed

/-! ## 8. Ledger (PLAN §6 E2)

### Proved here (no `sorry`, no axiom; imports: `Fam/Lin` only)

* The cache carrier: `SlotSummary`/`summaryOfDomain`, `SlotEntry`
  (slot + frozen domain key + extrema), `LinCache`, the validity
  predicate `CacheValid` and the per-entry spelling lemmas
  (`SlotEntry.stored_minContrib_eq_dom`: the stored contribution is the
  stored domain's extrema-contribution; `SlotEntry.stored_minContrib_eq`:
  it is the CURRENT `minContrib`).
* The cached selection layer: `LinCache.minAt`/`maxAt`/`causeMinAt`/
  `causeMaxAt`/`sumMinC`/`sumMaxC`/`causesMin`/`causesMax` with
  `_eq` agreement theorems against `minContrib`/`maxContrib`/
  `linCauseMinPair`/`linCauseMaxPair`/`sumMin`/`sumMax`/`linCausesMin`/
  `linCausesMax` (`sumContrib` is the fold; `sumMin_eq_sumContrib` etc.
  are the reference instances).
* The cached kernels: `linDeduceLeC`/`linDeduceEqC` + arms, each with an
  arm-by-arm `_eq`; the reference `linSweep` is REUSED (no sweep twin).
* **The equivalences**: `propLinLe2Cached_eq`, `propLinEq2Cached_eq`
  (`CacheValid` + coverage ⇒ the cached run IS the certified run), and
  the transferred consumer obligations `propLinLe2Cached_safe`/`_entitled`/
  `_reason_valid` (+ `linEq` twins).
* The update laws: `rebuild`/`rebuild_valid`/`rebuild_covers` (+ the
  positional bridge `rebuild_getElem?`/`rebuild_get?_key` for an
  array/slot-indexed runtime table), the per-slot recomputation
  `touch` + `touch_valid` (frame condition: other slots unchanged) +
  `touch_covers`, the batch/restoration recomputation `touchSlots` +
  `touchSlots_valid` + `touchSlots_covers`, and the conservative
  `invalidateSlot` + `invalidateSlot_valid` +
  `invalidateSlot_covers_other`.
* The stale-reason obligation `StaleReasonOK` (with the `StaleBoundOK`
  monotonicity certificate defined), its inhabitation
  `staleReasonOK_of_valid`, and the machine-checked witness
  `stale_head_not_entailed`/`stale_witness_not_staleReasonOK`: stale data
  passes every historical field yet the emitted literal is not entailed
  at the current state, so `head_entailed` is load-bearing.

### To wire (not in this module)

1. **Storage point** (recommended): a new `caches : List (Option LinCache)`
   field in `PropScheduler` (`ScheduledPropagation.lean`) aligned with
   the propagator list — like `seen`, but holding E2 summaries instead
   of recorded results. `PropSchedulerOK` gains a `CachesOK` conjunct
   (`∀ i, props[i]? = some p → caches[i]? = some c → CacheValid c
   (frameState g)`), preserved by the existing scan theorems. The E1
   alternative — extending `WorkQueue.seen`'s per-unit record — couples
   the cache to the queue's reference frames and only helps queued units;
   the scheduler-field route helps EVERY linear run at a changed frame
   (the measured 1HZ5 hot spot re-runs the linEq sweep every step).
2. **Event-driven updates**: `EventContract.frameEvents qframe f`
   already yields the changed slots; call `touchSlots cache (frameState f)`
   with those slots on a frame transition (or `touch` per event slot),
   and use the `replaced` kind for restoration (`invalidateSlot` where a
   conservative drop is wanted). `PropScheduler.qframe` is the reference
   frame for computing the events.
3. **Run replacement**: the linear registration's `run` becomes
   `propLinLe2Cached c st coeffs is b` with `c` looked up per index; the
   proofs above discharge equivalence. (The reverted `watches := []`
   registration is unaffected: E0 locality/`SkipsStable` for the linear
   families is already proved at the audited footprint; E2 does NOT need
   it — it makes the run cheap instead of skipping it.)
4. **Versioned-domain API (D2)**: `Valid` compares the stored key with
   `=`. The runtime key should be a per-slot version/summary (`SlotSum`
   from `DbScanIndex.lean` has the same `minInt`/`maxInt` projections as
   `SlotSummary`; `CompactDomain`'s `Dom` version would serve as the
   constant-time key). The bridge obligation is a refinement theorem
   `summaryOfDomain` = runtime summary of the current domain; `touch`
   already avoids content comparisons entirely.
5. **Runtime lookup shape**: this module's proof-model lookup is
   `entries.find?` (linear); the wiring should index by slot (array /
   aligned table) through `rebuild_getElem?`/`rebuild_get?_key`, and may
   precompute the rest-sums as total-minus-pair to make each sweep
   position O(1) in the sums.

### Missing proofs for the genuinely stale route (open, named)

* `StaleBoundOK → StaleReasonOK.head_entailed` (min/max-contribution sums
  are monotone under box inclusion; the certificate is defined, the
  implication is not proved).
* The direct `StaleReasonOK.reason_entailed` discharge without
  `CacheValid` (the cached nogood truth kernel; plausible by the same
  arithmetic as `lin2_nogood_*_true` with cached selectors).
* The pin-chronology half of live reuse: the emitted clause's non-head
  literals must be trail-false at the consuming state (the engine
  chronology side of the stale-reason hazard).

### Performance note (PLAN 1HZ5 evidence)

The measured 1HZ5 linEq run is ~0.60 s per scheduler step (a 169-slot
constraint over wide domains; the sweep re-reads every other slot's
`domMinI`/`domMaxI` per position — ~n² wide-domain scans per run). The
cache replaces those scans by one pass per changed slot plus lookups;
the equivalence theorems above make the replacement free. To MEASURE the
benefit: wire items 1-3 (or a `Tests/E2/` harness running
`propLinEq2` vs `propLinEq2Cached` on a 1HZ5-shaped frame), then use the
B0 scaffold (`audits/benchmark_performance.py`) with the same 60-second
budget; the per-run difference is directly attributable because the
kernel choice is the only change. This module deliberately does not
touch the runtime. -/

end LeanFzn.Solver.Propagation
