/-
File: LeanFzn/Solver/Propagation/SparseFrame.lean

Purpose (M2 stage 1: the sparse frame TYPE and TRANSPORTS, UNWIRED).

  This module exposes the S0 arbitrary-slot frame API
  (`S0-decision-design.md` §3, the shape chosen by S0 and prototyped in
  `DecisionProto.lean`) as a standalone refinement layer over the current
  positional `BranchFrame = List Domain × Assignment`, and proves the
  transports between the two representations.  It does NOT switch any
  shared type, does NOT wire any runtime path, and is imported by no
  runtime module: the scheduled cone keeps the positional `BranchFrame`
  until the later D1-gated integration stages.

  The frame type itself is S0's frozen shape (`doms : List Domain`,
  `order : List Nat`), imported and re-exported as `SparseFrame.Frame`
  (import DAG checked: `DecisionProto` imports only `FrontierSemantics` and
  nothing imports `DecisionProto`, so the import is acyclic and no S0
  theorem is reproved here — the S0/S1 results are reused by import).

  Contents:
  * §1 the frame alias and `Frame.WF` (duplicate-free decision order, all
    decided slots are slot indices, decided slots hold their singletons;
    `WF_iff_protoWF` connects it to S0's two-conjunct invariant, and
    `order_perm_range_of_level_eq` discharges the "duplicate-free
    permutation of `List.range doms.length`" reading for complete frames);
  * §2 denotation/coverage (`Frame.Denote`, `Frame.covers`), the
    `FrameCovers`-compatible bridges, `toPrefixFrame`/`ofPrefixFrame` and
    the general `toPrefixFrame?` transport with the round-trip laws under
    `WF` (plus the unconditional empty-prefix round trips), and the
    order-independence laws;
  * §3 operation refinement: `pin`/`retire` coverage laws (including the
    S0 union law `covers_pin_or_retire` and the positional `covers_split`
    bridge at the empty prefix), the sparse `filterSlot`/`Frame.filterFrame`,
    the bridge from the current `filterSlots`/`filterFrame` at the empty
    prefix, and both enum-level filter coverage equivalences;
  * §4 decision/level/checkpoint vocabulary: `Frame.slotAtLevel`,
    `Frame.decisionEntry` (with the `BranchState.decide` connection), the
    `Checkpoint.Identifies` → `DecisionCheckpoint.Identifies` transport
    for the current checkpoint type, and the level-to-slot ledger laws;
  * §5 restatements (pointers) of the S0 progress facts: `mass_pin_lt`,
    `mass_retire_lt`, `cost_pin_lt`, `cost_retire_lt`,
    `frontierWeight_split_lt` — reused from `DecisionProto`, not reproved.

  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no proof escapes.

Obligation ledger (S0 `S0-decision-design.md` §5 migration map).

  Covered by this stage (the type + transport part of M1):
  * sparse frame type (S0 §3.1) with `WF` and all S0 `WF` facts;
  * coverage bridge to the current `FrameCovers` and to
    `allAssigns`-membership semantics;
  * `toPrefixFrame` (empty-prefix positional transport),
    `ofPrefixFrame`, the general `toPrefixFrame?` transport matching the
    current `(remaining, prefix)` representation, and the round-trip laws;
  * `pin`/`retire` coverage laws (S0 union law + exact enum-level
    characterizations), the positional `covers_split` bridge, the filter
    semantics bridge, and slot-order independence of the denotation;
  * level vocabulary (`Frame.level`, `Frame.slotAtLevel`,
    `Frame.decisionEntry`) and the checkpoint transport to the current
    `DecisionCheckpoint.Identifies`;
  * the S0 progress facts (imported from `DecisionProto`, restated).

  Remaining (later stages; this module is the interface):
  * M2 (D1-gated shared edit): switch the scheduled cone's `BranchFrame`
    to the sparse type — `Frontier.lean` rename + new type,
    `FrontierSemantics.lean` membership body, `FrameFilter.lean`
    slot-direct filter, chronological cone renamed `PrefixFrame`; the
    statements of `FrameCovers`/`FrameDescendsFrom`/`Identifies` keep
    their shapes;
  * M3 closure layer: `ExplainedPropagation`, `ConflictResolution`,
    `ClosureFast`, `Analysis*` consume `Frame.filterFrame` (slot-direct,
    `none` iff the filtered domain empties);
  * M4 restoration: `canonicalPins`/`slotFalsifiers`/`canonicalTrail`/
    `resumePending` construction (`BackjumpFrontier`, `SchedulerStep`,
    `SchedulerState`); this stage supplies `decisionEntry`/`slotAtLevel`
    and states the trail-prefix law as an explicit hypothesis in the
    checkpoint transport;
  * M5 proof layer: `SchedulerRank` adoption `(frontierWeight,
    Frame.mass, Frame.level)` over `Frame.cost`;
  * M6: S1 wiring (`selectSlot` is imported and unwired) and the runtime
    A/B measurement;
  * M7: compiler/objective/output transport (none expected: the witness is
    read in original slot order, `covers_read`; `toStore` untouched).

  Exact next-stage interface: use `SparseFrame.Frame`, `toPrefixFrame` for
  empty-prefix positional bridges, `Frame.filterFrame` for narrowing,
  `DecisionProto.selectSlot` for selection, and
  `Checkpoint.identifies_toDecisionCheckpoint` for checkpoints (providing
  the canonical trail prefix in M4).

DAG: DecisionProto + FrameFilter + BackjumpFrontier -> SparseFrame
     (leaf module; nothing scheduled imports it yet).
-/
import LeanFzn.Legacy.Solver.Propagation.DecisionProto
import LeanFzn.Solver.Propagation.FrameFilter
import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier

open LeanFzn.Semantics LeanFzn.Solver.Core

namespace LeanFzn.Solver.Propagation.SparseFrame

/-! ## §1 The sparse frame type and its structure invariant -/

/-- The S0 sparse search frame: the full per-slot box (`doms`, indexed by
the ORIGINAL slot number; decided slots hold their singleton) and the
decision order (`order`, decided slots oldest-first; level `L` decided
`order[L-1]`). This is S0's frozen shape, re-exported from the prototype
`DecisionProto.Frame` (no duplicate declaration; see the header). -/
abbrev Frame := DecisionProto.Frame

/-- The frame's current decision level: the number of decisions. -/
abbrev Frame.level (f : Frame) : Nat := f.order.length

/-- Pin the selected slot `k` to `v`: the decision child (S0/DecisionProto). -/
abbrev Frame.pin (f : Frame) (k : Nat) (v : Value) : Frame :=
  DecisionProto.Frame.pin f k v

/-- Retire the value `v` from slot `k`: the sibling alternative
(S0/DecisionProto). -/
abbrev Frame.retire (f : Frame) (k : Nat) (vs : Domain) : Frame :=
  DecisionProto.Frame.retire f k vs

/-- Sparse frame coverage (S0/DecisionProto), re-exported. -/
abbrev Frame.Covers (f : Frame) (a : Assignment) : Prop :=
  DecisionProto.Frame.Covers f a

/-- `FrameCovers`-compatible membership denotation: the assignments
enumerated by the full per-slot box. This is exactly the body S0 freezes
for the sparse `FrameCovers` (§3.1); `covers_iff_FrameCovers` bridges it
to the current positional `FrameCovers` at the empty prefix. -/
def Frame.covers (f : Frame) (a : Assignment) : Prop := a ∈ allAssigns f.doms

/-- The sparse coverage as a predicate on complete assignments (S0 §3.1). -/
def Frame.Denote (f : Frame) : Assignment → Prop := fun a => f.covers a

/-- Membership in the denotation is coverage. -/
theorem Frame.mem_Denote_iff (f : Frame) (a : Assignment) :
    f.Denote a ↔ f.covers a := Iff.rfl

/-- Frame-level decision legality (S0/DecisionProto): a live slot has a
non-singleton domain. -/
abbrev Frame.Live (f : Frame) (k : Nat) : Prop := DecisionProto.Live f.doms k

/-- Box-level decision legality. -/
abbrev Live := DecisionProto.Live

/-- The S1 selection hook (imported; unwired in this stage). -/
abbrev selectSlot := DecisionProto.selectSlot

/-- Domain cardinality read at a slot (imported from DecisionProto). -/
abbrev Card := DecisionProto.Card

/-- Sparse frame mass: the sum of the domain lengths of the full box. -/
abbrev Frame.mass (f : Frame) : Nat := DecisionProto.Frame.mass f

/-- Sparse frame cost: the shared `branchCost` read on the full box. -/
abbrev Frame.cost (f : Frame) : Nat := DecisionProto.Frame.cost f

/-- Sparse frontier weight (S0 §3.5): `∑ 3 ^ cost` over the pending stack,
the replacement for the positional `frontierCost` (S0 obstruction 3). -/
abbrev frontierWeight := DecisionProto.frontierWeight

/-- The full box of a sparse frame (S0 §3.1). -/
abbrev Frame.domains (f : Frame) : List Domain := f.doms

/-- The sparse analogue of S0's `PinsAgree` (§3.1): a (covered) assignment
reads the recorded value at every singleton slot — in particular at every
decided slot. This replaces the positional `f.2 <+: a` prefix test. -/
def Frame.PinsAgree (f : Frame) (a : Assignment) : Prop :=
  ∀ (k : Nat) (v : Value), f.doms[k]? = some (Dom.ofList [v]) → a[k]? = some v

/-- The sparse frame's structural invariant (S0 §3.1 + the range form):
the decision order is duplicate-free, every decided slot is a slot index
of the box, and every decided slot holds its singleton. A duplicate-free
list of distinct slot indices is a sub-permutation of
`List.range f.doms.length`; when the frame is fully decided
(`level = doms.length`) it is a permutation
(`Frame.WF.order_perm_range_of_level_eq`). -/
def Frame.WF (f : Frame) : Prop :=
  f.order.Nodup ∧ (∀ k ∈ f.order, k < f.doms.length) ∧
    (∀ k ∈ f.order, ∃ v, f.doms[k]? = some (Dom.ofList [v]))

/-- `Frame.WF` is S0's prototype invariant: the extra range conjunct is
derivable from "decided slots hold singletons", and is kept explicit so the
order is literally a duplicate-free list of slot indices. -/
theorem Frame.WF_iff_protoWF {f : Frame} :
    f.WF ↔ DecisionProto.Frame.WF f := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2⟩
  · intro h
    refine ⟨h.1, ?_, h.2⟩
    intro k hk
    obtain ⟨v, hv⟩ := h.2 k hk
    exact (List.getElem?_eq_some_iff.mp hv).1

/-- The decision order is duplicate-free. -/
theorem Frame.WF.order_nodup {f : Frame} (h : f.WF) : f.order.Nodup := h.1

/-- Every decided slot is a slot index of the box. -/
theorem Frame.WF.order_lt {f : Frame} (h : f.WF) :
    ∀ k ∈ f.order, k < f.doms.length := h.2.1

/-- Every decided slot is a member of `List.range doms.length`. -/
theorem Frame.WF.order_mem_range {f : Frame} (h : f.WF) :
    ∀ k ∈ f.order, k ∈ List.range f.doms.length :=
  fun k hk => List.mem_range.mpr (h.2.1 k hk)

/-- Every decided slot holds its singleton. -/
theorem Frame.WF.order_singleton {f : Frame} (h : f.WF) :
    ∀ k ∈ f.order, ∃ v, f.doms[k]? = some (Dom.ofList [v]) := h.2.2

/-- Erasing a member of a duplicate-free list removes its only occurrence. -/
private theorem not_mem_erase_of_nodup {l : List Nat} (hnd : l.Nodup) (a : Nat) :
    a ∉ l.erase a := by
  intro hmem
  have hmeml : a ∈ l := List.mem_of_mem_erase hmem
  have hcount : List.count a (l.erase a) = List.count a l - 1 := List.count_erase_self
  have hcountl : List.count a l = 1 := by
    rw [List.Nodup.count hnd]
    simp [hmeml]
  have hpos : 0 < List.count a (l.erase a) := List.count_pos_iff.mpr hmem
  omega

/-- Distinct naturals below `n` number at most `n`. -/
private theorem length_le_of_nodup_forall_lt : ∀ (n : Nat) (l : List Nat),
    l.Nodup → (∀ k ∈ l, k < n) → l.length ≤ n
  | 0, l, _, h => by
      cases l with
      | nil => simp
      | cons k rest => exact absurd (h k (List.mem_cons_self ..)) (Nat.not_lt_zero k)
  | n + 1, l, hnd, h => by
      by_cases hmem : n ∈ l
      · have hnd' : (l.erase n).Nodup := hnd.erase n
        have h' : ∀ k ∈ l.erase n, k < n := by
          intro k hk
          have hk' : k ∈ l := List.mem_of_mem_erase hk
          have hklt : k < n + 1 := h k hk'
          have hkne : k ≠ n := by
            intro hkn
            exact not_mem_erase_of_nodup hnd n (hkn ▸ hk)
          omega
        have hle := length_le_of_nodup_forall_lt n (l.erase n) hnd' h'
        have hlen : (l.erase n).length = l.length - 1 := List.length_erase_of_mem hmem
        have hpos : 0 < l.length := List.length_pos_of_mem hmem
        omega
      · have h' : ∀ k ∈ l, k < n := by
          intro k hk
          have hklt : k < n + 1 := h k hk
          have hkne : k ≠ n := fun hkn => hmem (hkn ▸ hk)
          omega
        have hle := length_le_of_nodup_forall_lt n l hnd h'
        omega

/-- Level bound: a well-formed frame never has more decisions than slots. -/
theorem Frame.WF.level_le_length {f : Frame} (h : f.WF) :
    f.level ≤ f.doms.length := by
  have := length_le_of_nodup_forall_lt f.doms.length f.order h.1 h.2.1
  simpa [Frame.level] using this

/-- A duplicate-free order of exactly the range's length and inside the
range is a permutation of the range. -/
private theorem perm_range_of_nodup_forall_lt_length : ∀ (n : Nat) (l : List Nat),
    l.Nodup → (∀ k ∈ l, k < n) → l.length = n → l.Perm (List.range n)
  | 0, l, _, _, hlen => by
      have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst hl
      exact List.perm_nil.mpr rfl
  | n + 1, l, hnd, hlt, hlen => by
      by_cases hmem : n ∈ l
      · have hnd' : (l.erase n).Nodup := hnd.erase n
        have hlt' : ∀ k ∈ l.erase n, k < n := by
          intro k hk
          have hk' : k ∈ l := List.mem_of_mem_erase hk
          have hklt : k < n + 1 := hlt k hk'
          have hkne : k ≠ n := fun hkn => not_mem_erase_of_nodup hnd n (hkn ▸ hk)
          omega
        have hlen' : (l.erase n).length = n := by
          rw [List.length_erase_of_mem hmem]
          omega
        have ih := perm_range_of_nodup_forall_lt_length n (l.erase n) hnd' hlt' hlen'
        have hperm1 : l.Perm (n :: l.erase n) := List.perm_cons_erase hmem
        have hperm2 : (n :: l.erase n).Perm (n :: List.range n) := List.Perm.cons n ih
        have hperm3 : (n :: List.range n).Perm (List.range n ++ [n]) := by
          rw [← List.singleton_append]
          exact List.perm_append_comm.symm
        rw [List.range_succ]
        exact hperm1.trans (hperm2.trans hperm3)
      · have hlt' : ∀ k ∈ l, k < n := by
          intro k hk
          have hklt : k < n + 1 := hlt k hk
          have hkne : k ≠ n := fun hkn => hmem (hkn ▸ hk)
          omega
        have hbound := length_le_of_nodup_forall_lt n l hnd hlt'
        exact absurd hlen (by omega)

/-- The "permutation of `List.range doms.length`" reading of `WF` for a
fully decided frame: a duplicate-free order listing distinct in-range
slots of the right length is a permutation of the range. -/
theorem Frame.WF.order_perm_range_of_level_eq {f : Frame} (h : f.WF)
    (hfull : f.level = f.doms.length) :
    f.order.Perm (List.range f.doms.length) :=
  perm_range_of_nodup_forall_lt_length f.doms.length f.order h.1 h.2.1
    (by simpa [Frame.level] using hfull)

/-- A live slot is never a decided slot (imported decision freshness). -/
theorem Frame.WF.not_mem_order_of_live {f : Frame} (h : f.WF) {k : Nat}
    (hl : f.Live k) : k ∉ f.order :=
  DecisionProto.Frame.WF.not_mem_order_of_live (Frame.WF_iff_protoWF.mp h) hl

/-- The decision step preserves well-formedness. -/
theorem Frame.WF.pin {f : Frame} (h : f.WF) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hfresh : k ∉ f.order) :
    (f.pin k v).WF :=
  Frame.WF_iff_protoWF.mpr
    (DecisionProto.Frame.WF.pin (Frame.WF_iff_protoWF.mp h) hk hfresh)

/-- The retirement step preserves well-formedness. -/
theorem Frame.WF.retire {f : Frame} (h : f.WF) {k : Nat} {vs : Domain}
    (hfresh : k ∉ f.order) : (f.retire k vs).WF :=
  Frame.WF_iff_protoWF.mpr
    (DecisionProto.Frame.WF.retire (Frame.WF_iff_protoWF.mp h) hfresh)

/-- Well-formedness is preserved by a decision on a live slot: freshness is
`WF.not_mem_order_of_live`. -/
theorem Frame.WF.pin_of_live {f : Frame} (h : f.WF) {k : Nat} {v : Value}
    {vs : Domain} (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hl : f.Live k) :
    (f.pin k v).WF :=
  h.pin hk (h.not_mem_order_of_live hl)

/-! ## §2 Denotation and transports to the positional frame -/

/-- Coverage through the shared name: the sparse body is exactly the
membership form S0 freezes for the sparse `FrameCovers`. -/
theorem Frame.covers_iff_Covers (f : Frame) (a : Assignment) :
    f.covers a ↔ DecisionProto.Frame.Covers f a := Iff.rfl

/-- `FrameCovers`-compatibility at the empty prefix: the sparse coverage is
the current positional `FrameCovers` of the derived `(f.doms, [])` frame. -/
theorem Frame.covers_iff_FrameCovers (f : Frame) (a : Assignment) :
    f.covers a ↔ PrefixCovers (f.doms, []) a :=
  DecisionProto.Frame.covers_iff_frameCovers f a

/-- A covered assignment is pinned-agreeing. -/
theorem Frame.pinsAgree_of_covers {f : Frame} {a : Assignment} (h : f.covers a) :
    f.PinsAgree a :=
  fun _ _ hk => DecisionProto.covers_read h hk

/-- A covered assignment fits the box (read through the shared `Fits`). -/
theorem Frame.covers_fits {f : Frame} {a : Assignment} (h : f.covers a) :
    a.Fits f.domains :=
  allAssigns_fits f.doms a h

/-- The current positional bridge: a sparse frame is represented exactly by
the empty-prefix positional frame `(f.doms, [])`. -/
def toPrefixFrame (f : Frame) : PrefixFrame := (f.doms, [])

/-- Coverage is preserved by the empty-prefix transport. -/
theorem covers_toPrefixFrame_iff (f : Frame) (a : Assignment) :
    f.covers a ↔ PrefixCovers (toPrefixFrame f) a :=
  DecisionProto.Frame.covers_iff_frameCovers f a

/-- The positional bridge in the other direction: reconstruct the sparse
frame of a `(remaining, prefix)` frame — the chosen prefix becomes
singleton domains and the decision order `List.range prefix.length`. -/
def ofPrefixFrame (g : PrefixFrame) : Frame :=
  { doms := g.2.map (fun v => Dom.ofList [v]) ++ g.1, order := List.range g.2.length }

@[simp] theorem ofPrefixFrame_doms (g : PrefixFrame) :
    (ofPrefixFrame g).doms = g.2.map (fun v => Dom.ofList [v]) ++ g.1 := rfl

@[simp] theorem ofPrefixFrame_order (g : PrefixFrame) :
    (ofPrefixFrame g).order = List.range g.2.length := rfl

/-- The product of singleton domains is the single assignment of the prefix. -/
theorem allAssigns_map_singleton (vs : Assignment) :
    allAssigns (vs.map (fun v => Dom.ofList [v])) = [vs] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, allAssigns, Dom.enum_ofList, List.flatMap_cons,
        List.map_cons]
      rw [ih]
      simp

/-- The positional coverage is exactly the sparse coverage of
`ofPrefixFrame`: `(remaining, prefix)` is representable as the sparse frame
whose decided prefix slots are `0 .. prefix.length-1`. -/
theorem covers_ofPrefixFrame_iff (g : PrefixFrame) (a : Assignment) :
    PrefixCovers g a ↔ (ofPrefixFrame g).covers a := by
  obtain ⟨slots, chosen⟩ := g
  rw [Frame.covers]
  change (∃ tail ∈ allAssigns slots, a = chosen ++ tail) ↔
    a ∈ allAssigns (chosen.map (fun v => Dom.ofList [v]) ++ slots)
  rw [allAssigns_append_of_elems]
  constructor
  · rintro ⟨tail, ht, rfl⟩
    exact ⟨chosen, by rw [allAssigns_map_singleton]; exact List.mem_singleton.mpr rfl,
      tail, ht, rfl⟩
  · rintro ⟨pre, hp, tail, ht, heq⟩
    rw [allAssigns_map_singleton] at hp
    have hpre : pre = chosen := List.mem_singleton.mp hp
    exact ⟨tail, ht, by rw [heq, hpre]⟩

/-- `ofPrefixFrame` is well formed for every positional frame. -/
theorem ofPrefixFrame_WF (g : PrefixFrame) : (ofPrefixFrame g).WF := by
  obtain ⟨slots, chosen⟩ := g
  refine ⟨?_, ?_, ?_⟩
  · exact List.nodup_range (n := chosen.length)
  · intro k hk
    have hk' : k < chosen.length := List.mem_range.mp hk
    simp only [ofPrefixFrame_doms, List.length_append, List.length_map]
    omega
  · intro k hk
    have hk' : k < chosen.length := List.mem_range.mp hk
    refine ⟨chosen[k], ?_⟩
    rw [ofPrefixFrame_doms, List.getElem?_append_left (by simpa using hk'),
      List.getElem?_map, List.getElem?_eq_some_iff.mpr ⟨hk', rfl⟩]
    rfl

/-- The reconstructed frame's level is the prefix length. -/
theorem ofPrefixFrame_level (g : PrefixFrame) :
    (ofPrefixFrame g).level = g.2.length := by
  simp [Frame.level, ofPrefixFrame]

/-- Reading singleton domains of a box prefix, `none` when some domain is
not a singleton. -/
def singletonValues : List Domain → Option Assignment
  | [] => some []
  | d :: rest =>
      match Dom.enum d with
      | [v] =>
          if Dom.eqB d (Dom.ofList [v]) then
            (singletonValues rest).map fun pre => v :: pre
          else none
      | _ => none

/-- Singleton boxes read back their values. -/
theorem singletonValues_map_singleton (vs : Assignment) :
    singletonValues (vs.map (fun v => Dom.ofList [v])) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, singletonValues, Dom.enum_ofList, Dom.eqB_refl,
        if_true]
      rw [ih]
      rfl

/-- Exact characterization of a successful read: the box is exactly the
    canonical singleton domains of the read assignment. -/
theorem singletonValues_eq_some_iff : ∀ (l : List Domain) (pre : Assignment),
    singletonValues l = some pre ↔ l = pre.map (fun v => Dom.ofList [v]) := by
  intro l
  induction l with
  | nil =>
      intro pre
      constructor
      · intro h
        have hp : pre = [] := by simpa [singletonValues] using h.symm
        subst hp
        rfl
      · intro h
        have hp : pre = [] := by
          have hlen := congrArg List.length h
          simpa using hlen.symm
        subst hp
        rfl
  | cons d rest ih =>
      intro pre
      match hd : Dom.enum d with
      | [] =>
          have hnone : singletonValues (d :: rest) = none := by
            simp only [singletonValues, hd]
          rw [hnone]
          constructor
          · intro h
            exact absurd h (by simp)
          · intro h
            cases pre with
            | nil => simp at h
            | cons w pre' =>
                simp only [List.map_cons, List.cons.injEq] at h
                obtain ⟨hdw, -⟩ := h
                have he := congrArg Dom.enum hdw
                rw [hd, Dom.enum_ofList] at he
                simp at he
      | [v] =>
          by_cases heq : Dom.eqB d (Dom.ofList [v]) = true
          · have hdEq : d = Dom.ofList [v] := Dom.eqB_sound heq
            have hsome : singletonValues (d :: rest) =
                (singletonValues rest).map (fun pre => v :: pre) := by
              simp only [singletonValues, hd, heq, if_true]
            rw [hsome, Option.map_eq_some_iff]
            constructor
            · rintro ⟨pre', hpre', rfl⟩
              rw [(ih pre').mp hpre', hdEq]
              rfl
            · intro h
              cases pre with
              | nil => simp at h
              | cons w pre' =>
                  simp only [List.map_cons, List.cons.injEq] at h
                  obtain ⟨hdw, hrest⟩ := h
                  have hwv : w = v := by
                    have he := congrArg Dom.enum hdw
                    rw [Dom.enum_ofList, hd] at he
                    simpa using he.symm
                  subst hwv
                  exact ⟨pre', (ih pre').mpr hrest, rfl⟩
          · have hnone : singletonValues (d :: rest) = none := by
              simp only [singletonValues, hd, heq, Bool.false_eq_true, if_false]
            rw [hnone]
            constructor
            · intro h
              exact absurd h (by simp)
            · intro h
              cases pre with
              | nil => simp at h
              | cons w pre' =>
                  simp only [List.map_cons, List.cons.injEq] at h
                  obtain ⟨hdw, -⟩ := h
                  have hwv : w = v := by
                    have he := congrArg Dom.enum hdw
                    rw [Dom.enum_ofList, hd] at he
                    simpa using he.symm
                  subst hwv
                  exfalso
                  exact heq (by rw [hdw, Dom.eqB_refl])
      | v :: w :: ws =>
          have hnone : singletonValues (d :: rest) = none := by
            simp only [singletonValues, hd]
          rw [hnone]
          constructor
          · intro h
            exact absurd h (by simp)
          · intro h
            cases pre with
            | nil => simp at h
            | cons u pre' =>
                simp only [List.map_cons, List.cons.injEq] at h
                obtain ⟨hdu, -⟩ := h
                have he := congrArg Dom.enum hdu
                rw [hd, Dom.enum_ofList] at he
                simp at he

/-- The general transport matching the current `(remaining, prefix)`
representation: read the decided prefix values from the singleton domains
of the first `level` slots and keep the rest as remaining domains. `none`
when the first `level` slots are not the decided singletons (the
empty-prefix `toPrefixFrame` is the always-defined fallback). -/
def toPrefixFrame? (f : Frame) : Option PrefixFrame :=
  (singletonValues (f.doms.take f.level)).map fun pre =>
    (f.doms.drop f.level, pre)

/-- Exact characterization of the general transport. -/
theorem toPrefixFrame?_eq_some_iff {f : Frame} {g : PrefixFrame} :
    toPrefixFrame? f = some g ↔
      ∃ pre : Assignment, singletonValues (f.doms.take f.level) = some pre ∧
        g = (f.doms.drop f.level, pre) := by
  unfold toPrefixFrame?
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨pre, hpre, hg⟩
    exact ⟨pre, hpre, hg.symm⟩
  · rintro ⟨pre, hpre, rfl⟩
    exact ⟨pre, hpre, rfl⟩

/-- Round trip (unconditional, prefix direction): transporting a positional
frame to the sparse representation and back returns the same frame. -/
theorem toPrefixFrame?_ofPrefixFrame (g : PrefixFrame) :
    toPrefixFrame? (ofPrefixFrame g) = some g := by
  obtain ⟨slots, chosen⟩ := g
  have htake : (chosen.map (fun v => Dom.ofList [v]) ++ slots).take
      (List.range chosen.length).length = chosen.map (fun v => Dom.ofList [v]) := by
    rw [List.length_range, List.take_append_of_le_length (by simp)]
    apply List.take_of_length_le
    simp
  have hdrop : (chosen.map (fun v => Dom.ofList [v]) ++ slots).drop
      (List.range chosen.length).length = slots := by
    rw [List.length_range]
    rw [show chosen.length = (chosen.map (fun v => Dom.ofList [v])).length by simp]
    exact List.drop_left
  show (singletonValues ((chosen.map (fun v => Dom.ofList [v]) ++ slots).take
      (List.range chosen.length).length)).map (fun pre =>
        (((chosen.map (fun v => Dom.ofList [v]) ++ slots).drop
          (List.range chosen.length).length), pre)) = some (slots, chosen)
  rw [htake, hdrop, singletonValues_map_singleton]
  rfl

/-- Round trip under `WF` (sparse direction): a well-formed frame whose
order is the initial segment `range level` — the frames the scheduled cone
produces — is exactly `ofPrefixFrame` of its general transport. -/
theorem ofPrefixFrame_toPrefixFrame? {f : Frame} {g : PrefixFrame}
    (h : f.WF) (hp : f.order = List.range f.level)
    (hg : toPrefixFrame? f = some g) : ofPrefixFrame g = f := by
  obtain ⟨pre, hpre, hg'⟩ := toPrefixFrame?_eq_some_iff.mp hg
  subst hg'
  have hkeep : f.doms.take f.level = pre.map (fun v => Dom.ofList [v]) :=
    (singletonValues_eq_some_iff _ _).mp hpre
  have hlevel : f.level ≤ f.doms.length := h.level_le_length
  have hplen : pre.length = f.level := by
    have hlen := congrArg List.length hkeep
    rw [List.length_take, List.length_map, Nat.min_eq_left hlevel] at hlen
    omega
  have hd : pre.map (fun v => Dom.ofList [v]) ++ f.doms.drop f.level = f.doms := by
    rw [← hkeep]
    exact List.take_append_drop f.level f.doms
  have ho : List.range pre.length = f.order := by
    rw [hplen]
    exact hp.symm
  calc ofPrefixFrame (f.doms.drop f.level, pre)
      = { doms := f.doms, order := f.order } :=
        (BranchFrame.mk.injEq _ _ _ _).mpr ⟨hd, ho⟩
    _ = f := rfl

/-- Coverage through the general transport under `WF`: the transported
positional frame covers exactly the sparse frame's assignments. -/
theorem covers_toPrefixFrame? {f : Frame} {g : PrefixFrame} {a : Assignment}
    (h : f.WF) (hp : f.order = List.range f.level)
    (hg : toPrefixFrame? f = some g) :
    PrefixCovers g a ↔ f.covers a := by
  rw [← ofPrefixFrame_toPrefixFrame? h hp hg]
  exact covers_ofPrefixFrame_iff g a

/-- Empty-prefix round trip (positional direction, unconditional). -/
theorem toPrefixFrame_ofPrefixFrame_eq_of_snd_eq_nil {g : PrefixFrame}
    (h : g.2 = []) : toPrefixFrame (ofPrefixFrame g) = g := by
  obtain ⟨slots, chosen⟩ := g
  simp only at h
  subst h
  simp [toPrefixFrame, ofPrefixFrame]

/-- Empty-prefix round trip (sparse direction, unconditional). -/
theorem ofPrefixFrame_toPrefixFrame_eq_of_order_eq_nil {f : Frame}
    (h : f.order = []) : ofPrefixFrame (toPrefixFrame f) = f := by
  obtain ⟨doms, order⟩ := f
  simp only at h
  subst h
  simp [toPrefixFrame, ofPrefixFrame]

/-- Coverage round trip on the empty prefix (any frame, no `WF` needed). -/
theorem ofPrefixFrame_toPrefixFrame_covers (f : Frame) (a : Assignment) :
    (ofPrefixFrame (toPrefixFrame f)).covers a ↔ f.covers a := by
  rw [toPrefixFrame, ofPrefixFrame]
  simp [Frame.covers]

/-- The empty-prefix round trip preserves well-formedness. -/
theorem ofPrefixFrame_toPrefixFrame_WF (f : Frame) :
    (ofPrefixFrame (toPrefixFrame f)).WF :=
  ofPrefixFrame_WF _

/-- The denotation of a sparse frame does not depend on the decision
order: slot-order independence of coverage. -/
theorem Frame.covers_eq_of_doms_eq {f g : Frame} (h : f.doms = g.doms)
    (a : Assignment) : f.covers a ↔ g.covers a := by
  rw [Frame.covers, Frame.covers, h]

/-- Slot-order independence, explicitly at fixed box and two orders. -/
theorem Frame.covers_mk_eq (ds : List Domain) (o₁ o₂ : List Nat)
    (a : Assignment) : Frame.covers ⟨ds, o₁⟩ a ↔ Frame.covers ⟨ds, o₂⟩ a :=
  Frame.covers_eq_of_doms_eq rfl a

/-- The denotation of a pin does not depend on the frame's order. -/
theorem Frame.covers_pin_congr {f g : Frame} (h : f.doms = g.doms) (k : Nat)
    (v : Value) (a : Assignment) :
    (f.pin k v).covers a ↔ (g.pin k v).covers a := by
  apply Frame.covers_eq_of_doms_eq
  simp only [Frame.pin, DecisionProto.Frame.pin_doms]
  rw [h]

/-- The denotation of a retirement does not depend on the frame's order. -/
theorem Frame.covers_retire_congr {f g : Frame} (h : f.doms = g.doms) (k : Nat)
    (vs : Domain) (a : Assignment) :
    (f.retire k vs).covers a ↔ (g.retire k vs).covers a := by
  apply Frame.covers_eq_of_doms_eq
  simp only [Frame.retire, DecisionProto.Frame.retire_doms]
  rw [h]

/-- Sparse descent: every assignment covered by `g` is covered by `f`
(the sparse analogue of the current `FrameDescendsFrom`). -/
def Frame.DescendsFrom (g f : Frame) : Prop := ∀ a, g.covers a → f.covers a

/-- The sparse descent is the shared scheduled `FrameDescendsFrom` (M2):
both are coverage inclusion on the full box. -/
theorem Frame.descendsFrom_iff_FrameDescendsFrom (g f : Frame) :
    g.DescendsFrom f ↔ FrameDescendsFrom g f := Iff.rfl

/-! ## §3 Operation refinement: pin/retire vs filter -/

/-- Membership decomposition of `allAssigns` at the head (re-exported from
the prototype). -/
theorem mem_allAssigns_cons_iff {d : Domain} {rest : List Domain}
    {a : Assignment} :
    a ∈ allAssigns (d :: rest) ↔
      ∃ v ∈ d, ∃ a' ∈ allAssigns rest, a = v :: a' :=
  DecisionProto.mem_allAssigns_cons_iff

/-- The sparse slot filter (S0 §4.2): filter the domain at the literal's
slot directly, by absolute slot index (no positional offset). -/
def filterSlot (l : Literal) (ds : List Domain) : List Domain :=
  ds.set l.atom.slot (Dom.filterLitKeep l (ds.getD l.atom.slot Dom.empty))

/-- The sparse frame filter (S0 §3.2/§4.2): filter slot `l.atom.slot`
directly; `none` exactly when the target domain becomes empty (the
assigned-singleton rejection is the current prefix-rejection `none` case).
Out-of-range literals are a no-op, matching the current `filterSlots`
behaviour at an out-of-range offset. -/
def Frame.filterFrame (l : Literal) (f : Frame) : Option Frame :=
  match f.doms[l.atom.slot]? with
  | none => some f
  | some d =>
      match Dom.enum (Dom.filterLitKeep l d) with
      | [] => none
      | _ => some { f with doms := f.doms.set l.atom.slot (Dom.filterLitKeep l d) }

/-- Reading the slot a set operation wrote. -/
theorem getD_set_self {ds : List Domain} {k : Nat} {x : Domain}
    (hk : k < ds.length) : (ds.set k x).getD k Dom.empty = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk]
  rfl

/-- A fitting assignment reads a box value at an in-range slot. -/
theorem read_of_fits {ds : List Domain} {a : Assignment} (hfit : a.Fits ds)
    {k : Nat} (hk : k < ds.length) : ∃ w ∈ ds.getD k Dom.empty, a[k]? = some w := by
  have hk' : k < a.length := by rw [hfit.1]; exact hk
  refine ⟨a[k], ?_, List.getElem?_eq_getElem hk'⟩
  exact hfit.2 k a[k] (List.getElem?_eq_getElem hk')

/-- Reading a covered assignment at an in-range slot. -/
theorem exists_read_of_covers {f : Frame} {a : Assignment} (h : f.covers a)
    {k : Nat} (hk : k < f.doms.length) :
    ∃ v ∈ f.doms.getD k Dom.empty, a[k]? = some v :=
  read_of_fits (allAssigns_fits f.doms a h) hk

/-- Membership in `allAssigns` is preserved by writing a domain containing
the covered value at a slot. -/
theorem mem_allAssigns_set_of_mem {ds : List Domain} {a : Assignment} {k : Nat}
    {x : Domain} {v : Value} (ha : a ∈ allAssigns ds) (hk : a[k]? = some v)
    (hv : v ∈ x) : a ∈ allAssigns (ds.set k x) := by
  induction ds generalizing k a with
  | nil =>
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      simp at hk
  | cons d rest ih =>
      obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          rw [List.set_cons_zero]
          exact mem_allAssigns_cons_iff.mpr ⟨w, hk.symm ▸ hv, a', ha', rfl⟩
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          rw [List.set_cons_succ]
          exact mem_allAssigns_cons_iff.mpr ⟨w, hw, a', ih ha' hk, rfl⟩

/-- Membership in `allAssigns` is refined by writing a sub-domain at a
slot. -/
theorem mem_allAssigns_of_mem_set {ds : List Domain} {a : Assignment} {k : Nat}
    {x : Domain} (hsub : ∀ v ∈ x, v ∈ ds.getD k Dom.empty)
    (ha : a ∈ allAssigns (ds.set k x)) : a ∈ allAssigns ds := by
  induction ds generalizing k a with
  | nil =>
      have ha' : a = [] := by simpa [allAssigns] using ha
      subst ha'
      exact List.mem_singleton.mpr rfl
  | cons d rest ih =>
      cases k with
      | zero =>
          rw [List.set_cons_zero] at ha
          obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
          have hwd : w ∈ d := by simpa using hsub w hw
          exact mem_allAssigns_cons_iff.mpr ⟨w, hwd, a', ha', rfl⟩
      | succ k =>
          rw [List.set_cons_succ] at ha
          obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
          have hsub' : ∀ v ∈ x, v ∈ rest.getD k Dom.empty := by
            intro v hv
            have := hsub v hv
            simpa only [List.getD_cons_succ] using this
          exact mem_allAssigns_cons_iff.mpr ⟨w, hw, a', ih hsub' ha', rfl⟩

/-- Enum-level coverage of `pin`: the pinned child keeps exactly the
assignments of the parent that read the pinned value at the pinned slot. -/
theorem Frame.covers_pin_iff {f : Frame} {k : Nat} {v : Value} {d : Domain}
    (hd : f.doms[k]? = some d) (hv : v ∈ d) (a : Assignment) :
    (f.pin k v).covers a ↔ f.covers a ∧ a[k]? = some v := by
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  have hgetD : f.doms.getD k Dom.empty = d := by
    rw [List.getD_eq_getElem?_getD, hd]
    rfl
  constructor
  · intro hc
    have hfit : a.Fits (f.doms.set k (Dom.ofList [v])) := allAssigns_fits _ _ hc
    have hklt' : k < (f.doms.set k (Dom.ofList [v])).length := by rwa [List.length_set]
    obtain ⟨w, hw, hread⟩ := read_of_fits hfit hklt'
    rw [getD_set_self hklt] at hw
    have hwv : w = v := by simpa using hw
    refine ⟨mem_allAssigns_of_mem_set ?_ hc, ?_⟩
    · intro u hu
      rw [hgetD]
      have huv : u = v := by simpa using hu
      subst huv
      exact hv
    · rw [hread, hwv]
  · rintro ⟨hc, hread⟩
    exact mem_allAssigns_set_of_mem hc hread (by simp)

/-- Enum-level coverage of `retire`: the sibling keeps exactly the parent
assignments whose value at the retired slot lies in the sibling domain. -/
theorem Frame.covers_retire_iff {f : Frame} {k : Nat} {vs : Domain} {d : Domain}
    (hd : f.doms[k]? = some d) (hsub : ∀ v ∈ vs, v ∈ d) (a : Assignment) :
    (f.retire k vs).covers a ↔ f.covers a ∧ ∃ v ∈ vs, a[k]? = some v := by
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  constructor
  · intro hc
    have hfit : a.Fits (f.doms.set k vs) := allAssigns_fits _ _ hc
    have hklt' : k < (f.doms.set k vs).length := by rwa [List.length_set]
    obtain ⟨w, hw, hread⟩ := read_of_fits hfit hklt'
    rw [getD_set_self hklt] at hw
    refine ⟨mem_allAssigns_of_mem_set ?_ hc, w, hw, hread⟩
    intro u hu
    rw [List.getD_eq_getElem?_getD, hd]
    exact hsub u hu
  · rintro ⟨hc, v, hv, hread⟩
    exact mem_allAssigns_set_of_mem hc hread hv

/-- THE ARBITRARY-SLOT SPLIT (S0 §3.5 prints this as `covers_split_at`;
the prototype's name is `covers_pin_or_retire`): the parent's coverage is
exactly the union of the pinned child's coverage and the retired sibling's
coverage, at an ARBITRARY slot. Reused from `DecisionProto` under this
module's `Frame.covers` (the same membership denotation, definitionally):
the coverage-equivalence half of the `pin`/`retire` operation refinement. -/
theorem covers_pin_or_retire {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (a : Assignment) :
    f.covers a ↔ (f.pin k v).covers a ∨ (f.retire k vs).covers a :=
  DecisionProto.covers_pin_or_retire h a

/-- S0 §5 (M1) bridge at the empty prefix: the current positional head-split
`covers_split` is exactly the sparse `covers_pin_or_retire` of the
empty-prefix sparse frame `⟨(v :: vs) :: rest, []⟩` — the positional split
is the sparse `pin`/`retire` at the prefix-head slot. -/
theorem covers_split_iff_sparse_pin_or_retire {v : Value} {vs : Domain}
    {rest : List Domain} {a : Assignment} :
    PrefixCovers ((Dom.cons v vs) :: rest, []) a ↔
      Frame.covers ((⟨(Dom.cons v vs) :: rest, []⟩ : Frame).pin 0 v) a ∨
        Frame.covers ((⟨(Dom.cons v vs) :: rest, []⟩ : Frame).retire 0 vs) a :=
  ((Frame.covers_iff_FrameCovers (⟨(Dom.cons v vs) :: rest, []⟩ : Frame) a).symm).trans
    (covers_pin_or_retire (f := ⟨(Dom.cons v vs) :: rest, []⟩) (k := 0) (v := v)
      (vs := vs) (by
        show some (Dom.enum (Dom.cons v vs)) = some (v :: vs.enum)
        rw [Dom.enum_cons]) a)

/-- The sparse filter preserves exactly the assignments satisfying the
literal: enum-level coverage equivalence. -/
theorem Frame.covers_filterFrame_iff {l : Literal} {f g : Frame}
    (h : Frame.filterFrame l f = some g) (hsl : l.atom.slot < f.doms.length)
    (a : Assignment) :
    g.covers a ↔ f.covers a ∧ l.eval a = some true := by
  unfold Frame.filterFrame at h
  split at h
  · rename_i _ hd
    rw [List.getElem?_eq_none_iff] at hd
    omega
  · rename_i _ d hd
    split at h
    · rename_i _ hfil
      cases h
    · cases h
      constructor
      · intro hc
        have hfit : a.Fits (f.doms.set l.atom.slot (Dom.filterLitKeep l d)) :=
          allAssigns_fits _ _ hc
        have hklt' : l.atom.slot <
            (f.doms.set l.atom.slot (Dom.filterLitKeep l d)).length := by
          rwa [List.length_set]
        obtain ⟨w, hw, hread⟩ := read_of_fits hfit hklt'
        rw [getD_set_self hsl] at hw
        have hvw : l.valueHolds w = true := (Dom.mem_filterLitKeep_iff.mp hw).2
        refine ⟨mem_allAssigns_of_mem_set ?_ hc, (valueHolds_read hread).mp hvw⟩
        intro u hu
        have hud : u ∈ d := (Dom.mem_filterLitKeep_iff.mp hu).1
        rwa [List.getD_eq_getElem?_getD, hd]
      · rintro ⟨hc, hev⟩
        obtain ⟨w, hwd, hread⟩ := exists_read_of_covers hc hsl
        have hvw : l.valueHolds w = true := (valueHolds_read hread).mpr hev
        have hwd' : w ∈ d := by rwa [List.getD_eq_getElem?_getD, hd] at hwd
        exact mem_allAssigns_set_of_mem hc hread (Dom.mem_filterLitKeep_iff.mpr ⟨hwd', hvw⟩)

/-- When the sparse filter rejects, no covered assignment satisfies the
literal. -/
theorem Frame.covers_filterFrame_none {l : Literal} {f : Frame}
    (h : Frame.filterFrame l f = none) :
    ∀ a, f.covers a → l.eval a ≠ some true := by
  intro a hc hev
  unfold Frame.filterFrame at h
  split at h
  · cases h
  · rename_i _ d hd
    split at h
    · rename_i _ hfil
      have hklt : l.atom.slot < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
      obtain ⟨w, hwd, hread⟩ := exists_read_of_covers hc hklt
      have hwd' : w ∈ d := by
        rwa [List.getD_eq_getElem?_getD, hd] at hwd
      have hfilter : Dom.enum (d.filter l.valueHolds) = [] := by
        rw [Dom.enum_filter, ← Dom.enum_filterLitKeep]
        exact hfil
      have hfalse : ¬ l.valueHolds w = true :=
        (enum_filter_eq_nil_iff.mp hfilter) w hwd'
      have : l.valueHolds w = true := (valueHolds_read hread).mpr hev
      exact hfalse this
    · cases h

/-- Narrowing never changes the decision order: the sparse filter is a
narrowing of the box, not a decision. -/
theorem Frame.filterFrame_order {l : Literal} {f g : Frame}
    (h : Frame.filterFrame l f = some g) : g.order = f.order := by
  unfold Frame.filterFrame at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- Exact rejection criterion for the sparse filter. -/
theorem Frame.filterFrame_eq_none_iff (l : Literal) (f : Frame) :
    Frame.filterFrame l f = none ↔
      ∃ d : Domain, f.doms[l.atom.slot]? = some d ∧
        Dom.enum (d.filter l.valueHolds) = [] := by
  constructor
  · intro h
    unfold Frame.filterFrame at h
    split at h
    · cases h
    · rename_i _ d hd
      split at h
      · rename_i _ hfil
        refine ⟨d, hd, ?_⟩
        rw [Dom.enum_filter, ← Dom.enum_filterLitKeep]
        exact hfil
      · cases h
  · rintro ⟨d, hd, hfil⟩
    simp only [Frame.filterFrame, hd]
    rw [Dom.enum_filterLitKeep, ← Dom.enum_filter, hfil]

/-- Filtering an out-of-range slot is a no-op. -/
theorem filterSlot_eq_self_of_le_length (l : Literal) (ds : List Domain)
    (h : ds.length ≤ l.atom.slot) : filterSlot l ds = ds := by
  unfold filterSlot
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]
  exact List.set_eq_of_length_le h

/-- The positional `filterSlots` never acts after its offset passes the
literal's slot. -/
theorem filterSlots_eq_self_of_lt (l : Literal) :
    ∀ (ds : List Domain) (offset : Nat), l.atom.slot < offset → filterSlots l offset ds = ds := by
  intro ds
  induction ds with
  | nil => intro offset _; rfl
  | cons d rest ih =>
      intro offset h
      simp only [filterSlots]
      rw [if_neg (by omega), ih (offset + 1) (by omega)]

/-- The positional `filterSlots` at an offset at or below the literal's
slot is the absolute slot filter at the shifted index. -/
theorem filterSlots_eq_filterSlotAt (l : Literal) (ds : List Domain) (offset : Nat)
    (hle : offset ≤ l.atom.slot) :
    filterSlots l offset ds =
      ds.set (l.atom.slot - offset)
        (Dom.filterLitKeep l (ds.getD (l.atom.slot - offset) Dom.empty)) := by
  induction ds generalizing offset with
  | nil => simp [filterSlots, List.set]
  | cons d rest ih =>
      simp only [filterSlots]
      by_cases heq : offset = l.atom.slot
      · subst heq
        rw [if_pos rfl,
          filterSlots_eq_self_of_lt l rest (l.atom.slot + 1) (Nat.lt_succ_self _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.set_cons_zero]
      · have hlt : offset < l.atom.slot := by omega
        rw [if_neg heq, ih (offset + 1) (by omega)]
        rw [show l.atom.slot - offset = l.atom.slot - (offset + 1) + 1 by omega]
        simp only [List.set_cons_succ, List.getD_cons_succ]

/-- The current positional `filterSlots` at offset `0` is exactly the
sparse absolute-slot filter. -/
theorem filterSlots_zero_eq_filterSlot (l : Literal) (ds : List Domain) :
    filterSlots l 0 ds = filterSlot l ds := by
  rw [filterSlots_eq_filterSlotAt l ds 0 (Nat.zero_le _)]
  simp only [filterSlot, Nat.sub_zero]

/-- The positional filter on an empty prefix does not reject: it filters
the remaining domains at offset `0` (M2: the positional twin is
`prefixFilterFrame`). -/
theorem filterFrame_nil_eq (l : Literal) (ds : List Domain) :
    prefixFilterFrame l (ds, []) = some (filterSlots l 0 ds, []) := by
  simp [prefixFilterFrame]

/-- Enum-level coverage of the current `filterSlots` at offset `0`: the
filtered box contains exactly the assignments satisfying the literal. -/
theorem mem_allAssigns_filterSlots_iff {l : Literal} {ds : List Domain}
    {a : Assignment} (hsl : l.atom.slot < ds.length) :
    a ∈ allAssigns (filterSlots l 0 ds) ↔ a ∈ allAssigns ds ∧ l.eval a = some true := by
  rw [filterSlots_zero_eq_filterSlot]
  unfold filterSlot
  constructor
  · intro ha
    have hfit : a.Fits (ds.set l.atom.slot
        (Dom.filterLitKeep l (ds.getD l.atom.slot Dom.empty))) := allAssigns_fits _ _ ha
    have hklt' : l.atom.slot < (ds.set l.atom.slot
        (Dom.filterLitKeep l (ds.getD l.atom.slot Dom.empty))).length := by rwa [List.length_set]
    obtain ⟨w, hw, hread⟩ := read_of_fits hfit hklt'
    rw [getD_set_self hsl] at hw
    have hvw : l.valueHolds w = true := (Dom.mem_filterLitKeep_iff.mp hw).2
    exact ⟨mem_allAssigns_of_mem_set (fun v hv => (Dom.mem_filterLitKeep_iff.mp hv).1) ha,
      (valueHolds_read hread).mp hvw⟩
  · rintro ⟨ha, hev⟩
    obtain ⟨v, hvd, hread⟩ := exists_read_of_covers (f := ⟨ds, []⟩) ha hsl
    have hvw : l.valueHolds v = true := (valueHolds_read hread).mpr hev
    exact mem_allAssigns_set_of_mem ha hread (Dom.mem_filterLitKeep_iff.mpr ⟨hvd, hvw⟩)

/-- The sparse filter and the current positional
`filterFrame`/`filterSlots` at the empty prefix cover the same assignments:
the M2/M3 semantic bridge. -/
theorem filterSlots_covers_iff_filterFrame {l : Literal} {ds : List Domain}
    {a : Assignment} (hsl : l.atom.slot < ds.length) :
    PrefixCovers (filterSlots l 0 ds, []) a ↔
      ∃ g : Frame, Frame.filterFrame l ⟨ds, []⟩ = some g ∧ g.covers a := by
  have hbridge : PrefixCovers (filterSlots l 0 ds, []) a ↔
      a ∈ allAssigns (filterSlots l 0 ds) :=
    (DecisionProto.Frame.covers_iff_frameCovers ⟨filterSlots l 0 ds, []⟩ a).symm
  rw [hbridge, mem_allAssigns_filterSlots_iff hsl]
  have hgetD : ds.getD l.atom.slot Dom.empty = ds[l.atom.slot] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsl]
    rfl
  cases hfil : Dom.enum (Dom.filterLitKeep l (ds.getD l.atom.slot Dom.empty)) with
  | nil =>
      have hfil' : Dom.enum (Dom.filterLitKeep l (ds[l.atom.slot])) = [] := by
        rw [← hgetD]
        exact hfil
      have hnone : Frame.filterFrame l ⟨ds, []⟩ = none := by
        simp only [Frame.filterFrame, List.getElem?_eq_getElem hsl, hfil']
      constructor
      · rintro ⟨ha, hev⟩
        obtain ⟨v, hvd, hread⟩ := exists_read_of_covers (f := ⟨ds, []⟩) ha hsl
        have hvw : l.valueHolds v = true := (valueHolds_read hread).mpr hev
        refine absurd (Dom.mem_filterLitKeep_iff.mpr ⟨hvd, hvw⟩) ?_
        rw [DomainLike.mem_iff, domElems_eq_enum, hfil]
        simp
      · rintro ⟨g, hg, -⟩
        rw [hnone] at hg
        cases hg
  | cons v vs =>
      have hfil' : Dom.enum (Dom.filterLitKeep l (ds[l.atom.slot])) = v :: vs := by
        rw [← hgetD]
        exact hfil
      have hsome : Frame.filterFrame l ⟨ds, []⟩ =
          some { doms := ds.set l.atom.slot
                   (Dom.filterLitKeep l (ds[l.atom.slot])), order := [] } := by
        simp only [Frame.filterFrame, List.getElem?_eq_getElem hsl, hfil']
      constructor
      · rintro ⟨ha, hev⟩
        refine ⟨_, hsome, ?_⟩
        exact (Frame.covers_filterFrame_iff hsome hsl a).mpr ⟨ha, hev⟩
      · rintro ⟨g, hg, hcov⟩
        rw [hsome] at hg
        cases hg
        exact (Frame.covers_filterFrame_iff hsome hsl a).mp hcov

/-! ## §4 Decision/level/checkpoint vocabulary -/

/-- The slot decided at level `L` (1-indexed; `none` at the root). -/
def Frame.slotAtLevel (f : Frame) (L : Nat) : Option Nat :=
  if L = 0 then none else f.order[L - 1]?

/-- The root has no decided slot. -/
theorem Frame.slotAtLevel_zero (f : Frame) : f.slotAtLevel 0 = none := rfl

/-- The slot-at-level map, characterized. -/
theorem Frame.slotAtLevel_eq_some_iff {f : Frame} {L k : Nat} :
    f.slotAtLevel L = some k ↔ L ≠ 0 ∧ f.order[L - 1]? = some k := by
  unfold Frame.slotAtLevel
  by_cases h : L = 0
  · subst h
    simp
  · simp [h]

/-- The decision's slot is exactly the new level's slot. -/
theorem Frame.slotAtLevel_pin (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).slotAtLevel (f.level + 1) = some k := by
  rw [Frame.slotAtLevel_eq_some_iff]
  refine ⟨by omega, ?_⟩
  rw [show f.level + 1 - 1 = f.level by omega]
  rw [show (f.pin k v).order = f.order ++ [k] from DecisionProto.Frame.pin_order f k v]
  rw [show f.level = f.order.length from rfl]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- A decision opens exactly one new level. -/
theorem Frame.level_pin (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).level = f.level + 1 :=
  DecisionProto.Frame.pin_level f k v

/-- A retirement keeps the level. -/
theorem Frame.level_retire (f : Frame) (k : Nat) (vs : Domain) :
    (f.retire k vs).level = f.level := rfl

/-- The trail entry a decision records (S0 §3.3), on the ORIGINAL slot
index: the pinned value's literal at the new level, no reason. -/
def Frame.decisionEntry (f : Frame) (k : Nat) (v : Value) : Option TrailEntry :=
  (valueLiteral k v).map fun l =>
    { literal := l.norm, level := f.level + 1, reason := none }

/-- The decision entry, characterized. -/
theorem Frame.decisionEntry_eq_some_iff {f : Frame} {k : Nat} {v : Value}
    {e : TrailEntry} :
    f.decisionEntry k v = some e ↔
      ∃ l : Literal, valueLiteral k v = some l ∧
        e = { literal := l.norm, level := f.level + 1, reason := none } := by
  unfold Frame.decisionEntry
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨l, hl, he⟩
    exact ⟨l, hl, he.symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

/-- A decision entry opens the next level. -/
theorem Frame.decisionEntry_level {f : Frame} {k : Nat} {v : Value}
    {e : TrailEntry} (h : f.decisionEntry k v = some e) :
    e.level = f.level + 1 := by
  obtain ⟨l, -, rfl⟩ := Frame.decisionEntry_eq_some_iff.mp h
  rfl

/-- A decision entry carries no reason. -/
theorem Frame.decisionEntry_reason {f : Frame} {k : Nat} {v : Value}
    {e : TrailEntry} (h : f.decisionEntry k v = some e) : e.reason = none := by
  obtain ⟨l, -, rfl⟩ := Frame.decisionEntry_eq_some_iff.mp h
  rfl

/-- The literal form of a decision entry. -/
theorem Frame.decisionEntry_matches_literal {f : Frame} {k : Nat} {v : Value}
    {l : Literal} (hval : valueLiteral k v = some l) :
    f.decisionEntry k v =
      some { literal := l.norm, level := f.level + 1, reason := none } := by
  unfold Frame.decisionEntry
  rw [hval]
  rfl

/-- The sparse decision entry is exactly the trail entry the current
`BranchState.decide` appends (when levels agree). -/
theorem decisionEntry_decide {bs : BranchState leaf} {f : Frame} {k : Nat}
    {v : Value} {l : Literal} (hval : valueLiteral k v = some l)
    (hlev : bs.level = f.level) :
    (bs.decide l).trail =
        bs.trail ++ [{ literal := l.norm, level := f.level + 1, reason := none }] ∧
      f.decisionEntry k v =
        some { literal := l.norm, level := f.level + 1, reason := none } := by
  constructor
  · show bs.trail ++ [{ literal := l.norm, level := bs.level + 1, reason := none }] =
        bs.trail ++ [{ literal := l.norm, level := f.level + 1, reason := none }]
    rw [hlev]
  · exact Frame.decisionEntry_matches_literal hval

/-- The transport of a sparse checkpoint to the current
`DecisionCheckpoint` type: the frame is the empty-prefix positional
transport, the level and the caller-provided trail are kept. The trail
content (the canonical pins and their prefix law) is the M4 restoration
obligation and is therefore an explicit hypothesis here. -/
def toDecisionCheckpoint {leaf : Assignment → Bool}
    (cp : DecisionProto.Checkpoint) (trail : List TrailEntry) :
    DecisionCheckpoint leaf :=
  { level := cp.level, frame := ⟨cp.doms, cp.order⟩, trail := trail }

/-- CHECKPOINT TRANSPORT: a sparse `Checkpoint.Identifies` yields the
current `DecisionCheckpoint.Identifies` for the transported checkpoint and
the empty-prefix branch state, under the explicit trail-prefix law. The
descent conjunct is exactly S0's coverage-descent conjunct through the
`FrameCovers` bridge (no extra `WF` hypothesis is needed for this
direction; `WF` is used by the level/permutation vocabulary of §1). -/
theorem Checkpoint.identifies_toDecisionCheckpoint {cp : DecisionProto.Checkpoint}
    {f : Frame} (h : cp.Identifies f) {leaf : Assignment → Bool}
    {bs : BranchState leaf} (hframe : bs.frame = ⟨f.doms, f.order⟩)
    {trail : List TrailEntry}
    (htrail : ∃ mid : List TrailEntry,
      bs.trail = trail ++ mid ∧ ∀ e ∈ mid, cp.level ≤ e.level) :
    (toDecisionCheckpoint (leaf := leaf) cp trail).Identifies bs cp.level := by
  obtain ⟨-, hcov, -⟩ := h
  refine ⟨rfl, htrail, ?_⟩
  intro a ha
  rw [hframe] at ha
  exact hcov a ha

/-- Root instance of the checkpoint transport: the initial state (empty
prefix, empty trail) is identified by the transported self-checkpoint of
any frame at its own level. -/
theorem Checkpoint.identifies_init (f : Frame) (leaf : Assignment → Bool) :
    (toDecisionCheckpoint (leaf := leaf) (DecisionProto.Checkpoint.ofFrame f) []).Identifies
      (BranchState.init (leaf := leaf) ⟨f.doms, f.order⟩)
      (DecisionProto.Checkpoint.ofFrame f).level :=
  Checkpoint.identifies_toDecisionCheckpoint (DecisionProto.Checkpoint.identifies_self f) rfl
    ⟨[], by simp [BranchState.init], fun e he => by cases he⟩

/-- The checkpoint's level-to-slot ledger is the frame's truncated order:
`slotAtLevel` agrees with the frame at every level up to the checkpoint's. -/
theorem Checkpoint.slotAtLevel_eq {cp : DecisionProto.Checkpoint} {f : Frame}
    (h : cp.Identifies f) {L : Nat} (hL : L ≤ cp.level) :
    Frame.slotAtLevel ⟨cp.doms, cp.order⟩ L = f.slotAtLevel L := by
  obtain ⟨-, -, hord⟩ := h
  unfold Frame.slotAtLevel
  change (if L = 0 then none else cp.order[L - 1]?) =
    (if L = 0 then none else f.order[L - 1]?)
  rw [hord]
  by_cases h0 : L = 0
  · simp [h0]
  · have hlt' : L - 1 < cp.level := by omega
    simp only [h0, if_false, List.getElem?_take, hlt', if_true]

/-! ## §5 S0 progress facts (imported from `DecisionProto`, restated) -/

/-- PROGRESS (pin), sum measure. Reused from `DecisionProto` (§4): the S0
fact is imported, not reproved. -/
theorem mass_pin_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hne : vs.enum ≠ []) :
    (f.pin k v).mass < f.mass :=
  DecisionProto.mass_pin_lt h hne

/-- PROGRESS (retire), sum measure. Reused from `DecisionProto` (§4). -/
theorem mass_retire_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    (f.retire k vs).mass < f.mass :=
  DecisionProto.mass_retire_lt h

/-- PROGRESS (pin), decide-arm measure. Reused from `DecisionProto` (§4);
the nonempty-box hypothesis is the route's `FrameShape` guarantee. -/
theorem cost_pin_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hne : vs.enum ≠ [])
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) : (f.pin k v).cost < f.cost :=
  DecisionProto.cost_pin_lt h hne hall

/-- PROGRESS (retire), decide-arm measure. Reused from `DecisionProto` (§4). -/
theorem cost_retire_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.retire k vs).cost < f.cost :=
  DecisionProto.cost_retire_lt h hall

/-- PROGRESS (frontier): replacing a frame by its two strictly cheaper
children strictly decreases `frontierWeight = ∑ 3 ^ cost` — the sparse
replacement for the positional `frontierCost_expand` identity. Reused from
`DecisionProto` (§4). -/
theorem frontierWeight_split_lt {pending : List Frame} {parent child sibling : Frame}
    (h₁ : child.cost < parent.cost) (h₂ : sibling.cost < parent.cost) :
    frontierWeight (child :: sibling :: pending) <
      frontierWeight (parent :: pending) :=
  DecisionProto.frontierWeight_split_lt h₁ h₂

end LeanFzn.Solver.Propagation.SparseFrame
