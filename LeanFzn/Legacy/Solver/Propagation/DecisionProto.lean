/-
File: LeanFzn/Solver/Propagation/DecisionProto.lean

Purpose (PLAN tasks S0 + S1 prototype):
  A STANDALONE, UNWIRED prototype of the arbitrary-slot decision mechanism
  the S0 design document (`S0-decision-design.md`) recommends, with the S1
  minimum-cardinality variable-selection rule: a search frame whose
  remaining domains live at their ORIGINAL slot indices, plus the decision
  order that maps decision levels to slots. Nothing here is imported by any
  runtime module; the shared `BranchFrame` representation
  (`LeanFzn/Solver/Propagation/Frontier.lean`) is deliberately untouched.

  The prototype proves the S0/S1 acceptance core on the new mechanism:

  * `selectSlot` — THE S1 POLICY: among live (non-singleton) slots, minimum
    domain cardinality; ties by the smallest slot index; `none` when no
    live slot exists. `selectSlot_live`/`selectSlot_min`/`selectSlot_complete`/
    `selectSlot_none_iff` are its specification; `selectSlot_eq_of_min`
    (with `selectSlot_unique_min`) shows the tie rule determines the choice
    uniquely (a pure function of the box, no state).
  * `scanCost_eq_length` / `scanCost_le_length` and
    `cmpCost_le_liveCount` / `cmpCost_le_length` — the selection cost is
    statically bounded: one slot visit per slot, at most one key comparison
    per live slot.
  * `covers_pin_or_retire` + `allAssigns_set_split` — the branch is
    exhaustive at an arbitrary slot; `Frame.split_covers`/`Frame.split_min`
    are the selected-split forms;
  * `mass_pin_lt`/`mass_retire_lt` and `cost_pin_lt`/`cost_retire_lt` —
    strict progress of both children in the sum-of-lengths and
    `branchCost` measures, and `frontierWeight_split_lt` for the frontier
    weight the design freezes as the termination measure;
  * `covers_read` + `Frame.split_pin_read` — assignment reconstruction: any
    covered assignment reads a decided slot's recorded value at its
    ORIGINAL slot index (no output permutation);
  * `Checkpoint.identifies_self`/`identifies_pin`/`identifies_retire` and
    the `WF` facts — checkpoint/assignment/frame consistency under
    decisions, the sparse-frame analogue of
    `DecisionCheckpoint.Identifies` and `FrameDescendsFrom`.

  Design notes (frozen by S0/S1, see the design document):
  * `Frame.doms` is the FULL per-slot box; a decided slot holds its
    singleton. `Frame.Covers` is therefore `allAssigns`-membership, and
    `FrameCovers (f.doms, [])` is the shared name for the same set.
  * `Frame.order` records the decided slots oldest-first: decision level
    `L` is `order[L-1]`, so `order.length = level`. `pin` appends the
    selected slot; `retire` keeps the order (the sibling is not decided).
  * The selector is a pure function of the box: S2's per-conflict activity
    metadata belongs on the scheduler configuration, not on the frame.

Dependencies: LeanFzn.Solver.Propagation.FrontierSemantics (the shared
`allAssigns`/`FrameCovers` vocabulary) only. Restated locally (rather than
imported from the heavy compiler/UIP cones): `mem_allAssigns_length`,
`mem_allAssigns_read`.

No `sorry`/`admit`/`axiom`/`native_decide`, no proof escapes. Not wired.
-/
import LeanFzn.Solver.Propagation.FrontierSemantics

namespace LeanFzn.Solver.Propagation.DecisionProto
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

/-! ## §1 The sparse frame and its coverage -/

/-- The S0 sparse search frame: the full per-slot box (`doms`, indexed by
the ORIGINAL slot number; decided slots hold their singleton) and the
decision order (`order`, decided slots oldest-first). Decision levels are
1-indexed into `order`: level `L` decided `order[L-1]`.

M2: this is definitionally the shared scheduled structure
`LeanFzn.Solver.Propagation.BranchFrame` (declared in `Frontier.lean`), so
every S0/S1 theorem below applies to the scheduled frame directly — the
prototype name is kept for the standalone development. -/
abbrev Frame := LeanFzn.Solver.Propagation.BranchFrame

/-- The frame's current decision level: the number of decisions. -/
def Frame.level (f : Frame) : Nat := f.order.length

/-- Coverage of a sparse frame: the assignments enumerated by its full
per-slot box. This is the membership-based shared `FrameCovers`; the two
names denote the same proposition (`covers_iff_FrameCovers`). -/
def Frame.Covers (f : Frame) (a : Assignment) : Prop := a ∈ allAssigns f.doms

/-- Bridge to the shared sparse name: the sparse frame's coverage is the
shared `FrameCovers`. -/
theorem Frame.covers_iff_FrameCovers (f : Frame) (a : Assignment) :
    f.Covers a ↔ FrameCovers f a := Iff.rfl

/-- Bridge to the positional vocabulary: the sparse frame's coverage is the
`PrefixCovers` of the derived `(doms, [])` prefix frame (M2 retarget: the
positional type is `PrefixFrame`). -/
theorem Frame.covers_iff_frameCovers (f : Frame) (a : Assignment) :
    f.Covers a ↔ PrefixCovers (f.doms, []) a := by
  constructor
  · intro h
    exact ⟨a, h, (List.nil_append a).symm⟩
  · rintro ⟨tail, ht, heq⟩
    subst heq
    simpa [Frame.Covers] using ht

/-! ## §2 Decision legality: live slots and the policy hook -/

/-- A slot is LIVE when its domain is non-singleton: the exact legality
condition of a decision.  Stated on the box through the denotation: the
slot enumerates as `v :: vs.enum` with a nonempty tail.  (The compact
`Dom` need not be syntactically `Dom.cons`, so the enumeration is the
stable view the runtime split can always produce.) -/
def Live (ds : List Domain) (k : Nat) : Prop :=
  ∃ (v : Value) (vs : Domain), ds[k]?.map Dom.enum = some (v :: vs.enum) ∧ vs.enum ≠ []

/-- The frame-level legality predicate. -/
abbrev Frame.Live (f : Frame) (k : Nat) : Prop :=
  LeanFzn.Solver.Propagation.DecisionProto.Live f.doms k

/-- `2 ≤ d.length` is exactly "the enumeration has a head and a nonempty
tail". -/
theorem two_le_length_iff {d : Domain} :
    2 ≤ d.length ↔
      ∃ (v : Value) (vs : Domain), d.enum = v :: vs.enum ∧ vs.enum ≠ [] := by
  rw [Dom.length_eq_enum]
  cases hd : d.enum with
  | nil => simp
  | cons v vs =>
      cases vs with
      | nil => simp
      | cons w ws =>
          exact ⟨fun _ => ⟨v, Dom.ofList (w :: ws), by simp, by simp⟩,
            fun _ => by simp⟩

/-! ## §2 The S1 minimum-cardinality selector (PLAN S1)

The frozen policy hook `selectSlot` implements the S1 rule: among the
LIVE slots (non-singleton domains, `Live`), choose one with MINIMUM domain
cardinality; ties are broken by the SMALLEST slot index. If no live slot
exists the selector returns `none` (the S0 exhaustion behavior
unchanged). The scan is a single structural pass (`bestOf`), so the
slot-visit cost is exactly the number of slots (`scanCost_eq_length`),
and the candidate comparisons performed are at most the number of live
slots (`cmpCost_le_liveCount`). -/

/-- The domain cardinality read at a slot index (0 when out of range). -/
def Card (ds : List Domain) (j : Nat) : Nat := (ds.getD j Dom.empty).length

/-- `Card` at an in-range slot is the domain's length. -/
theorem Card_eq_of_getElem? {ds : List Domain} {j : Nat} {d : Domain}
    (h : ds[j]? = some d) : Card ds j = d.length := by
  rw [Card, List.getD_eq_getElem?_getD, h]
  rfl

/-- A slot is "big" (a decision candidate) when its domain has at least
two values: `Live` read through `Card`. -/
def BigSlot (ds : List Domain) (j : Nat) : Prop := 2 ≤ Card ds j

/-- `Live` and `BigSlot` are the same condition. -/
theorem live_iff_bigSlot {ds : List Domain} {j : Nat} :
    Live ds j ↔ BigSlot ds j := by
  constructor
  · rintro ⟨v, vs, hv, hne⟩
    rw [BigSlot]
    have hget : ds[j]?.map Dom.enum = some (v :: vs.enum) := hv
    cases hq : ds[j]? with
    | none => simp [hq] at hget
    | some d =>
        have hd : d.enum = v :: vs.enum := by simpa [hq] using hget
        rw [Card_eq_of_getElem? hq, Dom.length_eq_enum, hd]
        cases hvs : vs.enum with
        | nil => simp [hvs] at hne
        | cons w ws => simp
  · intro h
    rw [BigSlot, Card] at h
    have hne : (ds.getD j Dom.empty).enum ≠ [] := by
      intro hlen
      have h0 : (ds.getD j Dom.empty).length = 0 := by
        rw [Dom.length_eq_enum, hlen]
        rfl
      omega
    obtain ⟨v, vs, hget⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨v, Dom.ofList vs, ?_, ?_⟩
    · rw [Dom.enum_ofList]
      rw [List.getD_eq_getElem?_getD] at hget
      cases hj : ds[j]? with
      | none => simp [hj, Dom.enum_empty] at hget
      | some d =>
          have hget' : d.enum = v :: vs := by
            simpa [hj] using hget
          simpa using hget'
    · rw [Dom.enum_ofList]
      cases vs with
      | nil =>
          have hlen : (ds.getD j Dom.empty).length = 1 := by
            rw [Dom.length_eq_enum, hget]
            rfl
          omega
      | cons w ws => simp

/-- The S1 scan: the best `(cardinality, index)` key over the live slots
of the list (relative indices; shifted when the head is not live). One
structural pass per list cell. -/
def bestOf : List Domain → Option (Nat × Nat)
  | [] => none
  | d :: rest =>
      if 2 ≤ d.length then
        match bestOf rest with
        | none => some (d.length, 0)
        | some (c, i) =>
            if c < d.length then some (c, i + 1) else some (d.length, 0)
      else
        (bestOf rest).map fun p => (p.1, p.2 + 1)

/-- The scan's specification: either no slot is big, or the scan returns
the minimum `(cardinality, index)` key of the big slots (ties by index). -/
def BestSpec (ds : List Domain) : Prop :=
  (bestOf ds = none ∧ ∀ j, ¬ BigSlot ds j) ∨
    ∃ c i, bestOf ds = some (c, i) ∧ BigSlot ds i ∧ c = Card ds i ∧
      ∀ j, BigSlot ds j → c < Card ds j ∨ (c = Card ds j ∧ i ≤ j)

theorem bestOf_spec (ds : List Domain) : BestSpec ds := by
  induction ds with
  | nil =>
      left
      refine ⟨rfl, fun j => ?_⟩
      simp [BigSlot, Card, Dom.length_eq_enum, Dom.enum_empty]
  | cons d rest ih =>
      by_cases hd : 2 ≤ d.length
      · cases hr : bestOf rest with
        | none =>
            right
            refine ⟨d.length, 0, ?_, ?_, by simp [Card], ?_⟩
            · simp only [bestOf, if_pos hd, hr]
            · simpa [BigSlot, Card] using hd
            · intro j hj
              cases j with
              | zero => exact Or.inr ⟨by simp [Card], Nat.zero_le _⟩
              | succ k =>
                  have hk : BigSlot rest k := by simpa [BigSlot, Card] using hj
                  have hno : ∀ j, ¬ BigSlot rest j := by
                    rcases ih with ⟨-, hno⟩ | ⟨c, i, hs, -⟩
                    · exact hno
                    · rw [hr] at hs; cases hs
                  exact absurd hk (hno k)
        | some p =>
            obtain ⟨c, i⟩ := p
            have hfacts : BigSlot rest i ∧ c = Card rest i ∧
                ∀ j, BigSlot rest j →
                  c < Card rest j ∨ (c = Card rest j ∧ i ≤ j) := by
              rcases ih with ⟨hn, -⟩ | ⟨c', i', hs, hbig, hcard, hmin⟩
              · rw [hr] at hn; cases hn
              · rw [hr] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                exact ⟨hbig, hcard, hmin⟩
            obtain ⟨hbig, hcard, hmin⟩ := hfacts
            by_cases hlt : c < d.length
            · right
              refine ⟨c, i + 1, ?_, ?_, by simpa [Card] using hcard, ?_⟩
              · simp only [bestOf, if_pos hd, hr, if_pos hlt]
              · simpa [BigSlot, Card] using hbig
              · intro j hj
                cases j with
                | zero => exact Or.inl (by simpa [Card] using hlt)
                | succ k =>
                    have hk : BigSlot rest k := by simpa [BigSlot, Card] using hj
                    rcases hmin k hk with h1 | ⟨h2, h3⟩
                    · exact Or.inl (by simpa [Card] using h1)
                    · exact Or.inr ⟨by simpa [Card] using h2, by omega⟩
            · right
              refine ⟨d.length, 0, ?_, ?_, by simp [Card], ?_⟩
              · simp only [bestOf, if_pos hd, hr, if_neg hlt]
              · simpa [BigSlot, Card] using hd
              · intro j hj
                cases j with
                | zero => exact Or.inr ⟨by simp [Card], Nat.zero_le _⟩
                | succ k =>
                    have hk : BigSlot rest k := by simpa [BigSlot, Card] using hj
                    have hle : d.length ≤ c := by omega
                    rcases hmin k hk with h1 | ⟨h2, -⟩
                    · exact Or.inl (by simp only [Card, List.getD_cons_succ] at h1 ⊢; omega)
                    · by_cases hlt2 : d.length < Card rest k
                      · exact Or.inl (by simpa [Card] using hlt2)
                      · exact Or.inr ⟨by
                          simp only [Card, List.getD_cons_succ] at *
                          omega, Nat.zero_le _⟩
      · cases hr : bestOf rest with
        | none =>
            left
            refine ⟨?_, ?_⟩
            · simp only [bestOf, if_neg hd, hr]
              rfl
            · intro j hj
              cases j with
              | zero => exact absurd (by simpa [BigSlot, Card] using hj) hd
              | succ k =>
                  have hk : BigSlot rest k := by simpa [BigSlot, Card] using hj
                  have hno : ∀ j, ¬ BigSlot rest j := by
                    rcases ih with ⟨-, hno⟩ | ⟨c, i, hs, -⟩
                    · exact hno
                    · rw [hr] at hs; cases hs
                  exact hno k hk
        | some p =>
            obtain ⟨c, i⟩ := p
            have hfacts : BigSlot rest i ∧ c = Card rest i ∧
                ∀ j, BigSlot rest j →
                  c < Card rest j ∨ (c = Card rest j ∧ i ≤ j) := by
              rcases ih with ⟨hn, -⟩ | ⟨c', i', hs, hbig, hcard, hmin⟩
              · rw [hr] at hn; cases hn
              · rw [hr] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨rfl, rfl⟩ := hs
                exact ⟨hbig, hcard, hmin⟩
            obtain ⟨hbig, hcard, hmin⟩ := hfacts
            right
            refine ⟨c, i + 1, ?_, ?_, by simpa [Card] using hcard, ?_⟩
            · simp only [bestOf, if_neg hd, hr, Option.map_some]
            · simpa [BigSlot, Card] using hbig
            · intro j hj
              cases j with
              | zero => exact absurd (by simpa [BigSlot, Card] using hj) hd
              | succ k =>
                  have hk : BigSlot rest k := by simpa [BigSlot, Card] using hj
                  rcases hmin k hk with h1 | ⟨h2, h3⟩
                  · exact Or.inl (by simpa [Card] using h1)
                  · exact Or.inr ⟨by simpa [Card] using h2, by omega⟩

/-- The scan's positive fact, extracted from `bestOf_spec`. -/
theorem bestOf_some_spec {ds : List Domain} {c i : Nat}
    (h : bestOf ds = some (c, i)) :
    BigSlot ds i ∧ c = Card ds i ∧
      ∀ j, BigSlot ds j → c < Card ds j ∨ (c = Card ds j ∧ i ≤ j) := by
  rcases bestOf_spec ds with ⟨hnone, -⟩ | ⟨c', i', hs, hbig, hcard, hmin⟩
  · rw [h] at hnone; cases hnone
  · rw [h] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hbig, hcard, hmin⟩

/-- The scan's negative fact, extracted from `bestOf_spec`. -/
theorem bestOf_none_spec {ds : List Domain} (h : bestOf ds = none) :
    ∀ j, ¬ BigSlot ds j := by
  rcases bestOf_spec ds with ⟨-, hno⟩ | ⟨c, i, hs, -⟩
  · exact hno
  · rw [h] at hs; cases hs

/-- THE S1 POLICY HOOK (minimum-cardinality variable selection): among the
live slots, minimum domain cardinality; ties by the smallest slot index;
`none` when no live slot exists. A pure function of the box: no state. -/
def selectSlot (ds : List Domain) : Option Nat := (bestOf ds).map Prod.snd

/-- Every selected slot is live: decision legality. -/
theorem selectSlot_live : ∀ {ds : List Domain} {k : Nat},
    selectSlot ds = some k → Live ds k := by
  intro ds k h
  rw [selectSlot] at h
  cases hb : bestOf ds with
  | none => simp [hb] at h
  | some p =>
      obtain ⟨c, i⟩ := p
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact live_iff_bigSlot.mpr (bestOf_some_spec hb).1

/-- THE S1 RULE, precisely: the selected slot is live, has minimum
cardinality among live slots, and wins ties by the smallest index. -/
theorem selectSlot_min {ds : List Domain} {k : Nat}
    (h : selectSlot ds = some k) :
    Live ds k ∧ ∀ j, Live ds j →
      Card ds k < Card ds j ∨ (Card ds k = Card ds j ∧ k ≤ j) := by
  rw [selectSlot] at h
  cases hb : bestOf ds with
  | none => simp [hb] at h
  | some p =>
      obtain ⟨c, i⟩ := p
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hbig, hcard, hmin⟩ := bestOf_some_spec hb
      refine ⟨live_iff_bigSlot.mpr hbig, ?_⟩
      intro j hj
      rw [← hcard]
      exact hmin j (live_iff_bigSlot.mp hj)

/-- A live slot is selected whenever one exists: the selection cannot
miss a splittable domain. -/
theorem selectSlot_complete : ∀ {ds : List Domain},
    (∃ k, Live ds k) → ∃ k, selectSlot ds = some k := by
  intro ds hl
  cases hb : bestOf ds with
  | none =>
      obtain ⟨k, hk⟩ := hl
      exact absurd (live_iff_bigSlot.mp hk) (bestOf_none_spec hb k)
  | some p =>
      obtain ⟨c, i⟩ := p
      exact ⟨i, by rw [selectSlot, hb]; rfl⟩

/-- No live slot means selection is exhausted: the negative half of the
selection specification. -/
theorem selectSlot_none_iff {ds : List Domain} :
    selectSlot ds = none ↔ ¬ ∃ k, Live ds k := by
  constructor
  · intro h hlive
    obtain ⟨k, hk⟩ := selectSlot_complete hlive
    rw [h] at hk
    cases hk
  · intro h
    cases hb : bestOf ds with
    | none => rw [selectSlot, hb]; rfl
    | some p =>
        obtain ⟨c, i⟩ := p
        exact absurd ⟨i, live_iff_bigSlot.mpr (bestOf_some_spec hb).1⟩ h

/-! ### Determinism and the tie rule -/

/-- The tie-rule key of a slot: `(cardinality, slot index)`. -/
def SlotKey (ds : List Domain) (j : Nat) : Nat × Nat := (Card ds j, j)

/-- Lexicographic `≤` on tie-rule keys. -/
def KeyLE (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- The key order is antisymmetric: equal keys are equal pairs. -/
theorem KeyLE_antisymm {a b : Nat × Nat} (hab : KeyLE a b) (hba : KeyLE b a) :
    a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [KeyLE] at hab hba
  have h1 : a1 = b1 := by omega
  have h2 : a2 = b2 := by omega
  rw [h1, h2]

/-- The selector returns the minimum key among live slots. -/
theorem selectSlot_min_key {ds : List Domain} {k : Nat}
    (h : selectSlot ds = some k) :
    Live ds k ∧ ∀ j, Live ds j → KeyLE (SlotKey ds k) (SlotKey ds j) := by
  obtain ⟨hl, hmin⟩ := selectSlot_min h
  exact ⟨hl, fun j hj => hmin j hj⟩

/-- DETERMINISM / UNIQUENESS UNDER THE TIE RULE: any live slot that is
minimum for the `(cardinality, index)` key is exactly the selected one.
So the tie rule determines the choice, and the selector — a pure function
of the box — admits no second answer. -/
theorem selectSlot_eq_of_min {ds : List Domain} {k : Nat} (hk : Live ds k)
    (hmin : ∀ j, Live ds j → KeyLE (SlotKey ds k) (SlotKey ds j)) :
    selectSlot ds = some k := by
  obtain ⟨i, hi⟩ := selectSlot_complete ⟨k, hk⟩
  have hik : KeyLE (SlotKey ds i) (SlotKey ds k) :=
    (selectSlot_min_key hi).2 k hk
  have hki : KeyLE (SlotKey ds k) (SlotKey ds i) :=
    hmin i (selectSlot_live hi)
  have heq : SlotKey ds i = SlotKey ds k := KeyLE_antisymm hik hki
  have hik' : i = k := by simpa [SlotKey] using congrArg Prod.snd heq
  rw [← hik']
  exact hi

/-- Two live slots that both satisfy the tie rule are equal. -/
theorem selectSlot_unique_min {ds : List Domain} {k k' : Nat}
    (hk : Live ds k) (hk' : Live ds k')
    (hmink : ∀ j, Live ds j → KeyLE (SlotKey ds k) (SlotKey ds j))
    (hmink' : ∀ j, Live ds j → KeyLE (SlotKey ds k') (SlotKey ds j)) :
    k = k' := by
  have h1 := selectSlot_eq_of_min hk hmink
  have h2 := selectSlot_eq_of_min hk' hmink'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### Selection cost (statically bounded) -/

/-- The selector's slot scan: one visit per list cell (the implementation
`bestOf` recurses exactly once per `d :: rest`; the measure is
proof-only). -/
def scanCost : List Domain → Nat
  | [] => 0
  | _ :: rest => 1 + scanCost rest

/-- The scan visits every slot exactly once. -/
theorem scanCost_eq_length (ds : List Domain) : scanCost ds = ds.length := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
      simp only [scanCost, ih, List.length_cons]
      omega

/-- COST BOUND: the selection scan never visits more than the number of
slots (it visits exactly that many; no early exit, no second pass). -/
theorem scanCost_le_length (ds : List Domain) : scanCost ds ≤ ds.length :=
  Nat.le_of_eq (scanCost_eq_length ds)

/-- Live slots: the candidates the scan compares. -/
def liveCount : List Domain → Nat
  | [] => 0
  | d :: rest => (if 2 ≤ d.length then 1 else 0) + liveCount rest

theorem liveCount_le_length (ds : List Domain) : liveCount ds ≤ ds.length := by
  induction ds with
  | nil => simp [liveCount]
  | cons d rest ih =>
      by_cases hd : 2 ≤ d.length
      · simp only [liveCount, if_pos hd, List.length_cons]
        omega
      · simp only [liveCount, if_neg hd, List.length_cons]
        omega

/-- The number of candidate-key comparisons the scan performs: one per
live slot whose suffix still contains a candidate. -/
def cmpCost : List Domain → Nat
  | [] => 0
  | d :: rest =>
      (if 2 ≤ d.length then
        (match bestOf rest with | none => 0 | some _ => 1) else 0) + cmpCost rest

/-- COMPARISON BOUND: the scan compares at most one key per live slot, so
the comparison count is bounded by the live count (and hence by the
number of slots). -/
theorem cmpCost_le_liveCount (ds : List Domain) : cmpCost ds ≤ liveCount ds := by
  induction ds with
  | nil => simp [cmpCost, liveCount]
  | cons d rest ih =>
      by_cases hd : 2 ≤ d.length
      · cases hp : bestOf rest with
        | none =>
            simp only [cmpCost, liveCount, if_pos hd, hp]
            omega
        | some p =>
            simp only [cmpCost, liveCount, if_pos hd, hp]
            omega
      · simp only [cmpCost, liveCount, if_neg hd]
        omega

theorem cmpCost_le_length (ds : List Domain) : cmpCost ds ≤ ds.length :=
  Nat.le_trans (cmpCost_le_liveCount ds) (liveCount_le_length ds)

/-! ## §3 Splitting: pin child, retired sibling, exhaustiveness -/

/-- Pin the selected slot `k` to `v`: the decision child. The decided
slot holds the singleton `[v]`; the decision order grows by `k`. -/
def Frame.pin (f : Frame) (k : Nat) (v : Value) : Frame :=
  { doms := f.doms.set k (Dom.ofList [v]), order := f.order ++ [k] }

/-- Retire the value `v` from slot `k`: the sibling alternative, whose
domain is the old tail `vs` (typically nonempty: the sibling is pushed
only for live slots). The decision order is unchanged. -/
def Frame.retire (f : Frame) (k : Nat) (vs : Domain) : Frame :=
  { f with doms := f.doms.set k vs }

@[simp] theorem Frame.pin_doms (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).doms = f.doms.set k (Dom.ofList [v]) := rfl

@[simp] theorem Frame.pin_order (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).order = f.order ++ [k] := rfl

@[simp] theorem Frame.retire_doms (f : Frame) (k : Nat) (vs : Domain) :
    (f.retire k vs).doms = f.doms.set k vs := rfl

@[simp] theorem Frame.retire_order (f : Frame) (k : Nat) (vs : Domain) :
    (f.retire k vs).order = f.order := rfl

/-- The decision opens exactly one new level. -/
theorem Frame.pin_level (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).level = f.level + 1 := by
  simp [Frame.level]

/-- The decision's slot is exactly the new level's slot. -/
theorem Frame.slotAtLevel_pin (f : Frame) (k : Nat) (v : Value) :
    (f.pin k v).order[f.level]? = some k := by
  simp [Frame.level]

/-- Membership decomposition of `allAssigns` at the head.  The proof is the
shared one in `FrontierSemantics`; the local name keeps the standalone
development self-documenting. -/
theorem mem_allAssigns_cons_iff {d : Domain} {rest : List Domain}
    {a : Assignment} :
    a ∈ allAssigns (d :: rest) ↔
      ∃ v ∈ d, ∃ a' ∈ allAssigns rest, a = v :: a' :=
  LeanFzn.Solver.Propagation.mem_allAssigns_cons_iff

/-- THE ARBITRARY-SLOT SPLIT (enumeration view): the selected slot's
denotation is `v :: vs.enum`; the parent's assignments split into the pinned
child (`Dom.ofList [v]` at `k`) and the retired sibling (`vs` at `k`). -/
theorem allAssigns_set_split {ds : List Domain} {k : Nat} {v : Value}
    {vs : Domain} (h : ds[k]?.map Dom.enum = some (v :: vs.enum))
    (a : Assignment) :
    a ∈ allAssigns ds ↔
      a ∈ allAssigns (ds.set k (Dom.ofList [v])) ∨
        a ∈ allAssigns (ds.set k vs) :=
  LeanFzn.Solver.Propagation.allAssigns_set_split h a

/-- THE BRANCH IS EXHAUSTIVE: the parent's coverage is exactly the union
of the pinned child's and the retired sibling's coverage. -/
theorem covers_pin_or_retire {f : Frame} {k : Nat} {v : Value}
    {vs : Domain} (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (a : Assignment) :
    f.Covers a ↔ (f.pin k v).Covers a ∨ (f.retire k vs).Covers a := by
  rw [Frame.Covers, Frame.Covers, Frame.Covers, Frame.pin_doms,
    Frame.retire_doms]
  exact allAssigns_set_split h a

/-- Search-completeness shape: a leaf solution of the parent survives in
one of the two children. -/
theorem exists_leaf_child {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    {leaf : Assignment → Bool}
    (hfind : ∃ a, f.Covers a ∧ leaf a = true) :
    (∃ a, (f.pin k v).Covers a ∧ leaf a = true) ∨
      (∃ a, (f.retire k vs).Covers a ∧ leaf a = true) := by
  obtain ⟨a, hc, hl⟩ := hfind
  rcases (covers_pin_or_retire h a).mp hc with h' | h'
  · exact Or.inl ⟨a, h', hl⟩
  · exact Or.inr ⟨a, h', hl⟩

/-- One decision step: the selected slot, its value, and the sibling
domain. `none` when no live slot exists (the frame is exhausted). -/
def Frame.split (f : Frame) : Option (Nat × Value × Domain) :=
  match selectSlot f.doms with
  | none => none
  | some k =>
      match f.doms[k]? with
      | some d =>
          match Dom.enum d with
          | [] => none
          | v :: vs => some (k, v, Dom.ofList vs)
      | none => none

/-- The split data is exactly the selected live slot's enumeration head. -/
theorem Frame.split_spec {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) :
    f.doms[k]?.map Dom.enum = some (v :: vs.enum) := by
  unfold Frame.split at h
  cases hs : selectSlot f.doms with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hd' : Dom.enum d with
          | nil => simp [hd, hd'] at h
          | cons w ws =>
              simp only [hd, hd', Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp [hd, hd']

/-- The slot a split selects. -/
theorem Frame.split_slot {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) : selectSlot f.doms = some k := by
  unfold Frame.split at h
  cases hs : selectSlot f.doms with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hd' : Dom.enum d with
          | nil => simp [hd, hd'] at h
          | cons w ws =>
              simp only [hd, hd', Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -, -⟩ := h
              rfl

/-- The split's sibling domain is nonempty (only live slots split). -/
theorem Frame.split_live {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) : vs.enum ≠ [] := by
  have hs : selectSlot f.doms = some k := Frame.split_slot h
  obtain ⟨v', vs', hv', hne'⟩ := selectSlot_live hs
  have hspec := Frame.split_spec h
  rw [hspec] at hv'
  have hvs : vs.enum = vs'.enum := (List.cons.inj (Option.some.inj hv')).2
  intro hnil
  exact hne' (hvs ▸ hnil)

/-- The S1 rule at the selected split: the split's slot is live, has
minimum cardinality among live slots, and wins ties by smallest index. -/
theorem Frame.split_min {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) :
    f.Live k ∧ ∀ j, f.Live j →
      Card f.doms k < Card f.doms j ∨
        (Card f.doms k = Card f.doms j ∧ k ≤ j) :=
  selectSlot_min (Frame.split_slot h)

/-- Exhaustiveness at the selected split (the S1 decision covers the
parent). -/
theorem Frame.split_covers {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) (a : Assignment) :
    f.Covers a ↔ (f.pin k v).Covers a ∨ (f.retire k vs).Covers a :=
  covers_pin_or_retire (Frame.split_spec h) a

/-- A frame with a live slot always admits a split: selection completeness
through the S1 selector. -/
theorem Frame.split_complete {f : Frame} (hl : ∃ k, f.Live k) :
    ∃ k v vs, f.split = some (k, v, vs) := by
  obtain ⟨k, hk⟩ := selectSlot_complete hl
  obtain ⟨v, vs, hv, -⟩ := selectSlot_live hk
  refine ⟨k, v, Dom.ofList vs.enum, ?_⟩
  unfold Frame.split
  cases hd : f.doms[k]? with
  | none =>
      simp only [hk, hd] at hv
      simp at hv
  | some d =>
      simp only [hk, hd] at hv ⊢
      have hv' : Dom.enum d = v :: vs.enum := by simpa using hv
      rw [hv']

/-! ## §4 Progress: the decreasing measures -/

/-- Extract the selected domain from an enumeration-map hypothesis. -/
private theorem exists_getElem?_of_map_eq_some {ds : List Domain} {k : Nat}
    {v : Value} {vs : Domain}
    (h : ds[k]?.map Dom.enum = some (v :: vs.enum)) :
    ∃ d : Domain, ds[k]? = some d ∧ d.enum = v :: vs.enum := by
  cases hd : ds[k]? with
  | none => simp [hd] at h
  | some d => exact ⟨d, rfl, by simpa [hd] using h⟩

/-- Sum-of-lengths measure of a box (the propagation-style measure). -/
def sumMass (ds : List Domain) : Nat := (ds.map fun d => d.length).sum

/-- The frame's `sumMass` (agrees with the shared `Frame.mass` of the
derived `(doms, [])` prefix frame). -/
def Frame.mass (f : Frame) : Nat := sumMass f.doms

/-- Strict decrease of a slot-wise shrinking replacement. -/
theorem sumMass_set_lt {ds : List Domain} {k : Nat} {d x : Domain}
    (h : ds[k]? = some d) (hlt : x.length < d.length) :
    sumMass (ds.set k x) < sumMass ds := by
  induction ds generalizing k with
  | nil => simp at h
  | cons d₀ rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [List.set_cons_zero, sumMass, List.map_cons, List.sum_cons]
          omega
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hih : ((rest.set k x).map (fun d => d.length)).sum <
              ((rest.map (fun d => d.length)).sum) := by
            simpa [sumMass] using ih h
          simp only [List.set_cons_succ, sumMass, List.map_cons, List.sum_cons]
          omega

/-- PROGRESS (pin): the pinned child strictly decreases the sum measure. -/
theorem mass_pin_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hne : vs.enum ≠ []) :
    (f.pin k v).mass < f.mass := by
  obtain ⟨d, hd, hden⟩ := exists_getElem?_of_map_eq_some h
  have hpos : 0 < vs.enum.length := List.length_pos_iff.mpr hne
  have h1 : (Dom.ofList [v]).length = 1 := by simp
  have h2 : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hden]
    simp only [List.length_cons]
  have hlt : (Dom.ofList [v]).length < d.length := by
    rw [h1, h2]
    omega
  simpa [Frame.pin_doms, Frame.mass] using sumMass_set_lt hd hlt

/-- PROGRESS (retire): the retired sibling strictly decreases the sum
measure. -/
theorem mass_retire_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    (f.retire k vs).mass < f.mass := by
  obtain ⟨d, hd, hden⟩ := exists_getElem?_of_map_eq_some h
  have h2 : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hden]
    simp only [List.length_cons]
  have hlt : vs.length < d.length := by
    rw [Dom.length_eq_enum, h2]
    omega
  simpa [Frame.retire_doms, Frame.mass] using sumMass_set_lt hd hlt

/-- The per-frame cost the design freezes for the decide arm: the shared
positional `branchCost` read on the FULL box in original slot order (the
measure is proof-only; the frame keeps no order of its own). -/
def Frame.cost (f : Frame) : Nat := branchCost f.doms

/-- Strict decrease of `branchCost` under a slot-wise shrinking
replacement, provided every domain of the box is nonempty (the route's
`FrameShape` ensures nonempty domains; an empty prefix slot makes the box
itself exhausted and no decision fires). -/
theorem branchCost_set_lt {ds : List Domain} {k : Nat} {d x : Domain}
    (h : ds[k]? = some d) (hlt : x.length < d.length)
    (hne : ∀ e ∈ ds, e.enum ≠ []) :
    branchCost (ds.set k x) < branchCost ds := by
  induction ds generalizing k with
  | nil => simp at h
  | cons d₀ rest ih =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [List.set_cons_zero, branchCost]
          exact Nat.add_lt_add_left
            (Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos _)) 1
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hd₀ : d₀.enum ≠ [] := hne d₀ List.mem_cons_self
          have hpos : 0 < d₀.length := by
            rw [Dom.length_eq_enum]
            exact List.length_pos_iff.mpr hd₀
          have hrest := ih h (fun e he => hne e (List.mem_cons_of_mem _ he))
          simp only [List.set_cons_succ, branchCost]
          exact Nat.add_lt_add_left
            (Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hrest 1) hpos) 1

/-- PROGRESS (pin), decide-arm measure. -/
theorem cost_pin_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hne : vs.enum ≠ []) (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.pin k v).cost < f.cost := by
  obtain ⟨d, hd, hden⟩ := exists_getElem?_of_map_eq_some h
  have hpos : 0 < vs.enum.length := List.length_pos_iff.mpr hne
  have h1 : (Dom.ofList [v]).length = 1 := by simp
  have h2 : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hden]
    simp only [List.length_cons]
  have hlt : (Dom.ofList [v]).length < d.length := by
    rw [h1, h2]
    omega
  simpa [Frame.pin_doms, Frame.cost] using branchCost_set_lt hd hlt hall

/-- PROGRESS (retire), decide-arm measure. -/
theorem cost_retire_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.retire k vs).cost < f.cost := by
  obtain ⟨d, hd, hden⟩ := exists_getElem?_of_map_eq_some h
  have h2 : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hden]
    simp only [List.length_cons]
  have hlt : vs.length < d.length := by
    rw [Dom.length_eq_enum, h2]
    omega
  simpa [Frame.retire_doms, Frame.cost] using branchCost_set_lt hd hlt hall

/-- Frontier weight: the strictly decreasing stack measure. Each frame
contributes `3 ^ cost`; a split replaces `3^P` by `3^P₁ + 3^P₂` with both
children strictly cheaper, and `2·3^(P-1) < 3^P`. -/
def frontierWeight (pending : List Frame) : Nat :=
  (pending.map fun f => 3 ^ f.cost).sum

/-- PROGRESS (frontier): replacing a frame by its two strictly cheaper
children strictly decreases the frontier weight. This is the sparse-frame
replacement for the positional `frontierCost_expand` identity. -/
theorem frontierWeight_split_lt {pending : List Frame}
    {parent child sibling : Frame}
    (h₁ : child.cost < parent.cost) (h₂ : sibling.cost < parent.cost) :
    frontierWeight (child :: sibling :: pending) <
      frontierWeight (parent :: pending) := by
  have hP : parent.cost = (parent.cost - 1) + 1 := by omega
  have hchild : 3 ^ child.cost ≤ 3 ^ (parent.cost - 1) :=
    Nat.pow_le_pow_right (n := 3) (i := child.cost) (j := parent.cost - 1)
      (by decide) (by omega)
  have hsibling : 3 ^ sibling.cost ≤ 3 ^ (parent.cost - 1) :=
    Nat.pow_le_pow_right (n := 3) (i := sibling.cost) (j := parent.cost - 1)
      (by decide) (by omega)
  have hXpos : 0 < 3 ^ (parent.cost - 1) := Nat.pow_pos (by decide)
  simp only [frontierWeight, List.map_cons, List.sum_cons]
  rw [hP, Nat.pow_succ]
  omega

/-! ## §5 Assignment reconstruction and checkpoint consistency -/

/-- Membership in `allAssigns` fixes the assignment's length (restated
locally; the shared copy lives in the compiler proof cone). -/
theorem mem_allAssigns_length : ∀ (ds : List Domain) (a : Assignment),
    a ∈ allAssigns ds → a.length = ds.length := by
  intro ds
  induction ds with
  | nil =>
      intro a h
      simpa [allAssigns] using h
  | cons d rest ih =>
      intro a h
      obtain ⟨v, hv, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp h
      simp [ih a' ha']

/-- ASSIGNMENT RECONSTRUCTION (read): a covered assignment reads the
recorded value at every slot whose domain is a singleton — in particular
at every decided slot. The witness therefore stays in the problem's
ORIGINAL slot order; no output permutation is needed. -/
theorem mem_allAssigns_read : ∀ (ds : List Domain) (a : Assignment),
    a ∈ allAssigns ds → ∀ {k : Nat} {v : Value},
      ds[k]? = some (Dom.ofList [v]) → a[k]? = some v := by
  intro ds
  induction ds with
  | nil => intro a h k v hk; simp at hk
  | cons d rest ih =>
      intro a h k v hk
      obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp h
      cases k with
      | zero =>
          have : d = Dom.ofList [v] := by simpa using hk
          subst this
          have hwv : w = v := by simpa using hw
          subst hwv
          rfl
      | succ k =>
          have hk' : rest[k]? = some (Dom.ofList [v]) := by simpa using hk
          simpa using ih a' ha' hk'

/-- Frame-level reading: a covered assignment reads the decided slot's
value. -/
theorem covers_read {f : Frame} {a : Assignment} (h : f.Covers a)
    {k : Nat} {v : Value} (hk : f.doms[k]? = some (Dom.ofList [v])) :
    a[k]? = some v :=
  mem_allAssigns_read f.doms a h hk

/-- OUTPUT RECONSTRUCTION at the selected split: the pinned child's
covered assignment reads the chosen value at the ORIGINAL slot index
`k` (the witness is never reordered). -/
theorem Frame.split_pin_read {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    {a : Assignment} (h : f.split = some (k, v, vs))
    (ha : (f.pin k v).Covers a) : a[k]? = some v := by
  obtain ⟨d, hd, -⟩ := exists_getElem?_of_map_eq_some (Frame.split_spec h)
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  exact covers_read ha (List.getElem?_set_self hklt)

/-- Strict progress at the selected split, sum measure (both children). -/
theorem Frame.split_mass_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs)) :
    (f.pin k v).mass < f.mass ∧ (f.retire k vs).mass < f.mass :=
  ⟨mass_pin_lt (Frame.split_spec h) (Frame.split_live h),
   mass_retire_lt (Frame.split_spec h)⟩

/-- Strict progress at the selected split, decide-arm cost (both children;
nonempty-box route shape as in `cost_pin_lt`). -/
theorem Frame.split_cost_lt {f : Frame} {k : Nat} {v : Value} {vs : Domain}
    (h : f.split = some (k, v, vs))
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.pin k v).cost < f.cost ∧ (f.retire k vs).cost < f.cost :=
  ⟨cost_pin_lt (Frame.split_spec h) (Frame.split_live h) hall,
   cost_retire_lt (Frame.split_spec h) hall⟩

/-- A checkpoint: the frame's snapshot at a decision level — level, box,
and decision order. -/
structure Checkpoint where
  level : Nat
  doms : List Domain
  order : List Nat

/-- The checkpoint of a frame itself. -/
def Checkpoint.ofFrame (f : Frame) : Checkpoint :=
  { level := f.level, doms := f.doms, order := f.order }

/-- CHECKPOINT CONSISTENCY (the sparse-frame analogue of
`DecisionCheckpoint.Identifies` with `FrameDescendsFrom`): the checkpoint
level is at or below the frame's, the frame's coverage descends to the
checkpoint's box, and the checkpoint's decision order is the frame's order
truncated at that level — the level-to-slot ledger a restore reads. -/
def Checkpoint.Identifies (cp : Checkpoint) (f : Frame) : Prop :=
  cp.level ≤ f.level ∧
  (∀ a, f.Covers a → a ∈ allAssigns cp.doms) ∧
  cp.order = f.order.take cp.level

/-- A frame's own checkpoint identifies it. -/
theorem Checkpoint.identifies_self (f : Frame) :
    (Checkpoint.ofFrame f).Identifies f := by
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro a ha; exact ha
  · simp [Checkpoint.ofFrame, Frame.level]

/-- CHECKPOINT CONSISTENCY (decision step): deciding a fresh slot keeps
every checkpoint identifying the branch; the new level's slot is recorded
in the order, so the level-to-slot map extends by exactly the new slot. -/
theorem Checkpoint.identifies_pin {cp : Checkpoint} {f : Frame}
    (h : cp.Identifies f) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    cp.Identifies (f.pin k v) := by
  obtain ⟨hlev, hcov, hord⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Frame.pin_order, Frame.level, List.length_append,
      List.length_singleton] at hlev ⊢
    omega
  · intro a ha
    exact hcov a ((allAssigns_set_split hk a).mpr (Or.inl ha))
  · rw [hord]
    have hle : cp.level ≤ f.order.length := by
      simpa only [Frame.level] using hlev
    exact (List.take_append_of_le_length (l₁ := f.order) (l₂ := [k]) hle).symm

/-- CHECKPOINT CONSISTENCY (retirement step): retiring a sibling value
keeps every checkpoint identifying the branch. -/
theorem Checkpoint.identifies_retire {cp : Checkpoint} {f : Frame}
    (h : cp.Identifies f) {k : Nat} {v : Value} {vs : Domain}
    (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) :
    cp.Identifies (f.retire k vs) := by
  obtain ⟨hlev, hcov, hord⟩ := h
  refine ⟨by simpa [Frame.retire, Frame.level] using hlev, ?_, ?_⟩
  · intro a ha
    exact hcov a ((allAssigns_set_split hk a).mpr (Or.inr ha))
  · simpa [Frame.retire] using hord

/-! ## §6 Frame well-formedness: decided slots are singletons, order is
duplicate free, and only fresh slots are decided -/

/-- The sparse frame's structural invariant: the decision order has no
duplicates and every decided slot holds its singleton. -/
def Frame.WF (f : Frame) : Prop :=
  f.order.Nodup ∧ ∀ k ∈ f.order, ∃ v, f.doms[k]? = some (Dom.ofList [v])

/-- A live slot is never a decided slot: decision legality gives trail
freshness (`TrailLiteralsDistinct`'s sparse analogue). -/
theorem Frame.WF.not_mem_order_of_live {f : Frame} (h : f.WF) {k : Nat}
    (hl : f.Live k) : k ∉ f.order := by
  intro hk
  obtain ⟨v, hv⟩ := h.2 k hk
  obtain ⟨w, ws, hw, hne⟩ := hl
  have hmap : f.doms[k]?.map Dom.enum = some [v] := by
    rw [hv]
    simp
  rw [hw] at hmap
  simp only [Option.some.injEq] at hmap
  have hlen : (Dom.enum ws).length = 0 := by
    simpa using congrArg List.length hmap
  exact hne (List.length_eq_zero_iff.mp hlen)

/-- The decision step preserves well-formedness. -/
theorem Frame.WF.pin {f : Frame} (h : f.WF) {k : Nat} {v : Value}
    {vs : Domain} (hk : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hfresh : k ∉ f.order) : (f.pin k v).WF := by
  obtain ⟨hnd, hsing⟩ := h
  obtain ⟨d, hd, -⟩ := exists_getElem?_of_map_eq_some hk
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  refine ⟨?_, ?_⟩
  · rw [Frame.pin_order]
    exact List.nodup_append.mpr
      ⟨hnd, by simp, fun a ha b hb => by
        rw [List.mem_singleton] at hb
        subst hb
        exact fun haeq => hfresh (haeq ▸ ha)⟩
  · intro j hj
    rw [Frame.pin_order] at hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨w, hw⟩ := hsing j hj
      refine ⟨w, ?_⟩
      rw [Frame.pin_doms, List.getElem?_set]
      rw [if_neg (fun hkj : k = j => hfresh (hkj.symm ▸ hj))]
      exact hw
    · have hjk : j = k := by simpa using hj
      subst hjk
      refine ⟨v, ?_⟩
      simp only [Frame.pin_doms]
      exact List.getElem?_set_self hklt

/-- The retirement step preserves well-formedness (the retired slot is
fresh, so no decided slot changes). -/
theorem Frame.WF.retire {f : Frame} (h : f.WF) {k : Nat} {vs : Domain}
    (hfresh : k ∉ f.order) : (f.retire k vs).WF := by
  obtain ⟨hnd, hsing⟩ := h
  refine ⟨by simpa [Frame.retire] using hnd, ?_⟩
  intro j hj
  obtain ⟨w, hw⟩ := hsing j hj
  refine ⟨w, ?_⟩
  rw [Frame.retire_doms, List.getElem?_set]
  rw [if_neg (fun hkj : k = j => hfresh (hkj.symm ▸ hj))]
  exact hw

/-! ## §7 The tiny-model prototype (concrete, `rfl`/`simp`-checked) -/

/-- A three-slot tiny compiled box (two int slots and one bool slot). -/
def tinyBox : List Domain :=
  [Dom.ofList [Value.int 0, Value.int 1],
   Dom.ofList [Value.bool true, Value.bool false],
   Dom.ofList [Value.int 2, Value.int 3, Value.int 4]]

/-- Selection on the tiny box: slots 0 and 1 both have cardinality 2 and
slot 2 has 3, so the S1 minimum-cardinality rule picks slot 0 — the first
of the minimum-cardinality ties. -/
theorem tinyBox_select : selectSlot tinyBox = some 0 := by decide

theorem tinyBox_live : Live tinyBox 0 :=
  selectSlot_live tinyBox_select

/-- The S1 tie rule on the tiny box, read through the general theorem:
slot 0's `(cardinality, index)` key is minimum among live slots. -/
theorem tinyBox_min (j : Nat) (hj : Live tinyBox j) :
    Card tinyBox 0 < Card tinyBox j ∨
      (Card tinyBox 0 = Card tinyBox j ∧ 0 ≤ j) :=
  (selectSlot_min tinyBox_select).2 j hj

/-- Determinism on the tiny box: any live slot that is minimal for the
key is slot 0 (the tie rule admits no second answer). -/
theorem tinyBox_eq_of_min {k : Nat} (hk : Live tinyBox k)
    (hmin : ∀ j, Live tinyBox j →
      KeyLE (SlotKey tinyBox k) (SlotKey tinyBox j)) :
    k = 0 := by
  have h := selectSlot_eq_of_min hk hmin
  rw [tinyBox_select] at h
  exact (Option.some.inj h).symm

/-- A tiny box whose later slot is strictly SMALLER than the head: the S1
rule takes slot 1, while the positional head-of-remaining route would
always decide slot 0. -/
def tinySmallLast : List Domain :=
  [Dom.ofList [Value.int 1, Value.int 2, Value.int 3],
   Dom.ofList [Value.bool true, Value.bool false]]

/-- Minimum-cardinality selection takes the later, smaller slot. -/
theorem tinySmallLast_select : selectSlot tinySmallLast = some 1 := by decide

/-- The strictly-smaller-later case, read through the general rule: the
selected slot's cardinality is strictly below the head's. -/
theorem tinySmallLast_min :
    Card tinySmallLast 1 < Card tinySmallLast 0 := by
  have hlive : Live tinySmallLast 0 := by
    refine ⟨Value.int 1, Dom.ofList [Value.int 2, Value.int 3], ?_, ?_⟩
    · simp [tinySmallLast]
    · simp
  rcases (selectSlot_min tinySmallLast_select).2 0 hlive with h | ⟨-, hle⟩
  · exact h
  · omega

/-- A tiny box whose FIRST slot is a singleton: the positional frame would
be forced to decide slot 0, but no decision is legal there; the sparse
frame selects slot 1 — the arbitrary-slot behaviour S0 must enable. -/
def tinyHoleBox : List Domain :=
  [Dom.ofList [Value.int 7], Dom.ofList [Value.bool true, Value.bool false]]

/-- The arbitrary-slot selection: slot 1, not the prefix position 0. -/
theorem tinyHole_select : selectSlot tinyHoleBox = some 1 := by decide

theorem tinyHole_live : Live tinyHoleBox 1 :=
  selectSlot_live tinyHole_select

/-- The tiny frame over `tinyHoleBox` with no decisions yet. -/
def tinyHoleFrame : Frame := { doms := tinyHoleBox, order := [] }

/-- The tiny split data at the arbitrary slot 1. -/
theorem tinyHole_split :
    tinyHoleFrame.split = some (1, Value.bool true, Dom.ofList [Value.bool false]) := by
  unfold Frame.split
  dsimp only [tinyHoleFrame]
  rw [tinyHole_select]
  dsimp [tinyHoleBox]
  simp

/-- The concrete assignment `[7, true]` is covered by the tiny frame. -/
theorem tinyHole_covered :
    tinyHoleFrame.Covers [Value.int 7, Value.bool true] := by
  unfold Frame.Covers tinyHoleFrame tinyHoleBox
  rw [mem_allAssigns_cons_iff]
  refine ⟨Value.int 7, by simp, [Value.bool true], ?_, rfl⟩
  rw [mem_allAssigns_cons_iff]
  refine ⟨Value.bool true, by simp, [], by simp [allAssigns], rfl⟩

/-- The exhaustiveness instance at the arbitrary slot: the covered
assignment lands in the pinned child. -/
theorem tinyHole_branch :
    (tinyHoleFrame.pin 1 (Value.bool true)).Covers
      [Value.int 7, Value.bool true] := by
  rcases (covers_pin_or_retire (f := tinyHoleFrame) (k := 1)
    (v := Value.bool true) (vs := Dom.ofList [Value.bool false])
    (by simp [tinyHoleFrame, tinyHoleBox])
    (a := [Value.int 7, Value.bool true])).mp tinyHole_covered with h | h
  · exact h
  · exact absurd h (by
      intro hc
      have hread := covers_read hc (k := 1) (v := Value.bool false) rfl
      simp at hread)

/-- RECONSTRUCTION on the tiny model: the pinned child's covered
assignment reads the decided value at the decided slot. -/
theorem tinyHole_read :
    ([Value.int 7, Value.bool true] : Assignment)[1]? = some (Value.bool true) :=
  covers_read tinyHole_branch (k := 1) (v := Value.bool true) rfl

/-- The tiny frame is well formed (no decisions yet). -/
theorem tinyHoleFrame_wf : tinyHoleFrame.WF :=
  ⟨List.nodup_nil, fun k hk => by cases hk⟩

/-- CHECKPOINT CONSISTENCY on the tiny model: the frame's own checkpoint
identifies it, and deciding the arbitrary slot keeps the checkpoint
identifying the child branch. -/
theorem tinyHole_checkpoint :
    (Checkpoint.ofFrame tinyHoleFrame).Identifies tinyHoleFrame ∧
    (Checkpoint.ofFrame tinyHoleFrame).Identifies
      (tinyHoleFrame.pin 1 (Value.bool true)) :=
  ⟨Checkpoint.identifies_self tinyHoleFrame,
   Checkpoint.identifies_pin (cp := Checkpoint.ofFrame tinyHoleFrame)
     (f := tinyHoleFrame) (k := 1) (v := Value.bool true)
     (vs := Dom.ofList [Value.bool false])
     (Checkpoint.identifies_self tinyHoleFrame)
     (by simp [tinyHoleFrame, tinyHoleBox])⟩

end LeanFzn.Solver.Propagation.DecisionProto
