/-
File: LeanFzn/Solver/UIP/Proofs/PendingBacked.lean
pending resume's backing and reachability)

Purpose: the proof-side half of the R1 runtime repair. The runtime route
(LeanFzn/Solver/UIP/BackjumpFrontier.lean, `canonicalPins`/`canonicalFalsifiers`/
`canonicalTrail`/`resumePending`) treats a pending frame as its own
retained snapshot; this module supplies

  §0 `PendingBacked orig f` — the frame's own sub-box provenance (the
     premise the decide-arm push must maintain; R2's producer territory);
  §1 the literal/value bridges (`valueLiteral` injectivity, retirement
     algebra) the canonical entries are keyed by;
  §2 the `zipIdx` membership twin;
  §3 the membership inversions and shape facts of the canonical lists;
  §4 sortedness, well-formedness (and, with the frame's sub-box facts,
     the semantic fields) of the canonical trail.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.PendingBacked` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier
import LeanFzn.Legacy.Solver.Propagation.Proofs.BranchState
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerResume
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §0 The pending frame's own sub-box provenance -/

/-- The prefix-pin discipline of a sparse frame: the decision order is
duplicate-free and every DECIDED slot (a member of the order) holds its
pinned singleton with a decision literal. This is exactly
`PendingBacked.pins`, factored out so the producers and the
arm-preservation lemmas can name it. -/
def PrefixPinned (f : BranchFrame) : Prop :=
  f.order.Nodup ∧ ∀ k ∈ f.order, ∃ v : Value, f.doms[k]?.map Dom.enum = some [v] ∧
    ∃ l : Literal, valueLiteral k v = some l

/-- `filterFrame` preserves the prefix discipline: it keeps the decision
order and maps every decided singleton to itself. -/
theorem PrefixPinned.filterFrame {l : Literal} {f g : BranchFrame}
    (hg : filterFrame l f = some g) (hp : PrefixPinned f) : PrefixPinned g := by
  refine ⟨?_, ?_⟩
  · rw [Frame.filterFrame_order hg]
    exact hp.1
  · intro k hk
    have hkf : k ∈ f.order := by
      rwa [Frame.filterFrame_order hg] at hk
    obtain ⟨v, hv, l', hl'⟩ := hp.2 k hkf
    exact ⟨v, filterFrame_singleton hg hv, l', hl'⟩

/-- PENDING-BACKING (R1): the pending alternative is its own retained
snapshot. `full_len`/`fit` are the sub-box facts (from the split that
pushed the frame); `pins` records that every decided slot holds its
pinned value and has a decision literal (so the canonical trail can
re-force the decisions); `shape` is the box typing the semantic fields
need. Distinctness needs NO domain hypothesis: duplicated original
values (admitted by the accepted `var {..., k, ..., k, ...}` source
shape) emit their retire entry at the FIRST occurrence only — the runtime
dedup of `slotFalsifiers`. -/
structure PendingBacked (orig : List Domain) (f : BranchFrame) : Prop where
  /-- the full box of the frame has the original length -/
  full_len : (fullDomains f).length = orig.length
  /-- every decided slot holds its pinned singleton and has a decision literal -/
  pins : PrefixPinned f
  /-- the frame's whole box is inside the original box -/
  fit : ∀ i v, v ∈ (fullDomains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty
  /-- slot-wise typing of the original box -/
  shape : ShapeTypedDomains orig

/-! ## §1 Literal / value bridges -/

/-- Normalization preserves the referenced slot. -/
theorem literal_norm_atom_slot (l : Literal) :
    l.norm.atom.slot = l.atom.slot := by
  obtain ⟨atom, positive⟩ := l
  cases atom <;> (cases positive <;> simp [Literal.norm, Atom.slot])

/-- `valueLiteral`'s output is already normalized. -/
theorem valueLiteral_norm_self {s : Nat} {v : Value} {l : Literal}
    (h : valueLiteral s v = some l) : l.norm = l := by
  cases v with
  | bool b => simp [valueLiteral] at h; subst h; rfl
  | int i => simp [valueLiteral] at h; subst h; rfl
  | setOfInt s => simp [valueLiteral] at h
  | array s => simp [valueLiteral] at h

/-- THE PIN INJECTIVITY BRIDGE: one literal comes from one value per slot. -/
theorem valueLiteral_injective {s : Nat} {v v' : Value} {l : Literal}
    (h : valueLiteral s v = some l) (h' : valueLiteral s v' = some l) :
    v = v' := by
  cases v with
  | bool b =>
      have hb : posBool s b = l := by simpa [valueLiteral] using h
      cases v' with
      | bool b' =>
          have hb' : posBool s b' = l := by simpa [valueLiteral] using h'
          have heq : posBool s b = posBool s b' := hb.trans hb'.symm
          have h2 := congrArg Literal.atom heq
          simp only [posBool, Atom.boolEq.injEq] at h2
          obtain ⟨-, hbb⟩ := h2
          subst hbb
          rfl
      | int i =>
          have hi : negNe s i = l := by simpa [valueLiteral] using h'
          exact absurd (hb.trans hi.symm) (by intro hh; cases hh)
      | setOfInt s => simp [valueLiteral] at h'
      | array s => simp [valueLiteral] at h'
  | int i =>
      have hi : negNe s i = l := by simpa [valueLiteral] using h
      cases v' with
      | bool b =>
          have hb' : posBool s b = l := by simpa [valueLiteral] using h'
          exact absurd (hi.trans hb'.symm) (by intro hh; cases hh)
      | int i' =>
          have hi' : negNe s i' = l := by simpa [valueLiteral] using h'
          have heq : negNe s i = negNe s i' := hi.trans hi'.symm
          have h2 := congrArg Literal.atom heq
          simp only [negNe, Atom.intNe.injEq] at h2
          obtain ⟨-, hii⟩ := h2
          subst hii
          rfl
      | setOfInt s => simp [valueLiteral] at h'
      | array s => simp [valueLiteral] at h'
  | setOfInt s => simp [valueLiteral] at h
  | array s => simp [valueLiteral] at h

/-- The retire literal of an integer pin is the positive removal literal. -/
theorem negNe_negate_norm (s : Nat) (k : Int) :
    (negNe s k).negate.norm = posNe s k := rfl

/-- The retire literal of a Boolean pin is the opposite pin. -/
theorem posBool_negate_norm (s : Nat) (b : Bool) :
    (posBool s b).negate.norm = posBool s (!b) := rfl

/-- RETIRE-FORM INJECTIVITY: equal retirement literals force equal
retired values (per slot). -/
theorem valueLiteral_negate_norm_inj {s : Nat} {v v' : Value} {l l' : Literal}
    (h : valueLiteral s v = some l) (h' : valueLiteral s v' = some l')
    (heq : l.negate.norm = l'.negate.norm) : v = v' := by
  cases v with
  | bool b =>
      have hb : posBool s b = l := by simpa [valueLiteral] using h
      cases v' with
      | bool b' =>
          have hb' : posBool s b' = l' := by simpa [valueLiteral] using h'
          rw [← hb, ← hb', posBool_negate_norm, posBool_negate_norm] at heq
          have h2 := congrArg Literal.atom heq
          simp only [posBool, Atom.boolEq.injEq] at h2
          obtain ⟨-, hbb⟩ := h2
          have hbbb : b = b' := by cases b <;> cases b' <;> simpa using hbb
          subst hbbb
          rfl
      | int i =>
          have hi' : negNe s i = l' := by simpa [valueLiteral] using h'
          rw [← hb, ← hi', posBool_negate_norm, negNe_negate_norm] at heq
          exact absurd heq (by intro hh; cases hh)
      | setOfInt s => simp [valueLiteral] at h'
      | array s => simp [valueLiteral] at h'
  | int i =>
      have hi : negNe s i = l := by simpa [valueLiteral] using h
      cases v' with
      | bool b =>
          have hb' : posBool s b = l' := by simpa [valueLiteral] using h'
          rw [← hi, ← hb', negNe_negate_norm, posBool_negate_norm] at heq
          exact absurd heq (by intro hh; cases hh)
      | int i' =>
          have hi' : negNe s i' = l' := by simpa [valueLiteral] using h'
          rw [← hi, ← hi', negNe_negate_norm, negNe_negate_norm] at heq
          have h2 := congrArg Literal.atom heq
          simp only [posNe, Atom.intNe.injEq] at h2
          obtain ⟨-, hii⟩ := h2
          subst hii
          rfl
      | setOfInt s => simp [valueLiteral] at h'
      | array s => simp [valueLiteral] at h'
  | setOfInt s => simp [valueLiteral] at h
  | array s => simp [valueLiteral] at h

/-- THE LITERAL-vs-VALUE BRIDGE of the kept-pin test: for a value with a
pin, membership of the LITERAL in the slot's kept-pin list is exactly
membership of the VALUE in the kept domain. -/
theorem valueLiteral_kept_iff {j : Nat} {dom : Domain} {w : Value}
    {l : Literal} (hw : valueLiteral j w = some l) :
    l ∈ (Dom.enum dom).filterMap (valueLiteral j) ↔ w ∈ dom := by
  constructor
  · intro hmem
    obtain ⟨w', hw'mem, hw'⟩ := List.mem_filterMap.mp hmem
    have hw'w : w' = w := valueLiteral_injective hw' hw
    subst hw'w
    exact (DomainLike.mem_iff _ _).mpr (by simpa [domElems_eq_enum] using hw'mem)
  · intro hmem
    exact List.mem_filterMap.mpr
      ⟨w, by simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hmem, hw⟩

/-! ## §2 The `zipIdx` membership twin -/

/-- Polymorphic `zipIdx` membership: `(a, s) ∈ l.zipIdx` exactly when `s`
is an in-range index read as `a`. -/
theorem mem_zipIdx_iff' {α : Type} {l : List α} {a : α} {s : Nat} :
    (a, s) ∈ l.zipIdx ↔ ∃ h : s < l.length, l[s]'h = a := by
  constructor
  · intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.getElem_zipIdx] at heq
    have hlt : i < l.length := by simpa [List.length_zipIdx] using hi
    injection heq with h1 h2
    have hs : i = s := by omega
    subst hs
    exact ⟨hlt, h1⟩
  · rintro ⟨h, rfl⟩
    exact List.mem_iff_getElem.mpr
      ⟨s, by simpa [List.length_zipIdx] using h,
        by rw [List.getElem_zipIdx, Nat.zero_add]⟩

/-- `zipIdx` indices strictly increase along the list. -/
theorem pairwise_zipIdx_lt {α : Type} (l : List α) :
    List.Pairwise (fun a b : α × Nat => a.2 < b.2) l.zipIdx := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_zipIdx, Nat.zero_add]
  exact hij

/-- Normalization is idempotent. -/
theorem literal_norm_idem (l : Literal) : l.norm.norm = l.norm := by
  obtain ⟨atom, positive⟩ := l
  cases atom <;> (cases positive <;> rfl)

/-! ## §3 Membership inversions and structural facts of the canonical lists -/

/-- Membership in `canonicalPins`: an entry is a pin of a DECIDED slot
that holds a singleton with a decision literal. -/
theorem mem_canonicalPins {f : BranchFrame} {e : TrailEntry} :
    e ∈ canonicalPins f ↔
      ∃ p ∈ f.order.zipIdx, ∃ v : Value, ∃ l : Literal,
        f.doms[p.1]?.map Dom.enum = some [v] ∧ valueLiteral p.1 v = some l ∧
          e = { literal := l.norm, level := p.2 + 1, reason := none } := by
  rw [canonicalPins, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, he⟩
    split at he
    · rename_i d hd
      split at he
      · rename_i v hv
        rw [canonicalPinEntryAt, Option.map_eq_some_iff] at he
        obtain ⟨l, hl, hpe⟩ := he
        exact ⟨p, hp, v, l, by simp only [hd, Option.map_some, hv], hl, hpe.symm⟩
      · cases he
    · cases he
  · rintro ⟨p, hp, v, l, hv, hl, rfl⟩
    refine ⟨p, hp, ?_⟩
    cases hd : f.doms[p.1]? with
    | none => rw [hd] at hv; cases hv
    | some d =>
        rw [hd] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        simp only [Option.map_some, hv, canonicalPinEntryAt, hl]

/-- Level bound of a pin: it sits at the level its decision opened. -/
theorem canonicalPins_level_le {f : BranchFrame} {e : TrailEntry}
    (he : e ∈ canonicalPins f) : e.level ≤ f.level := by
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  obtain ⟨hlt, -⟩ := mem_zipIdx_iff'.mp hp
  simp only [BranchFrame.level]
  omega

/-- Pins are normalized entries with no reason. -/
theorem canonicalPins_literal_norm {f : BranchFrame} {e : TrailEntry}
    (he : e ∈ canonicalPins f) : e.literal = e.literal.norm := by
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  exact (literal_norm_idem l).symm

theorem canonicalPins_reason_none {f : BranchFrame} {e : TrailEntry}
    (he : e ∈ canonicalPins f) : e.reason = none := by
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  rfl

/-- The pins are level-sorted: `zipIdx` indices strictly increase. -/
theorem trailLevelSorted_of_const {L : List TrailEntry} {n : Nat}
    (h : ∀ e ∈ L, e.level = n) : TrailLevelSorted L := by
  rw [TrailLevelSorted, List.pairwise_iff_getElem]
  intro i j hi hj _
  rw [h _ (List.getElem_mem hi), h _ (List.getElem_mem hj)]
  exact Nat.le_refl n

/-- Every entry of a flatten of constant-level sublists has the level. -/
theorem flatten_levels_const {L : List (List TrailEntry)} {n : Nat}
    (h : ∀ l ∈ L, ∀ e ∈ l, e.level = n) :
    ∀ e ∈ L.flatten, e.level = n := by
  intro e he
  obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp he
  exact h l hl e hel

theorem canonicalPins_sorted (f : BranchFrame) :
    TrailLevelSorted (canonicalPins f) := by
  rw [canonicalPins, TrailLevelSorted]
  refine List.Pairwise.filterMap _ ?_ (pairwise_zipIdx_lt f.order)
  intro p q hpq b hb b' hb'
  split at hb
  · rename_i d hd
    split at hb
    · rename_i v hv
      rw [canonicalPinEntryAt, Option.map_eq_some_iff] at hb
      obtain ⟨l, hl, rfl⟩ := hb
      split at hb'
      · rename_i d' hd'
        split at hb'
        · rename_i v' hv'
          rw [canonicalPinEntryAt, Option.map_eq_some_iff] at hb'
          obtain ⟨l', hl', rfl⟩ := hb'
          simp only
          omega
        · cases hb'
      · cases hb'
    · cases hb
  · cases hb

/-- FIRST-OCCURRENCE EXISTENCE: a member of a `filterMap` image has a
position whose image is the member and whose PREFIX image does not
contain it — the first-occurring position. -/
theorem exists_first_of_mem_filterMap {α β : Type} [DecidableEq β]
    {g : α → Option β} {l : List α} {b : β}
    (h : b ∈ l.filterMap g) :
    ∃ p ∈ l.zipIdx, g p.1 = some b ∧ b ∉ (l.take p.2).filterMap g := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
      cases hg : g a with
      | none =>
          rw [List.filterMap_cons_none hg] at h
          obtain ⟨p, hp, hgp, hfirst⟩ := ih h
          refine ⟨(p.1, p.2 + 1), ?_, hgp, ?_⟩
          · rw [List.zipIdx_cons]
            refine List.mem_cons_of_mem _ ?_
            have hmem := (List.mem_zipIdx_iff_getElem? (x := (p.1, p.2))
              (l := as)).mp hp
            have := (List.mk_add_mem_zipIdx_iff_getElem? (k := 1) (i := p.2)
              (x := p.1) (l := as)).mpr hmem
            simpa [Nat.add_comm] using this
          · rw [List.take_succ_cons, List.filterMap_cons_none hg]
            exact hfirst
      | some c =>
          rw [List.filterMap_cons_some hg] at h
          by_cases hcb : c = b
          · refine ⟨(a, 0), ?_, ?_, ?_⟩
            · rw [List.zipIdx_cons]
              exact List.mem_cons_self ..
            · rw [← hcb]
              exact hg
            · rw [List.take_zero]
              simp
          · rcases List.mem_cons.mp h with hbc | htl
            · exact absurd hbc.symm hcb
            · obtain ⟨p, hp, hgp, hfirst⟩ := ih htl
              refine ⟨(p.1, p.2 + 1), ?_, hgp, ?_⟩
              · rw [List.zipIdx_cons]
                refine List.mem_cons_of_mem _ ?_
                have hmem := (List.mem_zipIdx_iff_getElem? (x := (p.1, p.2))
                  (l := as)).mp hp
                have := (List.mk_add_mem_zipIdx_iff_getElem? (k := 1)
                  (i := p.2) (x := p.1) (l := as)).mpr hmem
                simpa [Nat.add_comm] using this
              · rw [List.take_succ_cons, List.filterMap_cons_some hg]
                intro hmem
                rcases List.mem_cons.mp hmem with hbc' | htl'
                · exact hcb hbc'.symm
                · exact hfirst htl'

/-- Membership in a slot's falsifier list: an entry is the retire entry
of a FIRST occurrence, at its absolute slot, of a value outside the kept
pins. -/
theorem mem_slotFalsifiers {orig : List Domain} {f : BranchFrame} {k : Nat}
    {dom : Domain} {e : TrailEntry} :
    e ∈ slotFalsifiers orig f k dom ↔
      ∃ p ∈ (Dom.enum (orig.getD k Dom.empty)).zipIdx, ∃ l : Literal,
        valueLiteral k p.1 = some l ∧
        l ∉ (Dom.enum dom).filterMap (valueLiteral k) ∧
        l ∉ ((Dom.enum (orig.getD k Dom.empty)).take p.2).filterMap (valueLiteral k) ∧
        e = { literal := l.negate.norm, level := f.level,
              reason := none } := by
  unfold slotFalsifiers
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hmap⟩
    cases hv : valueLiteral k p.1 with
    | none =>
        simp only [hv] at hmap
        cases hmap
    | some l =>
        simp only [hv] at hmap
        split at hmap
        · cases hmap
        · rename_i hk
          split at hmap
          · cases hmap
          · rename_i htk
            refine ⟨p, hp, l, hv, hk, htk, ?_⟩
            simp only [canonicalRetire, hv, Option.map_some] at hmap
            exact (Option.some.inj hmap).symm
  · rintro ⟨p, hp, l, hv, hk, htk, rfl⟩
    refine ⟨p, hp, ?_⟩
    simp only [hv, if_neg hk, if_neg htk, canonicalRetire, Option.map_some]

/-- Membership in `canonicalFalsifiers`. -/
theorem mem_canonicalFalsifiers {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} :
    e ∈ canonicalFalsifiers orig f ↔
      ∃ p ∈ f.doms.zipIdx, p.2 ∉ f.order ∧
        ∃ q ∈ (Dom.enum (orig.getD p.2 Dom.empty)).zipIdx, ∃ l : Literal,
        valueLiteral p.2 q.1 = some l ∧
        l ∉ (Dom.enum p.1).filterMap (valueLiteral p.2) ∧
        l ∉ ((Dom.enum (orig.getD p.2 Dom.empty)).take q.2).filterMap (valueLiteral p.2) ∧
        e = { literal := l.negate.norm, level := f.level,
              reason := none } := by
  rw [canonicalFalsifiers, List.mem_flatten]
  constructor
  · rintro ⟨inner, hinner, he⟩
    simp only [List.mem_filterMap] at hinner
    obtain ⟨p, hp, hsome⟩ := hinner
    split at hsome
    · cases hsome
    · rename_i hnotin
      injection hsome with hinner_eq
      subst hinner_eq
      obtain ⟨q, hq, l, hv, hk, htk, rfl⟩ := mem_slotFalsifiers.mp he
      exact ⟨p, hp, hnotin, q, hq, l, hv, hk, htk, rfl⟩
  · rintro ⟨p, hp, hnotin, q, hq, l, hv, hk, htk, rfl⟩
    refine ⟨slotFalsifiers orig f p.2 p.1, ?_,
      mem_slotFalsifiers.mpr ⟨q, hq, l, hv, hk, htk, rfl⟩⟩
    exact List.mem_filterMap.mpr ⟨p, hp, by simp [hnotin]⟩

/-- EMISSION: every dropped undecided-slot original value's retire entry
is present (the direction `narrowing_complete` consumes). -/
theorem canonicalFalsifiers_emit {orig : List Domain} {f : BranchFrame}
    {k : Nat} {w : Value} {l : Literal}
    (hk : k ∉ f.order) (hklt : k < f.doms.length)
    (hw : w ∈ orig.getD k Dom.empty)
    (hl : valueLiteral k w = some l)
    (hnot : l ∉ (Dom.enum (f.doms.getD k Dom.empty)).filterMap (valueLiteral k)) :
    { literal := l.negate.norm, level := f.level, reason := none } ∈
      canonicalFalsifiers orig f := by
  have hget : f.doms.getD k Dom.empty = f.doms[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
    rfl
  rw [hget] at hnot
  have hwE : w ∈ Dom.enum (orig.getD k Dom.empty) := by
    simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw
  obtain ⟨q, hq, hgq, hfirst⟩ := exists_first_of_mem_filterMap
    (List.mem_filterMap.mpr ⟨w, hwE, hl⟩ : l ∈ (Dom.enum (orig.getD k
      Dom.empty)).filterMap (valueLiteral k))
  refine mem_canonicalFalsifiers.mpr
    ⟨(f.doms[k], k), mem_zipIdx_iff'.mpr ⟨hklt, rfl⟩, hk, q, hq, l, hgq,
      hnot, hfirst, rfl⟩

/-- Every falsifier entry sits at the resumed level, is normalized and has
no reason. -/
theorem canonicalFalsifiers_level {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.level = f.level := by
  obtain ⟨p, hp, hk, q, hq, l, hv, hkeep, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  rfl

theorem canonicalFalsifiers_literal_norm {orig : List Domain}
    {f : BranchFrame} {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.literal = e.literal.norm := by
  obtain ⟨p, hp, hk, q, hq, l, hv, hkeep, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  exact (literal_norm_idem l.negate).symm

theorem canonicalFalsifiers_reason_none {orig : List Domain}
    {f : BranchFrame} {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.reason = none := by
  obtain ⟨p, hp, hk, q, hq, l, hv, hkeep, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  rfl

/-- Every entry of a slot's falsifier list sits at the resumed level. -/
theorem slotFalsifiers_level {orig : List Domain} {f : BranchFrame} {k : Nat}
    {dom : Domain} {e : TrailEntry} (he : e ∈ slotFalsifiers orig f k dom) :
    e.level = f.level := by
  obtain ⟨q, hq, l, hv, hkeep, htk, rfl⟩ := mem_slotFalsifiers.mp he
  rfl

/-- The falsifiers are level-sorted (constant resumed level). -/
theorem canonicalFalsifiers_sorted (orig : List Domain) (f : BranchFrame) :
    TrailLevelSorted (canonicalFalsifiers orig f) := by
  rw [canonicalFalsifiers]
  refine trailLevelSorted_of_const (n := f.level)
    (flatten_levels_const (n := f.level) ?_)
  intro l hl e hel
  simp only [List.mem_filterMap] at hl
  obtain ⟨p, hp, hsome⟩ := hl
  split at hsome
  · cases hsome
  · rename_i hnotin
    injection hsome with hinner_eq
    subst hinner_eq
    exact slotFalsifiers_level hel

/-- Canonical-trail facts: every entry is a normalized, reason-less entry
at or below the resumed level. -/
theorem canonicalTrail_level_le {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalTrail orig f) :
    e.level ≤ f.level := by
  rcases List.mem_append.mp he with he | he
  · exact Nat.le_trans (canonicalPins_level_le he) (Nat.le_refl _)
  · exact Nat.le_of_eq (canonicalFalsifiers_level he)

theorem canonicalTrail_literal_norm {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalTrail orig f) :
    e.literal = e.literal.norm := by
  rcases List.mem_append.mp he with he | he
  · exact canonicalPins_literal_norm he
  · exact canonicalFalsifiers_literal_norm he

theorem canonicalTrail_reason_none {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalTrail orig f) : e.reason = none := by
  rcases List.mem_append.mp he with he | he
  · exact canonicalPins_reason_none he
  · exact canonicalFalsifiers_reason_none he

/-- The canonical trail is level-sorted: pins at levels `1..L` followed by
falsifiers at level `L`. -/
theorem canonicalTrail_sorted (orig : List Domain) (f : BranchFrame) :
    TrailLevelSorted (canonicalTrail orig f) := by
  rw [canonicalTrail, TrailLevelSorted, List.pairwise_append]
  refine ⟨canonicalPins_sorted f, canonicalFalsifiers_sorted orig f, ?_⟩
  intro a ha b hb
  have hb' : b.level = f.level := canonicalFalsifiers_level hb
  rw [hb']
  exact canonicalPins_level_le ha

/-- The canonical resume is well-formed: only the learned database survives
from the predecessor. -/
theorem canonicalTrail_wellFormed {orig : List Domain} {f : BranchFrame}
    {bs : BranchState leaf} (hlearn : LearnedEntailed leaf bs.learned) :
    (resumePendingBase orig bs f).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    show e.level ≤ f.level
    exact canonicalTrail_level_le he
  · intro e he
    exact canonicalTrail_literal_norm he
  · intro e he r hr
    rw [canonicalTrail_reason_none he] at hr
    cases hr
  · intro e he r hr
    rw [canonicalTrail_reason_none he] at hr
    cases hr
  · show LearnedEntailed leaf bs.learned
    exact hlearn

/-! ## §4 The semantic fields of the canonical trail -/

/-- The Bool-shaped twin of `intShaped_of_mem_int`. -/
theorem boolShaped_of_mem_bool {orig : List Domain} {s : Nat} {b : Bool}
    (hshape : ShapeTypedDomains orig) (h : Value.bool b ∈ orig.getD s Dom.empty) :
    ∀ w ∈ orig.getD s Dom.empty, ∃ b : Bool, w = Value.bool b := by
  have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s)
    (a := (Dom.empty : Domain))
  cases hgt : orig[s]? with
  | none =>
      rw [hlook, hgt] at h
      simp only [Option.getD_none] at h
      simp at h
  | some d =>
      have hd : d ∈ orig := List.mem_of_getElem? hgt
      have hh : Value.bool b ∈ d := by
        rw [hlook, hgt] at h
        simpa using h
      rcases hshape d hd with hint | hbool
      · obtain ⟨k, hk⟩ := hint _ hh
        exact absurd hk (fun hh => by cases hh)
      · intro w hw
        rw [hlook, hgt] at hw
        exact hbool w (by simpa using hw)

/-- The disjunctive shape fact at a `getD` read: any value of the read
domain exposes the slot's uniform shape. -/
theorem shaped_of_mem {orig : List Domain} {s : Nat} {v : Value}
    (hshape : ShapeTypedDomains orig) (hv : v ∈ orig.getD s Dom.empty) :
    (∀ w ∈ orig.getD s Dom.empty, ∃ k : Int, w = Value.int k) ∨
      (∀ w ∈ orig.getD s Dom.empty, ∃ b : Bool, w = Value.bool b) := by
  cases v with
  | bool b => exact Or.inr (boolShaped_of_mem_bool hshape hv)
  | int i => exact Or.inl (intShaped_of_mem_int hshape hv)
  | setOfInt q =>
      have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s)
        (a := (Dom.empty : Domain))
      cases hgt : orig[s]? with
      | none =>
          rw [hlook, hgt] at hv
          simp only [Option.getD_none] at hv
          simp at hv
      | some d =>
          have hd : d ∈ orig := List.mem_of_getElem? hgt
          have hh : Value.setOfInt q ∈ d := by
            rw [hlook, hgt] at hv
            simpa using hv
          rcases hshape d hd with hint | hbool
          · obtain ⟨k, hk⟩ := hint _ hh
            exact absurd hk (fun hh => by cases hh)
          · obtain ⟨b, hb⟩ := hbool _ hh
            exact absurd hb (fun hh => by cases hh)
  | array q =>
      have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s)
        (a := (Dom.empty : Domain))
      cases hgt : orig[s]? with
      | none =>
          rw [hlook, hgt] at hv
          simp only [Option.getD_none] at hv
          simp at hv
      | some d =>
          have hd : d ∈ orig := List.mem_of_getElem? hgt
          have hh : Value.array q ∈ d := by
            rw [hlook, hgt] at hv
            simpa using hv
          rcases hshape d hd with hint | hbool
          · obtain ⟨k, hk⟩ := hint _ hh
            exact absurd hk (fun hh => by cases hh)
          · obtain ⟨b, hb⟩ := hbool _ hh
            exact absurd hb (fun hh => by cases hh)

/-- A slot carrying an original value of a length-correct frame is a real
frame slot. -/
theorem slot_lt_of_mem {orig : List Domain} {f : BranchFrame}
    (hlen : (fullDomains f).length = orig.length) {k : Nat} {w : Value}
    (hw : w ∈ orig.getD k Dom.empty) : k < f.doms.length := by
  have h1 : k < orig.length := by
    suffices hnot : ¬ (orig.length ≤ k) by omega
    intro hge
    have hnil : orig.getD k Dom.empty = Dom.empty := by
      cases hlt : orig[k]? with
      | none =>
          rw [List.getD_eq_getElem?_getD, hlt]
          rfl
      | some d =>
          obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hlt
          omega
    rw [hnil] at hw
    exact absurd hw (by simp)
  rw [← hlen, fullDomains_length] at h1
  exact h1

/-- **F5 (narrowing completeness) for the canonical trail**: every dropped
original value of an UNDECIDED slot carries its retire entry. Needs only
the box typing (pin existence at dropped values) and the frame's length. -/
theorem narrowing_complete_canonical {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hlen : (fullDomains f).length = orig.length) :
    NarrowingComplete (canonicalTrail orig f) orig f := by
  intro k hkundec w hw hnot
  have hklt : k < f.doms.length := slot_lt_of_mem hlen hw
  have hpin : ∃ l, valueLiteral k w = some l := by
    rcases shaped_of_mem hshape hw with hint | hbool
    · obtain ⟨i, rfl⟩ := hint w hw
      exact ⟨negNe k i, rfl⟩
    · obtain ⟨b, rfl⟩ := hbool w hw
      exact ⟨posBool k b, rfl⟩
  obtain ⟨l, hl⟩ := hpin
  have hkeep : l ∉ (Dom.enum (f.doms.getD k Dom.empty)).filterMap (valueLiteral k) :=
    fun hmem => hnot ((valueLiteral_kept_iff hl).mp hmem)
  refine ⟨{ literal := l.negate.norm, level := f.level, reason := none },
    List.mem_append.mpr (Or.inr
      (canonicalFalsifiers_emit hkundec hklt hw hl hkeep)), ?_, ?_⟩
  · show l.negate.norm.atom.slot = k
    rw [literal_negate_norm_atom_slot]
    exact valueLiteral_atom_slot hl
  · exact valueLiteral_negate_norm_valueHolds_false hl

/-- A covered assignment reads a slot whose enumeration is a singleton. -/
theorem allAssigns_read_enum {ds : List Domain} {a : Assignment} {k : Nat}
    {v : Value} (ha : a ∈ allAssigns ds)
    (hk : ds[k]?.map Dom.enum = some [v]) : a[k]? = some v := by
  induction ds generalizing a k with
  | nil => simp at hk
  | cons d rest ih =>
      obtain ⟨w, hw, a', ha', rfl⟩ := mem_allAssigns_cons_iff.mp ha
      cases k with
      | zero =>
          have hde : Dom.enum d = [v] := by simpa using hk
          have hw' : w ∈ Dom.enum d := by
            simpa [domElems_eq_enum] using (DomainLike.mem_iff d w).mp hw
          rw [hde] at hw'
          have hwv : w = v := List.mem_singleton.mp hw'
          subst hwv
          rfl
      | succ j =>
          rw [List.getElem?_cons_succ] at hk ⊢
          exact ih ha' hk

/-- A covered assignment reads a frame slot whose enumeration is a
singleton. -/
theorem covers_read_enum {f : BranchFrame} {a : Assignment} {k : Nat}
    {v : Value} (ha : FrameCovers f a)
    (hk : f.doms[k]?.map Dom.enum = some [v]) : a[k]? = some v :=
  allAssigns_read_enum ha hk

/-- **F4-pins**: canonical pins hold at every frame-covered assignment (no
premises: the covered assignment reads its decided slots' singletons). -/
theorem agrees_canonicalPins {f : BranchFrame} :
    ∀ e ∈ canonicalPins f, ∀ a, FrameCovers f a →
      e.literal.eval a = some true := by
  intro e he a hcov
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  have hread : a[p.1]? = some v := covers_read_enum hcov hv
  have hslot : a[l.atom.slot]? = some v := by
    rw [valueLiteral_atom_slot hl]
    exact hread
  rw [Literal.norm_eval, ← valueHolds_read hslot]
  exact valueLiteral_valueHolds_self hl

/-- **F4-falsifier SEMANTICS**: a retire entry holds at every value the
sibling slot's kept domain still admits (the kept-pin test is by literal,
the domain read by value — the bridge is `valueLiteral` injectivity plus
the typed discipline that excludes the int-view collisions). -/
theorem falsifier_holds_of_not_kept {orig : List Domain} {j : Nat}
    {dom : Domain} {w w' : Value} {l : Literal}
    (hshape : ShapeTypedDomains orig) (hw : w ∈ orig.getD j Dom.empty)
    (hl : valueLiteral j w = some l)
    (hlk : l ∉ (Dom.enum dom).filterMap (valueLiteral j))
    (hdom : ∀ v ∈ dom, v ∈ orig.getD j Dom.empty) (hw' : w' ∈ dom) :
    l.negate.norm.valueHolds w' = true := by
  have hsh := shaped_of_mem hshape hw
  cases w with
  | bool b =>
      have hl' : l = posBool j b := by simpa [valueLiteral] using hl.symm
      have hbool : ∀ v ∈ orig.getD j Dom.empty, ∃ b : Bool, v = Value.bool b := by
        rcases hsh with hint | hbool
        · obtain ⟨k, hk⟩ := hint _ hw
          exact absurd hk (fun hh => by cases hh)
        · exact hbool
      obtain ⟨b', hb'⟩ := hbool w' (hdom w' hw')
      subst hb'
      have hne : b' ≠ b := by
        intro hbb
        apply hlk
        rw [hl', ← hbb]
        exact List.mem_filterMap.mpr
          ⟨Value.bool b',
            by simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw',
            by simp [valueLiteral]⟩
      rw [hl', posBool_negate_norm]
      cases b <;> cases b' <;> simp_all [Literal.valueHolds, posBool]
  | int k =>
      have hl' : l = negNe j k := by simpa [valueLiteral] using hl.symm
      have hint : ∀ v ∈ orig.getD j Dom.empty, ∃ k : Int, v = Value.int k := by
        rcases hsh with hint | hbool
        · exact hint
        · obtain ⟨b, hb⟩ := hbool _ hw
          exact absurd hb (fun hh => by cases hh)
      obtain ⟨k', hk'⟩ := hint w' (hdom w' hw')
      subst hk'
      have hne : k' ≠ k := by
        intro hkk
        apply hlk
        rw [hl', ← hkk]
        exact List.mem_filterMap.mpr
          ⟨Value.int k',
            by simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw',
            by simp [valueLiteral]⟩
      rw [hl', negNe_negate_norm]
      simp [Literal.valueHolds, posNe, Value.intView, hne]
  | setOfInt q => simp [valueLiteral] at hl
  | array q => simp [valueLiteral] at hl

/-- **F4-falsifiers**: canonical falsifiers hold at every frame-covered
assignment (the covered assignment reads a kept value of the slot the
retire entry falsifies). -/
theorem agrees_canonicalFalsifiers {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty)
    (_hlen : (fullDomains f).length = orig.length) :
    ∀ e ∈ canonicalFalsifiers orig f, ∀ a, FrameCovers f a →
      e.literal.eval a = some true := by
  intro e he a hcov
  obtain ⟨p, hp, hkundec, q, hq, l, hl, hlk, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  obtain ⟨hqlt, hqe⟩ := mem_zipIdx_iff'.mp hq
  have hw : q.1 ∈ orig.getD p.2 Dom.empty := by
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum]
    rw [← hqe]
    exact List.getElem_mem hqlt
  obtain ⟨hplt, hpre⟩ := mem_zipIdx_iff'.mp hp
  have hgetD : f.doms.getD p.2 Dom.empty = p.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hplt]
    exact hpre
  obtain ⟨w', hw'mem, hread⟩ := exists_read_of_covers hcov hplt
  rw [hgetD] at hw'mem
  have hslot : a[l.negate.norm.atom.slot]? = some w' := by
    rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hl]
    exact hread
  rw [← valueHolds_read hslot]
  refine falsifier_holds_of_not_kept (j := p.2) hshape hw hl ?_ ?_ hw'mem
  · exact hlk
  · intro v hv
    exact hfit p.2 v (by
      show v ∈ f.doms.getD p.2 Dom.empty
      rw [hgetD]
      exact hv)

/-- The canonical trail's entries all hold at covered assignments. -/
theorem agrees_canonicalTrail {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty)
    (hlen : (fullDomains f).length = orig.length) :
    ∀ e ∈ canonicalTrail orig f, ∀ a, FrameCovers f a →
      e.literal.eval a = some true := by
  intro e he a hcov
  rcases List.mem_append.mp he with he | he
  · exact agrees_canonicalPins e he a hcov
  · exact agrees_canonicalFalsifiers hshape hfit hlen e he a hcov

/-- The pin of a prefix value forces that value at `Fits`-assignments of a
typed slot (Bool globally exact; Int through the integer-view typing). -/
theorem pin_forces_of_fits {orig : List Domain} {s : Nat} {w : Value}
    {l : Literal} (hshape : ShapeTypedDomains orig)
    (hwm : w ∈ orig.getD s Dom.empty) (hl : valueLiteral s w = some l) :
    ∀ a, a.Fits orig → l.norm.eval a = some true → a[s]? = some w := by
  intro a hfits hev
  rw [Literal.norm_eval, valueLiteral_holds_iff hl a] at hev
  cases w with
  | bool b => simpa using hev
  | int k =>
      have htyped := intShaped_of_mem_int hshape hwm
      have hslot := getElem_of_slotInt_typed hfits htyped hev
      simpa using hslot
  | setOfInt q => simp [valueLiteral] at hl
  | array q => simp [valueLiteral] at hl

/-- **F3 (decision forcing)** for the sparse canonical trail: the pins
force every decided slot's value at every fitting assignment. -/
theorem pins_forced_canonical {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hpins : PrefixPinned f)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i Dom.empty → v ∈ orig.getD i Dom.empty) :
    PinsForced (canonicalTrail orig f) orig f := by
  intro k hk
  obtain ⟨v, hv, l, hl⟩ := hpins.2 k hk
  refine ⟨v, hv, ?_⟩
  intro a hsat hfits
  obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.mp hk
  have hpk : (k, i) ∈ f.order.zipIdx :=
    mem_zipIdx_iff'.mpr ⟨hi, hik⟩
  have hmem : { literal := l.norm, level := i + 1, reason := none } ∈
      canonicalPins f :=
    mem_canonicalPins.mpr ⟨(k, i), hpk, v, l, hv, hl, rfl⟩
  have hev : (l.norm).eval a = some true :=
    hsat _ (List.mem_append.mpr (Or.inl hmem))
  have hwm : v ∈ orig.getD k Dom.empty := by
    apply hfit
    show v ∈ f.doms.getD k Dom.empty
    exact mem_getD_of_enum_singleton hv
  exact pin_forces_of_fits hshape hwm hl a hfits hev

/-- A `zipIdx` member's first component is in the source list. -/
theorem order_mem_of_zipIdx {f : BranchFrame} {p : Nat × Nat}
    (hp : p ∈ f.order.zipIdx) : p.1 ∈ f.order := by
  obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
  rw [← hpre]
  exact List.getElem_mem hlt

/-- Every pin references a decided slot (a member of the order). -/
theorem canonicalPins_slot {f : BranchFrame} {e : TrailEntry}
    (he : e ∈ canonicalPins f) : e.literal.atom.slot ∈ f.order := by
  obtain ⟨p, hp, v, l, hv, hl, rfl⟩ := mem_canonicalPins.mp he
  rw [literal_norm_atom_slot, valueLiteral_atom_slot hl]
  exact order_mem_of_zipIdx hp

/-- Every falsifier entry references an UNDECIDED slot. -/
theorem canonicalFalsifiers_slot {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    ∃ p ∈ f.doms.zipIdx, p.2 ∉ f.order ∧ e.literal.atom.slot = p.2 := by
  obtain ⟨p, hp, hk, q, hq, l, hv, hkeep, htk, rfl⟩ :=
    mem_canonicalFalsifiers.mp he
  exact ⟨p, hp, hk, by
    rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hv]⟩

/-- Every entry of a slot's falsifier list references that slot. -/
theorem slotFalsifiers_slot {orig : List Domain} {f : BranchFrame} {k : Nat}
    {dom : Domain} {e : TrailEntry} (he : e ∈ slotFalsifiers orig f k dom) :
    e.literal.atom.slot = k := by
  obtain ⟨q, hq, l, hv, hkeep, htk, rfl⟩ := mem_slotFalsifiers.mp he
  rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hv]

/-- The pins are duplicate-free (strictly increasing levels). -/
theorem canonicalPins_nodup (f : BranchFrame) : (canonicalPins f).Nodup := by
  rw [List.Nodup, canonicalPins]
  refine List.Pairwise.filterMap _ ?_ (pairwise_zipIdx_lt f.order)
  intro p q hpq a ha b hb heq
  split at ha
  · rename_i d hd
    split at ha
    · rename_i v hv
      rw [canonicalPinEntryAt, Option.map_eq_some_iff] at ha
      obtain ⟨l, hl, rfl⟩ := ha
      split at hb
      · rename_i d' hd'
        split at hb
        · rename_i v' hv'
          rw [canonicalPinEntryAt, Option.map_eq_some_iff] at hb
          obtain ⟨l', hl', rfl⟩ := hb
          have hlev := congrArg TrailEntry.level heq
          simp only at hlev
          omega
        · cases hb
      · cases hb
    · cases ha
  · cases ha

/-- A slot's falsifier list is ALWAYS duplicate-free: entries are emitted
at their first-occurring position only, and distinct occurrences of the
same literal come from the same value (`valueLiteral_negate_norm_inj`) —
whose earlier occurrence is already in the take image. -/
theorem slotFalsifiers_nodup {orig : List Domain} {f : BranchFrame} {k : Nat}
    {dom : Domain} : (slotFalsifiers orig f k dom).Nodup := by
  simp only [slotFalsifiers]
  rw [List.Nodup, List.pairwise_filterMap]
  rw [List.pairwise_iff_getElem]
  intro i' j' hi' hj' hij e he e' he'
  simp only [List.getElem_zipIdx, Nat.zero_add] at he he'
  intro heq
  have hi'len : i' < (Dom.enum (orig.getD (k) Dom.empty)).length := by
    simpa [List.length_zipIdx] using hi'
  have hj'len : j' < (Dom.enum (orig.getD (k) Dom.empty)).length := by
    simpa [List.length_zipIdx] using hj'
  cases hv : valueLiteral (k)
      ((Dom.enum (orig.getD (k) Dom.empty))[i']'hi'len) with
  | none =>
      simp only [hv] at he
      cases he
  | some le =>
      simp only [hv] at he
      by_cases hk : le ∈ (Dom.enum dom).filterMap (valueLiteral (k))
      · rw [if_pos hk] at he
        cases he
      · rw [if_neg hk] at he
        by_cases htk : le ∈ ((Dom.enum (orig.getD (k) Dom.empty)).take i').filterMap
            (valueLiteral (k))
        · rw [if_pos htk] at he
          cases he
        · rw [if_neg htk] at he
          rw [canonicalRetire, hv, Option.map_some] at he
          have he_e : e = { literal := le.negate.norm, level := f.level, reason := none } :=
            (Option.some.inj he).symm
          cases hv' : valueLiteral (k)
              ((Dom.enum (orig.getD (k) Dom.empty))[j']'hj'len) with
          | none =>
              simp only [hv'] at he'
              cases he'
          | some le' =>
              simp only [hv'] at he'
              by_cases hk' : le' ∈ (Dom.enum dom).filterMap (valueLiteral (k))
              · rw [if_pos hk'] at he'
                cases he'
              · rw [if_neg hk'] at he'
                by_cases htk' : le' ∈ ((Dom.enum (orig.getD (k) Dom.empty)).take
                    j').filterMap (valueLiteral (k))
                · rw [if_pos htk'] at he'
                  cases he'
                · rw [if_neg htk'] at he'
                  rw [canonicalRetire, hv', Option.map_some] at he'
                  have he'_e : e' = { literal := le'.negate.norm, level := f.level, reason := none } :=
                    (Option.some.inj he').symm
                  rw [he_e, he'_e] at heq
                  have hlit : le.negate.norm = le'.negate.norm :=
                    congrArg TrailEntry.literal heq
                  have hds : (Dom.enum (orig.getD (k) Dom.empty))[i']'hi'len =
                      (Dom.enum (orig.getD (k) Dom.empty))[j']'hj'len :=
                    valueLiteral_negate_norm_inj hv hv' hlit
                  apply htk'
                  apply List.mem_filterMap.mpr
                  refine ⟨(Dom.enum (orig.getD (k) Dom.empty))[i']'hi'len, ?_, ?_⟩
                  · rw [List.mem_take_iff_getElem]
                    exact ⟨i', by omega, rfl⟩
                  · rw [hds]
                    exact hv'

/-- The falsifiers are duplicate-free: per-slot lists are (first-occurrence
dedup), and different slots cannot share an entry. -/
theorem canonicalFalsifiers_nodup {orig : List Domain} {f : BranchFrame} :
    (canonicalFalsifiers orig f).Nodup := by
  rw [canonicalFalsifiers, List.Nodup, List.pairwise_flatten]
  constructor
  · intro l hl
    simp only [List.mem_filterMap] at hl
    obtain ⟨p, hp, hsome⟩ := hl
    split at hsome
    · cases hsome
    · injection hsome with hinner
      subst hinner
      exact slotFalsifiers_nodup
  · refine List.Pairwise.filterMap _ ?_ (pairwise_zipIdx_lt f.doms)
    intro p q hpq l₁ hl₁ l₂ hl₂ x hx y hy
    split at hl₁
    · cases hl₁
    · rename_i hpnotin
      injection hl₁ with h1
      subst h1
      split at hl₂
      · cases hl₂
      · rename_i hqnotin
        injection hl₂ with h2
        subst h2
        intro heq
        have hxslot := slotFalsifiers_slot hx
        have hyslot := slotFalsifiers_slot hy
        rw [heq] at hxslot
        omega

/-- **F8 (norm-uniqueness)**: equal normalized literals force equal
entries — pins by their slots, falsifiers by retirement injectivity, and
the two groups never share a slot. -/
theorem canonicalTrail_norm_unique {orig : List Domain} {f : BranchFrame}
    (hnd : f.order.Nodup)
    {e e' : TrailEntry} (he : e ∈ canonicalTrail orig f)
    (he' : e' ∈ canonicalTrail orig f)
    (hl : e'.literal = e.literal.norm) : e' = e := by
  have hlit0 : e'.literal = e.literal := by
    rw [← canonicalTrail_literal_norm he] at hl
    exact hl
  rcases List.mem_append.mp he with he | he <;>
    rcases List.mem_append.mp he' with he' | he'
  · -- pin / pin
    obtain ⟨p, hp, v, l, hv, hl1, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨p', hp', v', l', hv', hl2, rfl⟩ := mem_canonicalPins.mp he'
    have hlit : l'.norm = l.norm := hlit0
    have hslot : p'.1 = p.1 := by
      have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
      rwa [literal_norm_atom_slot, literal_norm_atom_slot,
        valueLiteral_atom_slot hl2, valueLiteral_atom_slot hl1] at h1
    have hpos : p'.2 = p.2 := by
      obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
      obtain ⟨hlt', hpre'⟩ := mem_zipIdx_iff'.mp hp'
      have hord : f.order[p'.2] = f.order[p.2] := by
        rw [hpre', hslot, ← hpre]
      exact (List.getElem_inj hnd).mp hord
    rw [hpos, hlit]
  · -- pin / falsifier: disjoint slots
    exfalso
    obtain ⟨p, hp, v, l, hv, hl1, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨p', hp', hk', q', hq', l', hl2, hkeep', htk', rfl⟩ :=
      mem_canonicalFalsifiers.mp he'
    have hlit : l'.negate.norm = l.norm := hlit0
    have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
    rw [literal_negate_norm_atom_slot, literal_norm_atom_slot,
      valueLiteral_atom_slot hl1, valueLiteral_atom_slot hl2] at h1
    have hpinmem : p.1 ∈ f.order := order_mem_of_zipIdx hp
    exact hk' (h1.symm ▸ hpinmem)
  · -- falsifier / pin: disjoint slots
    exfalso
    obtain ⟨p, hp, hk, q, hq, l, hl1, hkeep, htk, rfl⟩ :=
      mem_canonicalFalsifiers.mp he
    obtain ⟨p', hp', v', l', hv', hl2, rfl⟩ := mem_canonicalPins.mp he'
    have hlit : l'.norm = l.negate.norm := hlit0
    have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
    rw [literal_negate_norm_atom_slot, literal_norm_atom_slot,
      valueLiteral_atom_slot hl1, valueLiteral_atom_slot hl2] at h1
    have hpinmem : p'.1 ∈ f.order := order_mem_of_zipIdx hp'
    exact hk (h1 ▸ hpinmem)
  · -- falsifier / falsifier
    obtain ⟨p, hp, hk, q, hq, l, hl1, hkeep, htk, rfl⟩ :=
      mem_canonicalFalsifiers.mp he
    obtain ⟨p', hp', hk', q', hq', l', hl2, hkeep', htk', rfl⟩ :=
      mem_canonicalFalsifiers.mp he'
    have hlit : l'.negate.norm = l.negate.norm := hlit0
    rw [hlit]

/-- **F8 (distinctness)** for the canonical trail. -/
theorem canonicalTrail_distinct {orig : List Domain} {f : BranchFrame}
    (hnd : f.order.Nodup) :
    TrailLiteralsDistinct (canonicalTrail orig f) := by
  refine ⟨fun e he e' he' hl => canonicalTrail_norm_unique hnd he he' hl, ?_⟩
  rw [canonicalTrail, List.nodup_append]
  refine ⟨canonicalPins_nodup f, canonicalFalsifiers_nodup, ?_⟩
  intro a ha b hb
  intro heq
  have has := canonicalPins_slot ha
  obtain ⟨p, hp, hk, hbs⟩ := canonicalFalsifiers_slot hb
  rw [heq] at has
  rw [hbs] at has
  exact hk has

/-- **R1 CORE: THE CANONICAL RESUME IS REACHABLE.** Every missing-checkpoint
resume's successor state satisfies the full eight-field `ReachableState`
of the frame's own box — the pending frame is its own retained snapshot. -/
theorem resumePendingBase_reachable {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {f : BranchFrame}
    (h : ReachableState leaf orig bs) (hb : PendingBacked orig f) :
    ReachableState leaf orig (resumePendingBase orig bs f) where
  length_ok := hb.full_len
  full_fits := hb.fit
  pins_forced := pins_forced_canonical hb.shape hb.pins hb.fit
  agrees := agrees_canonicalTrail hb.shape hb.fit hb.full_len
  narrowing_complete := narrowing_complete_canonical hb.shape hb.full_len
  wf := canonicalTrail_wellFormed h.wf.2.2.2.2
  sorted := canonicalTrail_sorted orig f
  distinct := canonicalTrail_distinct hb.pins.1

/-- R1d: the synchronised resume (`syncAll` of the canonical base) is
reachable as well; the only new input is that every leaf solution fits the
box (the explanation clauses of the synchronised literals are valid over the
ORIGINAL domains). -/
theorem resumePending_reachable {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {f : BranchFrame}
    (h : ReachableState leaf orig bs) (hb : PendingBacked orig f)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig (resumePending orig bs f) :=
  syncAll_reachable (resumePendingBase_reachable h hb) hfits

/-- **R1 CONSUMER (route (b))**: the missing-checkpoint consume resumes a
reachable branch — the successor's `ReachableState` at the predecessor's
own box, given the predecessor's reachability and the pending frame's own
backing. The R2 producer must supply `PendingBacked` at the decide-arm
push (its `nodup` field needs a compiled-domains `Nodup` fact). -/
theorem stepConsume_reachable_missing_checkpoint {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest)
    (hcp : checkpointAt cfg.checkpoints f.level = none)
    (h : stepConsume cfg = some next)
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hb : PendingBacked cfg.orig f)
    (hfits : ∀ a, leaf a = true → a.Fits cfg.orig) :
    ReachableState leaf cfg.orig next.branch := by
  rw [stepConsume_branch_of_no_checkpoint hp hcp h]
  exact resumePending_reachable hreach hb hfits

/-! ## §5 R2a: pending-side producers, preservation and the run invariant

R2a PRODUCES `PendingBacked` at the DECIDE push and PRESERVES it on every
arm, so consume sites take the backing from the run invariant instead of
assuming it.

* §5.1 the prefix-pin discipline `PrefixPinned` (the `pins` field's own
  proposition, factored out) and the pending-stack contract
  `PendingBackedList`;
* §5.2 the split producers: the pushed SIBLING and the pinned CHILD of a
  reachable split are both backed — `full_len`/`fit` from the parent's
  `ReachableState` box facts, `pins` from the parent's prefix discipline
  (the one genuinely new parent-side fact, stated as a named residual),
  `shape` from the run box;
* §5.3 retained-frame list preservation: propagation, the analyze site,
  local exclusion, the chronological fallback, the skip and the jump
  leave the pending stack unchanged; decide pushes the backed sibling in
  front of the (backed) older frames; consume drops its head and keeps
  the (backed) deeper frames;
* §5.4 the prefix discipline through the arms: the split extends it by
  the split data's own pin (`prefixPinned_append`), propagation narrows
  the frame (`filterFrame_prefix`), the jump restores a checkpoint frame
  (`perform_prefix`: `filterFrame` + the closure's fuel-narrowing,
  `explainedClosure_prefix`), and consume restores the pending head,
  whose discipline is available from its own backing;
* §5.5 `PendingSideInv` — the run-level bundle (branch prefix discipline,
  backed pending stack, checkpoint-frame prefix discipline) with one
  preservation lemma per transition, and the consume consumer that
  discharges `stepConsume_reachable_missing_checkpoint`'s backing premise
  from the invariant (NO backing is assumed at the consume site).

NO `sorry`, NO custom axiom, and no domain-Nodup hypothesis (the R0
first-occurrence emission already handles duplicated domain entries).
The producers are parametric in the original box and the frame's
remaining domains: sparse domains and deep/shallow pending stacks are
covered by the same lemmas (no density or depth hypothesis occurs).
-/

/-! ### §5.1 The prefix-pin discipline and the stack contract -/

/-- The `pins` field IS the prefix discipline (definitional). -/
theorem PendingBacked.prefixPinned {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) : PrefixPinned f :=
  hb.pins

/-- The empty decision order pins nothing. -/
theorem prefixPinned_nil (doms : List Domain) :
    PrefixPinned (⟨doms, []⟩ : BranchFrame) :=
  ⟨by simp, by intro k hk; exact absurd hk (by simp)⟩

/-- THE DECISION EXTENSION of the prefix discipline: pinning a fresh live
slot keeps every decided slot pinned (the new slot is pinned by the split
data's own literal). -/
theorem prefixPinned_pin {f : BranchFrame} {k : Nat} {v : Value}
    {l : Literal} (hpre : PrefixPinned f) (hfresh : k ∉ f.order)
    (hklt : k < f.doms.length)
    (hl : valueLiteral k v = some l) :
    PrefixPinned (f.pin k v) := by
  refine ⟨?_, ?_⟩
  · rw [BranchFrame.pin_order]
    exact List.nodup_append.mpr
      ⟨hpre.1, by simp, by
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact fun heq => hfresh (heq ▸ ha)⟩
  · intro k' hk'
    rw [BranchFrame.pin_order, List.mem_append, List.mem_singleton] at hk'
    rcases hk' with hk'ord | rfl
    · obtain ⟨v', hv', l', hl'⟩ := hpre.2 k' hk'ord
      have hne : k ≠ k' := fun hkk => hfresh (hkk ▸ hk'ord)
      refine ⟨v', ?_, l', hl'⟩
      rw [BranchFrame.pin_doms, getElem?_set_of_ne hne.symm]
      exact hv'
    · refine ⟨v, ?_, l, hl⟩
      rw [BranchFrame.pin_doms, List.getElem?_set_self hklt]
      simp

/-- A live slot of a pinned frame is not decided: the order's slots are
singletons. -/
theorem not_mem_order_of_split {f : BranchFrame} {l : Literal} {k : Nat}
    {v : Value} {vs : Domain} {σ : List Nat} (hsplit : splitData f σ = some (l, k, v, vs))
    (hpins : PrefixPinned f) : k ∉ f.order := by
  intro hk
  obtain ⟨v', hv', l', hl'⟩ := hpins.2 k hk
  have hspec := (splitData_spec hsplit).1
  have hvs : vs.enum ≠ [] := SparseRun.Frame.splitData_sibling_ne_nil hsplit
  have heq : [v'] = v :: vs.enum := by
    have h := hv'
    rw [hspec] at h
    exact (Option.some.inj h).symm
  have hlen : vs.enum.length = 0 := by
    have := congrArg List.length heq
    simpa using this
  exact hvs (List.length_eq_zero_iff.mp hlen)

/-- A whole pending stack is backed. -/
def PendingBackedList (orig : List Domain) (L : List BranchFrame) : Prop :=
  ∀ f ∈ L, PendingBacked orig f

theorem pendingBackedList_nil (orig : List Domain) :
    PendingBackedList orig [] := by
  intro f hf
  exact absurd hf (List.not_mem_nil)

theorem pendingBackedList_mem {orig : List Domain} {L : List BranchFrame}
    {f : BranchFrame} (h : PendingBackedList orig L) (hf : f ∈ L) :
    PendingBacked orig f := h f hf

theorem pendingBackedList_cons {orig : List Domain} {f : BranchFrame}
    {L : List BranchFrame} (hf : PendingBacked orig f)
    (hL : PendingBackedList orig L) : PendingBackedList orig (f :: L) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hL g hg

/-- DEEP-FRAME EXTRACTION: a backed cons stack is a backed head plus a
backed tail — the shape a consume/retirement step consumes. -/
theorem pendingBackedList_of_cons {orig : List Domain} {f : BranchFrame}
    {L : List BranchFrame} (h : PendingBackedList orig (f :: L)) :
    PendingBacked orig f ∧ PendingBackedList orig L :=
  ⟨h f (List.mem_cons_self ..), fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

/-- Backing is closed under sublists (retirement only ever removes
frames). -/
theorem pendingBackedList_sublist {orig : List Domain}
    {L L' : List BranchFrame} (h : PendingBackedList orig L)
    (hs : L'.Sublist L) : PendingBackedList orig L' :=
  fun f hf => h f (hs.subset hf)

/-! ### §5.2 The split producers (the decide push and the pinned child) -/

/-- **R2a PRODUCER — THE PUSHED SIBLING.** The pending alternative pushed
by the decide arm of a reachable split is backed: `full_len`, `fit` and
`pins` are inherited from the parent's backing (the sibling only retires
the selected slot's head), `shape` from the run box. No density, depth or
domain-Nodup hypothesis. -/
theorem pendingBacked_split_sibling {orig : List Domain} {f : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : f.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hfresh : k ∉ f.order)
    (hb : PendingBacked orig f) :
    PendingBacked orig (f.retire k vs) := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons hsplit
  refine ⟨?_, ?_, ?_, hb.shape⟩
  · simpa [fullDomains, Frame.domains, BranchFrame.retire_doms] using hb.full_len
  · refine ⟨?_, ?_⟩
    · rw [BranchFrame.retire_order]
      exact hb.pins.1
    · intro k' hk'
      rw [BranchFrame.retire_order] at hk'
      obtain ⟨v', hv', l', hl'⟩ := hb.pins.2 k' hk'
      have hne : k ≠ k' := fun hkk => hfresh (hkk ▸ hk')
      refine ⟨v', ?_, l', hl'⟩
      rw [BranchFrame.retire_doms, getElem?_set_of_ne hne.symm]
      exact hv'
  · intro i w hw
    have hw' : w ∈ (f.doms.set k vs).getD i Dom.empty := by
      simpa [fullDomains, Frame.domains, BranchFrame.retire_doms] using hw
    have hsub : ∀ w' ∈ vs, w' ∈ f.doms.getD k Dom.empty := by
      intro w' hw''
      rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
      refine (DomainLike.mem_iff _ _).mpr ?_
      rw [domElems_eq_enum, hde]
      exact List.mem_cons_of_mem v
        (by simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw'')
    exact hb.fit i w (getD_set_subset hsub i w hw')

/-- **R2a PRODUCER — THE PINNED CHILD.** The child frame of a reachable
split is backed: its full box is inside the parent's (only the selected
slot is pinned), its decision order extends the parent's by the fresh
selected slot, its prefix discipline is the parent's extended by the split
data's own pin, and the run box types it. -/
theorem pendingBacked_split_child {orig : List Domain} {f : BranchFrame}
    {k : Nat} {v : Value} {vs : Domain} {l : Literal}
    (hsplit : f.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hwl : valueLiteral k v = some l) (hfresh : k ∉ f.order)
    (hb : PendingBacked orig f) :
    PendingBacked orig (f.pin k v) := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons hsplit
  refine ⟨?_, ?_, ?_, hb.shape⟩
  · simpa [fullDomains, Frame.domains, BranchFrame.pin_doms] using hb.full_len
  · exact prefixPinned_pin hb.pins hfresh
      (List.getElem?_eq_some_iff.mp hd).1 hwl
  · intro i w hw
    have hw' : w ∈ (f.doms.set k (Dom.ofList [v])).getD i Dom.empty := by
      simpa [fullDomains, Frame.domains, BranchFrame.pin_doms] using hw
    have hsub : ∀ w' ∈ (Dom.ofList [v] : Domain), w' ∈ f.doms.getD k Dom.empty := by
      intro w' hw''
      have hw'v : w' = v := by
        have hmem : w' ∈ Dom.enum (Dom.ofList [v]) :=
          (DomainLike.mem_iff _ _).mp hw''
        rwa [Dom.enum_ofList, List.mem_singleton] at hmem
      subst hw'v
      rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
      exact (DomainLike.mem_iff _ _).mpr (by
        rw [domElems_eq_enum, hde]; exact List.mem_cons_self ..)
    exact hb.fit i w (getD_set_subset hsub i w hw')

/-- **R2a CONFIG-LEVEL PRODUCER — DECIDE PUSH.** The frame the decide arm
actually pushes (`cfg.branch.frame.retire k vs`, the sibling of the split)
is backed, from the parent configuration's reachability, the parent's
prefix discipline and the run box's typing. -/
theorem pendingBacked_decide_push {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (cfg.branch.frame.retire k vs) :=
  pendingBacked_split_sibling (splitData_spec hsplit).1
    (not_mem_order_of_split hsplit hpins)
    ⟨hreach.length_ok, hpins, hreach.full_fits, hshape⟩

/-- **R2a CONFIG-LEVEL PRODUCER — THE PINNED CHILD** (the decide/skip arm's
new current frame). -/
theorem pendingBacked_decide_child {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (cfg.branch.frame.pin k v) := by
  have hparts := splitData_spec hsplit
  exact pendingBacked_split_child hparts.1 hparts.2
    (not_mem_order_of_split hsplit hpins)
    ⟨hreach.length_ok, hpins, hreach.full_fits, hshape⟩

/-! ### §5.3 Retained-frame preservation across the arms -/

theorem stepPropagate_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf}
    (d : ProductiveDeduction leaf cfg.branch)
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepPropagate cfg d).pending := by
  simpa only [stepPropagate_pending] using h

theorem stepDecideSkip_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {k : Nat} {v : Value}
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepDecideSkip cfg k v).pending := by
  simpa only [stepDecideSkip] using h

theorem stepAnalyzeConflict_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {c : Clause}
    {learned : List Clause} (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepAnalyzeConflict cfg c learned).pending := by
  simpa only [stepAnalyzeConflict_pending] using h

theorem stepAnalyzeConflictCounted_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {c : Clause}
    {learned : List Clause} {n : Nat} (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepAnalyzeConflictCounted cfg c learned n).pending := by
  simpa only [stepAnalyzeConflictCounted_pending] using h

theorem stepLocalExclude_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {learned : List Clause}
    {r : DeadRegion} (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepLocalExclude cfg learned r).pending := by
  simpa only [stepLocalExclude_pending] using h

theorem stepChronologicalFallback_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepChronologicalFallback cfg r).pending := by
  simpa only [stepChronologicalFallback] using h

/-- THE JUMP keeps every pending frame: the deep alternatives are only
retained (the jump narrows the current branch and the checkpoint list). -/
theorem stepLearnBackjumpAssert_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepLearnBackjumpAssert cfg p ev restored).pending := by
  simpa only [stepLearnBackjumpAssert] using h

/-- DECIDE PUSH + RETAINED FRAMES: after a split the stack is the backed
sibling in front of the predecessor's (backed) alternatives. -/
theorem stepDecide_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame)
    (hshape : ShapeTypedDomains orig)
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepDecide cfg k v vs l).pending := by
  rw [stepDecide_pending]
  exact pendingBackedList_cons
    (pendingBacked_decide_push hsplit hreach hpins hshape) h

/-- CONSUME drops its head and keeps the deeper frames' backing. -/
theorem stepConsume_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (h : stepConsume cfg = some next)
    (hpend : PendingBackedList orig cfg.pending) :
    PendingBackedList orig next.pending := by
  obtain ⟨-, hnext, -, -, -⟩ := stepConsume_some_shape hp h
  intro g hg
  rw [hnext] at hg
  exact hpend g (by rw [hp]; exact List.mem_cons_of_mem f hg)

/-- **R2a CONSUME CONSUMER**: the missing-checkpoint resume of a reachable
consume step is reachable at the predecessor's own box, with the head's
backing DERIVED from the run-level stack invariant — no `PendingBacked`
premise at the consume site. -/
theorem stepConsume_reachable_of_backedList {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest)
    (hcp : checkpointAt cfg.checkpoints f.level = none)
    (h : stepConsume cfg = some next)
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hpend : PendingBackedList cfg.orig cfg.pending)
    (hfits : ∀ a, leaf a = true → a.Fits cfg.orig) :
    ReachableState leaf cfg.orig next.branch :=
  stepConsume_reachable_missing_checkpoint hp hcp h hreach
    (hpend f (by rw [hp]; exact List.mem_cons_self ..)) hfits

/-- The consume site's head frame is backed (for consumers that need the
frame's own backing rather than the resumed state's reachability). -/
theorem stepConsume_head_pendingBacked {orig : List Domain}
    {cfg : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (hpend : PendingBackedList orig cfg.pending) :
    PendingBacked orig f :=
  hpend f (by rw [hp]; exact List.mem_cons_self ..)

/-! ### §5.4 The prefix discipline through the arms -/

/-- Propagation narrows the frame by `filterFrame`, which keeps the decision
order (and so the prefix discipline). -/
theorem stepPropagate_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (d : ProductiveDeduction leaf cfg.branch)
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepPropagate cfg d).branch.frame := by
  rw [stepPropagate_branch_frame]
  exact h.filterFrame d.filtered

/-- The split's pinned child extends the decision order by the split data's
own fresh pin. -/
theorem stepDecide_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepDecide cfg k v vs l).branch.frame := by
  have hspec := splitData_spec hsplit
  obtain ⟨d, hd, -⟩ := exists_dom_of_enum_cons hspec.1
  show PrefixPinned (cfg.branch.frame.pin k v)
  exact prefixPinned_pin h (not_mem_order_of_split hsplit h)
    (List.getElem?_eq_some_iff.mp hd).1 hspec.2

/-- The redundant-pin skip's child extends the decision order by the split
data's own fresh pin (the recorded pin is the same literal). -/
theorem stepDecideSkip_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepDecideSkip cfg k v).branch.frame := by
  have hspec := splitData_spec hsplit
  obtain ⟨d, hd, -⟩ := exists_dom_of_enum_cons hspec.1
  show PrefixPinned (cfg.branch.frame.pin k v)
  exact prefixPinned_pin h (not_mem_order_of_split hsplit h)
    (List.getElem?_eq_some_iff.mp hd).1 hspec.2

/-- The explained closure only ever narrows the frame by `filterFrame`
(each step's frame comes from the deduction's own `filtered` call), so it
preserves the prefix discipline. -/
theorem explainedClosure_prefixPinned (orig : List Domain)
    (original : List Clause) (props : List Propagator) {bs : BranchState leaf}
    (h : PrefixPinned bs.frame) :
    PrefixPinned (explainedClosure orig original props bs).frame := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → PrefixPinned bs.frame →
      PrefixPinned (explainedClosure orig original props bs).frame from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) h
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hp
      rw [explainedClosure]
      split
      · exact hp
      · rename_i d _
        exfalso
        have := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hp
      rw [explainedClosure]
      split
      · exact hp
      · rename_i d _
        have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
          simp only [stepNarrowSync_frame]
          have := d.decreases
          omega
        have hstep : PrefixPinned (stepNarrowSync orig bs d).frame := by
          rw [stepNarrowSync_frame]
          exact hp.filterFrame d.filtered
        exact ih (stepNarrowSync orig bs d) hmass hstep

/-- The restored-and-narrowed state of a plan keeps the checkpoint frame's
prefix discipline (`filterFrame` preserves it). -/
theorem restoreNarrow_prefix {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    PrefixPinned p.checkpoint.frame → PrefixPinned s.frame := by
  intro hp
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · next g hg =>
      cases h
      show PrefixPinned g
      exact hp.filterFrame hg

/-- The complete learn/backjump/assert transition keeps the prefix
discipline of the SELECTED checkpoint's frame (restoration keeps it, the
assertion filter keeps it, the resumed closure keeps it). The residual is
exactly "the selected checkpoint frame's prefix is pinned", which the run
invariant `PendingSideInv.checkpoints` maintains. -/
theorem perform_prefix {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    PrefixPinned p.checkpoint.frame → PrefixPinned s.frame := by
  intro hp
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none => rw [hr] at h; cases h
  | some t =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      have hsync : PrefixPinned (syncAll orig t).frame := by
        rw [syncAll_frame]
        exact restoreNarrow_prefix hr hp
      exact explainedClosure_prefixPinned orig original props hsync

theorem stepLearnBackjumpAssert_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf}
    (hperf : p.perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hpcp : PrefixPinned p.checkpoint.frame) :
    PrefixPinned (stepLearnBackjumpAssert cfg p ev restored).branch.frame := by
  show PrefixPinned restored.frame
  exact perform_prefix hperf hpcp

/-- Consume restores the pending head, whose discipline comes from its own
backing (never from the failed branch). -/
theorem stepConsume_prefixPinned {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (h : stepConsume cfg = some next)
    (hpend : PendingBackedList orig cfg.pending) :
    PrefixPinned next.branch.frame := by
  obtain ⟨hframe, -, -, -, -⟩ := stepConsume_some_shape hp h
  rw [hframe]
  exact (hpend f (by rw [hp]; exact List.mem_cons_self ..)).prefixPinned

theorem stepAnalyzeConflict_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepAnalyzeConflict cfg c learned).branch.frame := by
  show PrefixPinned cfg.branch.frame
  exact h

theorem stepAnalyzeConflictCounted_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause} {n : Nat}
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepAnalyzeConflictCounted cfg c learned n).branch.frame := by
  show PrefixPinned cfg.branch.frame
  exact h

theorem stepLocalExclude_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepLocalExclude cfg learned r).branch.frame := by
  show PrefixPinned cfg.branch.frame
  exact h

theorem stepChronologicalFallback_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (h : PrefixPinned cfg.branch.frame) :
    PrefixPinned (stepChronologicalFallback cfg r).branch.frame := by
  show PrefixPinned cfg.branch.frame
  exact h

/-! ### §5.5 `PendingSideInv`: the run-level pending-side invariant -/

/-- THE PENDING-SIDE RUN INVARIANT (R2a): the current branch's prefix is
pinned (so the NEXT split's pushed sibling can be produced), every pending
alternative is backed, and every saved checkpoint's frame prefix is pinned
(so a jump's restoration keeps the branch discipline). This is the new
parent-side premise the decide producer needs; it is preserved by every
transition and instantiated at the real root, so it is an invariant of the
real run — not an assumed `PendingBacked` at the consume site. -/
structure PendingSideInv (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Prop where
  /-- the current branch's chosen prefix is pinned (the decide producer's
      parent-side premise) -/
  branch : PrefixPinned cfg.branch.frame
  /-- every pending alternative is backed -/
  pending : PendingBackedList orig cfg.pending
  /-- every saved checkpoint's frame prefix is pinned -/
  checkpoints : ∀ cp ∈ cfg.checkpoints, PrefixPinned cp.frame

theorem PendingSideInv.init {prio : List Nat} {actBump : Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) :
    PendingSideInv orig (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) where
  branch := prefixPinned_nil orig
  pending := pendingBackedList_nil orig
  checkpoints := by
    intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact prefixPinned_nil orig

theorem PendingSideInv.stepPropagate {orig : List Domain}
    {cfg : SchedulerConfig leaf} (h : PendingSideInv orig cfg)
    (d : ProductiveDeduction leaf cfg.branch) :
    PendingSideInv orig (stepPropagate cfg d) where
  branch := stepPropagate_prefixPinned d h.branch
  pending := stepPropagate_pendingBackedList d h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

theorem PendingSideInv.stepDecide {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (h : PendingSideInv orig cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    PendingSideInv orig (stepDecide cfg k v vs l) where
  branch := stepDecide_prefixPinned hsplit h.branch
  pending := stepDecide_pendingBackedList hsplit hreach h.branch hshape h.pending
  checkpoints := by
    intro cp hcp
    have hck : (LeanFzn.Solver.UIP.stepDecide cfg k v vs l).checkpoints
        = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
    rw [hck] at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · show PrefixPinned cfg.branch.frame
      exact h.branch
    · exact h.checkpoints cp hcp

theorem PendingSideInv.stepDecideSkip {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (h : PendingSideInv orig cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    PendingSideInv orig (stepDecideSkip cfg k v) where
  branch := stepDecideSkip_prefixPinned hsplit h.branch
  pending := stepDecideSkip_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

theorem PendingSideInv.stepAnalyzeConflict {orig : List Domain}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (h : PendingSideInv orig cfg) :
    PendingSideInv orig (stepAnalyzeConflict cfg c learned) where
  branch := stepAnalyzeConflict_prefixPinned h.branch
  pending := stepAnalyzeConflict_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

theorem PendingSideInv.stepAnalyzeConflictCounted {orig : List Domain}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause} {n : Nat}
    (h : PendingSideInv orig cfg) :
    PendingSideInv orig (stepAnalyzeConflictCounted cfg c learned n) where
  branch := stepAnalyzeConflictCounted_prefixPinned h.branch
  pending := stepAnalyzeConflictCounted_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

theorem PendingSideInv.stepLocalExclude {orig : List Domain}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (h : PendingSideInv orig cfg) :
    PendingSideInv orig (stepLocalExclude cfg learned r) where
  branch := stepLocalExclude_prefixPinned h.branch
  pending := stepLocalExclude_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

theorem PendingSideInv.stepChronologicalFallback {orig : List Domain}
    {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (h : PendingSideInv orig cfg) :
    PendingSideInv orig (stepChronologicalFallback cfg r) where
  branch := stepChronologicalFallback_prefixPinned h.branch
  pending := stepChronologicalFallback_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp (hcp : cp ∈ cfg.checkpoints)

/-- THE JUMP preserves the invariant whenever the selected checkpoint's
frame prefix is pinned (the runtime plan is `BackjumpPlan.ofCheckpoint cp`
with `cp` from `checkpointAt`, so the invariant's checkpoint component
supplies it — see `PendingSideInv.stepLearnBackjumpAssert_ofCheckpoint`). -/
theorem PendingSideInv.stepLearnBackjumpAssert {orig : List Domain}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf} (h : PendingSideInv orig cfg)
    (hperf : p.perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hpcp : PrefixPinned p.checkpoint.frame) :
    PendingSideInv orig (stepLearnBackjumpAssert cfg p ev restored) where
  branch := stepLearnBackjumpAssert_prefixPinned hperf hpcp
  pending := stepLearnBackjumpAssert_pendingBackedList h.pending
  checkpoints := by
    intro cp hcp
    have hck : (LeanFzn.Solver.UIP.stepLearnBackjumpAssert cfg p ev restored).checkpoints
        = cfg.checkpoints.filter (fun cp => cp.level ≤ p.target) := rfl
    rw [hck] at hcp
    exact h.checkpoints cp (List.mem_filter.mp hcp).1

/-- The runtime plan construction: `p := BackjumpPlan.ofCheckpoint cp …` is
the plan `backjumpStep` builds, so the checkpoint component of the
invariant discharges the plan premise directly. -/
theorem PendingSideInv.stepLearnBackjumpAssert_ofCheckpoint {orig : List Domain}
    {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf} {asserting : Literal}
    {learned : Clause} (h : PendingSideInv orig cfg)
    (hcp : cp ∈ cfg.checkpoints)
    (hperf : (BackjumpPlan.ofCheckpoint cp cfg.branch asserting learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    PendingSideInv orig (LeanFzn.Solver.UIP.stepLearnBackjumpAssert cfg
      (BackjumpPlan.ofCheckpoint cp cfg.branch asserting learned) ev restored) := by
  have hpcp : PrefixPinned
      (BackjumpPlan.ofCheckpoint cp cfg.branch asserting learned).checkpoint.frame :=
    h.checkpoints cp hcp
  exact h.stepLearnBackjumpAssert hperf hpcp

/-- A lookup's checkpoint frame prefix is pinned (the consumer shape of the
jump arm's premise, wired by `checkpointAt_mem`). -/
theorem PendingSideInv.prefixPinned_of_checkpointAt {orig : List Domain}
    {cfg : SchedulerConfig leaf} {target : Nat} {cp : DecisionCheckpoint leaf}
    (h : PendingSideInv orig cfg) (hat : checkpointAt cfg.checkpoints target = some cp) :
    PrefixPinned cp.frame :=
  h.checkpoints cp (checkpointAt_mem hat)

/-- CONSUME preserves the invariant: the resumed branch is the pending
head (its own backing pins its prefix), the stack loses its head, and the
retired checkpoints are a sublist. -/
theorem PendingSideInv.stepConsume {orig : List Domain}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (h : PendingSideInv orig cfg) (hp : cfg.pending = f :: rest)
    (hc : stepConsume cfg = some next) :
    PendingSideInv orig next where
  branch := stepConsume_prefixPinned hp hc h.pending
  pending := stepConsume_pendingBackedList hp hc h.pending
  checkpoints := by
    intro cp hcp
    exact h.checkpoints cp ((stepConsume_checkpoints_sublist hp hc).subset hcp)

end LeanFzn.Solver.UIP
