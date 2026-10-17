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

import LeanFzn.Solver.Propagation.BackjumpFrontier
import LeanFzn.Solver.Propagation.Proofs.BranchState
import LeanFzn.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Solver.UIP.Proofs.SchedulerResume
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §0 The pending frame's own sub-box provenance -/

/-- PENDING-BACKING (R1): the pending alternative is its own retained
snapshot. `full_len`/`fit` are the sub-box facts (from the split that
pushed the frame); `pins` records that every chosen prefix value has a
decision literal (so the canonical trail can re-force the prefix);
`shape` is the box typing the semantic fields need. Distinctness needs NO
domain hypothesis: duplicated original values (admitted by the accepted
`var {..., k, ..., k, ...}` source shape) emit their retire entry at the
FIRST occurrence only — the runtime dedup of `slotFalsifiers`. -/
structure PendingBacked (orig : List Domain) (f : BranchFrame) : Prop where
  /-- the full box of the frame has the original length -/
  full_len : (fullDomains f).length = orig.length
  /-- every chosen prefix position has a decision literal -/
  pins : ∀ (s : Nat) (hs : s < f.2.length),
    ∃ l : Literal, valueLiteral s (f.2[s]'hs) = some l
  /-- the frame's whole box is inside the original box -/
  fit : ∀ i v, v ∈ (fullDomains f).getD i [] → v ∈ orig.getD i []
  /-- slot-wise typing of the original box -/
  shape : ShapeTypedDomains orig

/-- Convenience: `full_len` bounds the prefix. -/
theorem PendingBacked.prefix_le {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) : f.2.length ≤ orig.length := by
  have h := hb.full_len
  rw [fullDomains_length] at h
  omega

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
    l ∈ dom.filterMap (valueLiteral j) ↔ w ∈ dom := by
  constructor
  · intro hmem
    obtain ⟨w', hw'mem, hw'⟩ := List.mem_filterMap.mp hmem
    have hw'w : w' = w := valueLiteral_injective hw' hw
    subst hw'w
    exact hw'mem
  · intro hmem
    exact List.mem_filterMap.mpr ⟨w, hmem, hw⟩

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

/-- Membership in `canonicalPins`: an entry is a pin of a chosen position
that has a decision literal. -/
theorem mem_canonicalPins {pre : List Value} {e : TrailEntry} :
    e ∈ canonicalPins pre ↔
      ∃ p ∈ pre.zipIdx, ∃ l : Literal,
        valueLiteral p.2 p.1 = some l ∧
          e = { literal := l.norm, level := p.2 + 1, reason := none } := by
  rw [canonicalPins, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, he⟩
    rw [canonicalPinEntry, Option.map_eq_some_iff] at he
    obtain ⟨l, hl, hpe⟩ := he
    exact ⟨p, hp, l, hl, hpe.symm⟩
  · rintro ⟨p, hp, l, hl, rfl⟩
    exact ⟨p, hp, by simp [canonicalPinEntry, hl]⟩

/-- Level bound of a pin: it sits at the level its decision opened. -/
theorem canonicalPins_level_le {pre : List Value} {e : TrailEntry}
    (he : e ∈ canonicalPins pre) : e.level ≤ pre.length := by
  obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
  obtain ⟨hlt, -⟩ := mem_zipIdx_iff'.mp hp
  simp only
  omega

/-- Pins are normalized entries with no reason. -/
theorem canonicalPins_literal_norm {pre : List Value} {e : TrailEntry}
    (he : e ∈ canonicalPins pre) : e.literal = e.literal.norm := by
  obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
  exact (literal_norm_idem l).symm

theorem canonicalPins_reason_none {pre : List Value} {e : TrailEntry}
    (he : e ∈ canonicalPins pre) : e.reason = none := by
  obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
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

theorem canonicalPins_sorted (pre : List Value) :
    TrailLevelSorted (canonicalPins pre) := by
  rw [canonicalPins, TrailLevelSorted, List.pairwise_filterMap]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_zipIdx, Nat.zero_add]
  intro b hb b' hb'
  rw [canonicalPinEntry, Option.map_eq_some_iff] at hb hb'
  obtain ⟨l, hl, hbl⟩ := hb
  obtain ⟨l', hl', hb'l⟩ := hb'
  subst hbl
  subst hb'l
  simp only
  omega

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
of a FIRST occurrence, at its position's slot, of a value outside the
kept pins. -/
theorem mem_slotFalsifiers {orig : List Domain} {f : BranchFrame} {i : Nat}
    {dom : Domain} {e : TrailEntry} :
    e ∈ slotFalsifiers orig f i dom ↔
      ∃ p ∈ (orig.getD (f.2.length + i) []).zipIdx, ∃ l : Literal,
        valueLiteral (f.2.length + i) p.1 = some l ∧
        l ∉ dom.filterMap (valueLiteral (f.2.length + i)) ∧
        l ∉ ((orig.getD (f.2.length + i) []).take p.2).filterMap
              (valueLiteral (f.2.length + i)) ∧
        e = { literal := l.negate.norm, level := f.2.length,
              reason := none } := by
  unfold slotFalsifiers
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hmap⟩
    cases hv : valueLiteral (f.2.length + i) p.1 with
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
      ∃ p ∈ f.1.zipIdx, ∃ q ∈ (orig.getD (f.2.length + p.2) []).zipIdx,
        ∃ l : Literal,
        valueLiteral (f.2.length + p.2) q.1 = some l ∧
        l ∉ p.1.filterMap (valueLiteral (f.2.length + p.2)) ∧
        l ∉ ((orig.getD (f.2.length + p.2) []).take q.2).filterMap
              (valueLiteral (f.2.length + p.2)) ∧
        e = { literal := l.negate.norm, level := f.2.length,
              reason := none } := by
  rw [canonicalFalsifiers, List.mem_flatten]
  constructor
  · rintro ⟨inner, hinner, he⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hinner
    obtain ⟨q, hq, l, hv, hk, htk, rfl⟩ := mem_slotFalsifiers.mp he
    exact ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩
  · rintro ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩
    exact ⟨slotFalsifiers orig f p.2 p.1, List.mem_map.mpr ⟨p, hp, rfl⟩,
      mem_slotFalsifiers.mpr ⟨q, hq, l, hv, hk, htk, rfl⟩⟩

/-- EMISSION: every dropped remaining-slot original value's retire entry is
present (the direction `narrowing_complete` consumes). -/
theorem canonicalFalsifiers_emit {orig : List Domain} {f : BranchFrame}
    {i : Nat} {w : Value} {l : Literal}
    (hi : i < f.1.length) (hw : w ∈ orig.getD (f.2.length + i) [])
    (hl : valueLiteral (f.2.length + i) w = some l)
    (hnot : l ∉ (f.1.getD i []).filterMap (valueLiteral (f.2.length + i))) :
    { literal := l.negate.norm, level := f.2.length, reason := none } ∈
      canonicalFalsifiers orig f := by
  have hget : f.1.getD i [] = f.1[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  rw [hget] at hnot
  obtain ⟨q, hq, hgq, hfirst⟩ := exists_first_of_mem_filterMap
    (List.mem_filterMap.mpr ⟨w, hw, hl⟩ : l ∈ (orig.getD (f.2.length + i)
      []).filterMap (valueLiteral (f.2.length + i)))
  refine mem_canonicalFalsifiers.mpr
    ⟨(f.1[i], i), mem_zipIdx_iff'.mpr ⟨hi, rfl⟩, q, hq, l, hgq, hnot,
      hfirst, rfl⟩

/-- Every falsifier entry sits at the resumed level, is normalized and has
no reason. -/
theorem canonicalFalsifiers_level {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.level = f.2.length := by
  obtain ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
  rfl

theorem canonicalFalsifiers_literal_norm {orig : List Domain}
    {f : BranchFrame} {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.literal = e.literal.norm := by
  obtain ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
  exact (literal_norm_idem l.negate).symm

theorem canonicalFalsifiers_reason_none {orig : List Domain}
    {f : BranchFrame} {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    e.reason = none := by
  obtain ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
  rfl

/-- Every entry of a slot's falsifier list sits at the resumed level. -/
theorem slotFalsifiers_level {orig : List Domain} {f : BranchFrame} {i : Nat}
    {dom : Domain} {e : TrailEntry} (he : e ∈ slotFalsifiers orig f i dom) :
    e.level = f.2.length := by
  obtain ⟨q, hq, l, hv, hk, htk, rfl⟩ := mem_slotFalsifiers.mp he
  rfl

/-- The falsifiers are level-sorted (constant resumed level). -/
theorem canonicalFalsifiers_sorted (orig : List Domain) (f : BranchFrame) :
    TrailLevelSorted (canonicalFalsifiers orig f) := by
  rw [canonicalFalsifiers]
  refine trailLevelSorted_of_const (n := f.2.length)
    (flatten_levels_const (n := f.2.length) ?_)
  intro l hl e hel
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
  exact slotFalsifiers_level hel

/-- Canonical-trail facts: every entry is a normalized, reason-less entry
at or below the resumed level. -/
theorem canonicalTrail_level_le {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalTrail orig f) :
    e.level ≤ f.2.length := by
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
  refine ⟨canonicalPins_sorted f.2, canonicalFalsifiers_sorted orig f, ?_⟩
  intro a ha b hb
  have hb' : b.level = f.2.length := canonicalFalsifiers_level hb
  rw [hb']
  exact canonicalPins_level_le ha

/-- The canonical resume is well-formed: only the learned database survives
from the predecessor. -/
theorem canonicalTrail_wellFormed {orig : List Domain} {f : BranchFrame}
    {bs : BranchState leaf} (hlearn : LearnedEntailed leaf bs.learned) :
    (resumePendingBase orig bs f).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    show e.level ≤ f.2.length
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
    (hshape : ShapeTypedDomains orig) (h : Value.bool b ∈ orig.getD s []) :
    ∀ w ∈ orig.getD s [], ∃ b : Bool, w = Value.bool b := by
  have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s)
    (a := ([] : Domain))
  cases hgt : orig[s]? with
  | none =>
      rw [hlook, hgt] at h
      simp only [Option.getD_none, List.not_mem_nil] at h
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
    (hshape : ShapeTypedDomains orig) (hv : v ∈ orig.getD s []) :
    (∀ w ∈ orig.getD s [], ∃ k : Int, w = Value.int k) ∨
      (∀ w ∈ orig.getD s [], ∃ b : Bool, w = Value.bool b) := by
  cases v with
  | bool b => exact Or.inr (boolShaped_of_mem_bool hshape hv)
  | int i => exact Or.inl (intShaped_of_mem_int hshape hv)
  | setOfInt q =>
      have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s)
        (a := ([] : Domain))
      cases hgt : orig[s]? with
      | none =>
          rw [hlook, hgt] at hv
          simp only [Option.getD_none, List.not_mem_nil] at hv
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
        (a := ([] : Domain))
      cases hgt : orig[s]? with
      | none =>
          rw [hlook, hgt] at hv
          simp only [Option.getD_none, List.not_mem_nil] at hv
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

/-- An indexed remaining slot of a length-correct frame is a real slot. -/
theorem remaining_index_lt_of_mem {orig : List Domain} {f : BranchFrame}
    (hlen : (fullDomains f).length = orig.length) {i : Nat} {w : Value}
    (hw : w ∈ orig.getD (f.2.length + i) []) : i < f.1.length := by
  have h1 : f.2.length + i < orig.length := by
    suffices hnot : ¬ (orig.length ≤ f.2.length + i) by omega
    intro hge
    have hnil : orig.getD (f.2.length + i) [] = [] := by
      cases hlt : orig[f.2.length + i]? with
      | none =>
          rw [List.getD_eq_getElem?_getD, hlt]
          rfl
      | some d =>
          obtain ⟨hlt', -⟩ := List.getElem?_eq_some_iff.mp hlt
          omega
    rw [hnil] at hw
    exact absurd hw (List.not_mem_nil)
  rw [← hlen, fullDomains_length] at h1
  omega

/-- **F5 (narrowing completeness) for the canonical trail**: every dropped
remaining-slot original value carries its retire entry. Needs only the box
typing (pin existence at dropped values) and the frame's length. -/
theorem narrowing_complete_canonical {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hlen : (fullDomains f).length = orig.length) :
    NarrowingComplete (canonicalTrail orig f) orig f := by
  intro i w hw hnot
  have hi : i < f.1.length := remaining_index_lt_of_mem hlen hw
  have hpin : ∃ l, valueLiteral (f.2.length + i) w = some l := by
    rcases shaped_of_mem hshape hw with hint | hbool
    · obtain ⟨k, rfl⟩ := hint w hw
      exact ⟨negNe (f.2.length + i) k, rfl⟩
    · obtain ⟨b, rfl⟩ := hbool w hw
      exact ⟨posBool (f.2.length + i) b, rfl⟩
  obtain ⟨l, hl⟩ := hpin
  have hkeep : l ∉ (f.1.getD i []).filterMap (valueLiteral (f.2.length + i)) :=
    fun hmem => hnot ((valueLiteral_kept_iff hl).mp hmem)
  refine ⟨{ literal := l.negate.norm, level := f.2.length, reason := none },
    List.mem_append.mpr (Or.inr
      (canonicalFalsifiers_emit hi hw hl hkeep)), ?_, ?_⟩
  · show l.negate.norm.atom.slot = f.2.length + i
    rw [literal_negate_norm_atom_slot]
    exact valueLiteral_atom_slot hl
  · exact valueLiteral_negate_norm_valueHolds_false hl

/-- **F4-pins**: canonical pins hold at every frame-covered assignment (no
premises: the covered assignment reads its prefix values). -/
theorem agrees_canonicalPins {f : BranchFrame} :
    ∀ e ∈ canonicalPins f.2, ∀ a, FrameCovers f a →
      e.literal.eval a = some true := by
  intro e he a hcov
  obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
  obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
  obtain ⟨tail, -, rfl⟩ := hcov
  have hslot : (f.2 ++ tail)[l.atom.slot]? = some p.1 := by
    rw [valueLiteral_atom_slot hl]
    rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt, hpre]
  rw [Literal.norm_eval, ← valueHolds_read hslot]
  exact valueLiteral_valueHolds_self hl

/-- **F4-falsifier SEMANTICS**: a retire entry holds at every value the
sibling slot's kept domain still admits (the kept-pin test is by literal,
the domain read by value — the bridge is `valueLiteral` injectivity plus
the typed discipline that excludes the int-view collisions). -/
theorem falsifier_holds_of_not_kept {orig : List Domain} {j : Nat}
    {dom : Domain} {w w' : Value} {l : Literal}
    (hshape : ShapeTypedDomains orig) (hw : w ∈ orig.getD j [])
    (hl : valueLiteral j w = some l)
    (hlk : l ∉ dom.filterMap (valueLiteral j))
    (hdom : ∀ v ∈ dom, v ∈ orig.getD j []) (hw' : w' ∈ dom) :
    l.negate.norm.valueHolds w' = true := by
  have hsh := shaped_of_mem hshape hw
  cases w with
  | bool b =>
      have hl' : l = posBool j b := by simpa [valueLiteral] using hl.symm
      have hbool : ∀ v ∈ orig.getD j [], ∃ b : Bool, v = Value.bool b := by
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
        exact List.mem_filterMap.mpr ⟨Value.bool b', hw', by simp [valueLiteral]⟩
      rw [hl', posBool_negate_norm]
      cases b <;> cases b' <;> simp_all [Literal.valueHolds, posBool]
  | int k =>
      have hl' : l = negNe j k := by simpa [valueLiteral] using hl.symm
      have hint : ∀ v ∈ orig.getD j [], ∃ k : Int, v = Value.int k := by
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
        exact List.mem_filterMap.mpr ⟨Value.int k', hw', by simp [valueLiteral]⟩
      rw [hl', negNe_negate_norm]
      simp [Literal.valueHolds, posNe, Value.intView, hne]
  | setOfInt q => simp [valueLiteral] at hl
  | array q => simp [valueLiteral] at hl

/-- **F4-falsifiers**: canonical falsifiers hold at every frame-covered
assignment (the covered assignment reads a kept value of the slot the
retire entry falsifies). -/
theorem agrees_canonicalFalsifiers {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i [] → v ∈ orig.getD i [])
    (hlen : (fullDomains f).length = orig.length) :
    ∀ e ∈ canonicalFalsifiers orig f, ∀ a, FrameCovers f a →
      e.literal.eval a = some true := by
  intro e he a hcov
  obtain ⟨p, hp, q, hq, l, hl, hlk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
  obtain ⟨hqlt, hqe⟩ := mem_zipIdx_iff'.mp hq
  have hw : q.1 ∈ orig.getD (f.2.length + p.2) [] := by
    rw [← hqe]
    exact List.getElem_mem hqlt
  obtain ⟨hlt, hpre⟩ := mem_zipIdx_iff'.mp hp
  obtain ⟨tail, htailmem, ha⟩ := hcov
  subst ha
  have hfits : (f.2 ++ tail).Fits (Frame.domains f) :=
    FrameCovers.fits ⟨tail, htailmem, rfl⟩
  have htail_len : tail.length = f.1.length := by
    have := hfits.1
    rw [List.length_append, fullDomains_length] at this
    omega
  have hp2 : p.2 < tail.length := by
    rw [htail_len]
    exact hlt
  have hread : (f.2 ++ tail)[f.2.length + p.2]? = some (tail[p.2]'hp2) := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    rw [show f.2.length + p.2 - f.2.length = p.2 from by omega]
    exact List.getElem?_eq_getElem hp2
  have hslot : (f.2 ++ tail)[l.negate.norm.atom.slot]? =
      some (tail[p.2]'hp2) := by
    rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hl]
    exact hread
  have hgetD : f.1.getD p.2 [] = p.1 := by
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem hlt]
    exact hpre
  rw [← valueHolds_read hslot]
  refine falsifier_holds_of_not_kept (j := f.2.length + p.2) hshape hw hl hlk
    ?_ ?_
  · intro v hv
    have hv' : v ∈ f.1.getD p.2 [] := by
      rw [hgetD]
      exact hv
    have hv'' : v ∈ (fullDomains f).getD (f.2.length + p.2) [] := by
      rw [fullDomains_getD_remaining]
      exact hv'
    exact hfit _ _ hv''
  · have hmem : tail[p.2]'hp2 ∈ (fullDomains f).getD (f.2.length + p.2) [] :=
      hfits.2 _ _ hread
    rwa [fullDomains_getD_remaining, hgetD] at hmem

/-- The canonical trail's entries all hold at covered assignments. -/
theorem agrees_canonicalTrail {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i [] → v ∈ orig.getD i [])
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
    (hwm : w ∈ orig.getD s []) (hl : valueLiteral s w = some l) :
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

/-- **F3 (prefix forcing)** for the canonical trail: the pins force the
frame's chosen prefix at every fitting assignment. -/
theorem prefix_forced_canonical {orig : List Domain} {f : BranchFrame}
    (hshape : ShapeTypedDomains orig)
    (hpins : ∀ (s : Nat) (hs : s < f.2.length),
      ∃ l, valueLiteral s (f.2[s]'hs) = some l)
    (hfit : ∀ i v, v ∈ (fullDomains f).getD i [] → v ∈ orig.getD i []) :
    PrefixForced (canonicalTrail orig f) orig f.2 := by
  intro a hsat hfits i hi
  obtain ⟨l, hl⟩ := hpins i hi
  have hmem : { literal := l.norm, level := i + 1, reason := none } ∈
      canonicalPins f.2 :=
    mem_canonicalPins.mpr ⟨(f.2[i], i), mem_zipIdx_iff'.mpr ⟨hi, rfl⟩, l, hl, rfl⟩
  have hev : (l.norm).eval a = some true :=
    hsat _ (List.mem_append.mpr (Or.inl hmem))
  have hwm : f.2[i] ∈ orig.getD i [] := by
    apply hfit
    rw [List.getD_eq_getElem?_getD, fullDomains_prefix f i hi]
    simp
  have := pin_forces_of_fits hshape hwm hl a hfits hev
  simpa [List.getElem?_eq_getElem hi] using this

/-- Every pin references a prefix slot. -/
theorem canonicalPins_slot {pre : List Value} {e : TrailEntry}
    (he : e ∈ canonicalPins pre) : e.literal.atom.slot < pre.length := by
  obtain ⟨p, hp, l, hl, rfl⟩ := mem_canonicalPins.mp he
  obtain ⟨hlt, -⟩ := mem_zipIdx_iff'.mp hp
  rw [literal_norm_atom_slot, valueLiteral_atom_slot hl]
  exact hlt

/-- Every falsifier entry references a remaining slot at or above the
resumed level. -/
theorem canonicalFalsifiers_slot {orig : List Domain} {f : BranchFrame}
    {e : TrailEntry} (he : e ∈ canonicalFalsifiers orig f) :
    ∃ p ∈ f.1.zipIdx, e.literal.atom.slot = f.2.length + p.2 := by
  obtain ⟨p, hp, q, hq, l, hv, hk, htk, rfl⟩ := mem_canonicalFalsifiers.mp he
  exact ⟨p, hp, by
    rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hv]⟩

/-- Every entry of a slot's falsifier list references that slot. -/
theorem slotFalsifiers_slot {orig : List Domain} {f : BranchFrame} {i : Nat}
    {dom : Domain} {e : TrailEntry} (he : e ∈ slotFalsifiers orig f i dom) :
    e.literal.atom.slot = f.2.length + i := by
  obtain ⟨q, hq, l, hv, hk, htk, rfl⟩ := mem_slotFalsifiers.mp he
  rw [literal_negate_norm_atom_slot, valueLiteral_atom_slot hv]

/-- The pins are duplicate-free (strictly increasing levels). -/
theorem canonicalPins_nodup (pre : List Value) : (canonicalPins pre).Nodup := by
  rw [List.Nodup, canonicalPins, List.pairwise_filterMap]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij a ha b hb
  simp only [List.getElem_zipIdx, Nat.zero_add] at ha hb
  intro heq
  rw [canonicalPinEntry, Option.map_eq_some_iff] at ha hb
  obtain ⟨l, hl, hal⟩ := ha
  obtain ⟨l', hl', hbl⟩ := hb
  subst hal
  subst hbl
  have hlev := congrArg TrailEntry.level heq
  simp only at hlev
  omega

/-- A slot's falsifier list is ALWAYS duplicate-free: entries are emitted
at their first-occurring position only, and distinct occurrences of the
same literal come from the same value (`valueLiteral_negate_norm_inj`) —
whose earlier occurrence is already in the take image. -/
theorem slotFalsifiers_nodup {orig : List Domain} {f : BranchFrame} {i : Nat}
    {dom : Domain} : (slotFalsifiers orig f i dom).Nodup := by
  simp only [slotFalsifiers]
  rw [List.Nodup, List.pairwise_filterMap]
  rw [List.pairwise_iff_getElem]
  intro i' j' hi' hj' hij e he e' he'
  simp only [List.getElem_zipIdx, Nat.zero_add] at he he'
  intro heq
  have hi'len : i' < (orig.getD (f.2.length + i) []).length := by
    simpa [List.length_zipIdx] using hi'
  have hj'len : j' < (orig.getD (f.2.length + i) []).length := by
    simpa [List.length_zipIdx] using hj'
  cases hv : valueLiteral (f.2.length + i)
      ((orig.getD (f.2.length + i) [])[i']'hi'len) with
  | none =>
      simp only [hv] at he
      cases he
  | some le =>
      simp only [hv] at he
      by_cases hk : le ∈ dom.filterMap (valueLiteral (f.2.length + i))
      · rw [if_pos hk] at he
        cases he
      · rw [if_neg hk] at he
        by_cases htk : le ∈ ((orig.getD (f.2.length + i) []).take i').filterMap
            (valueLiteral (f.2.length + i))
        · rw [if_pos htk] at he
          cases he
        · rw [if_neg htk] at he
          rw [canonicalRetire, hv, Option.map_some] at he
          have he_e : e = { literal := le.negate.norm, level := f.2.length, reason := none } :=
            (Option.some.inj he).symm
          cases hv' : valueLiteral (f.2.length + i)
              ((orig.getD (f.2.length + i) [])[j']'hj'len) with
          | none =>
              simp only [hv'] at he'
              cases he'
          | some le' =>
              simp only [hv'] at he'
              by_cases hk' : le' ∈ dom.filterMap (valueLiteral (f.2.length + i))
              · rw [if_pos hk'] at he'
                cases he'
              · rw [if_neg hk'] at he'
                by_cases htk' : le' ∈ ((orig.getD (f.2.length + i) []).take
                    j').filterMap (valueLiteral (f.2.length + i))
                · rw [if_pos htk'] at he'
                  cases he'
                · rw [if_neg htk'] at he'
                  rw [canonicalRetire, hv', Option.map_some] at he'
                  have he'_e : e' = { literal := le'.negate.norm, level := f.2.length, reason := none } :=
                    (Option.some.inj he').symm
                  rw [he_e, he'_e] at heq
                  have hlit : le.negate.norm = le'.negate.norm :=
                    congrArg TrailEntry.literal heq
                  have hds : (orig.getD (f.2.length + i) [])[i']'hi'len =
                      (orig.getD (f.2.length + i) [])[j']'hj'len :=
                    valueLiteral_negate_norm_inj hv hv' hlit
                  apply htk'
                  apply List.mem_filterMap.mpr
                  refine ⟨(orig.getD (f.2.length + i) [])[i']'hi'len, ?_, ?_⟩
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
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact slotFalsifiers_nodup
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    intro x hx y hy
    simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at hx hy
    intro heq
    have hxslot := slotFalsifiers_slot hx
    have hyslot := slotFalsifiers_slot hy
    rw [heq] at hxslot
    omega

/-- **F8 (norm-uniqueness)**: equal normalized literals force equal
entries — pins by their slots, falsifiers by retirement injectivity, and
the two groups never share a slot. -/
theorem canonicalTrail_norm_unique {orig : List Domain} {f : BranchFrame}
    {e e' : TrailEntry} (he : e ∈ canonicalTrail orig f)
    (he' : e' ∈ canonicalTrail orig f)
    (hl : e'.literal = e.literal.norm) : e' = e := by
  have hlit0 : e'.literal = e.literal := by
    rw [← canonicalTrail_literal_norm he] at hl
    exact hl
  rcases List.mem_append.mp he with he | he <;>
    rcases List.mem_append.mp he' with he' | he'
  · -- pin / pin
    obtain ⟨p, hp, l, hl1, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨p', hp', l', hl2, rfl⟩ := mem_canonicalPins.mp he'
    have hlit : l'.norm = l.norm := hlit0
    have hslot : p'.2 = p.2 := by
      have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
      rwa [literal_norm_atom_slot, literal_norm_atom_slot,
        valueLiteral_atom_slot hl2, valueLiteral_atom_slot hl1] at h1
    rw [hslot, hlit]
  · -- pin / falsifier: disjoint slots
    exfalso
    obtain ⟨p, hp, l, hl1, rfl⟩ := mem_canonicalPins.mp he
    obtain ⟨p', hp', q', hq', l', hl2, hk', htk', rfl⟩ :=
      mem_canonicalFalsifiers.mp he'
    have hlit : l'.negate.norm = l.norm := hlit0
    have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
    rw [literal_negate_norm_atom_slot, literal_norm_atom_slot,
      valueLiteral_atom_slot hl1, valueLiteral_atom_slot hl2] at h1
    obtain ⟨hlt, -⟩ := mem_zipIdx_iff'.mp hp
    omega
  · -- falsifier / pin: disjoint slots
    exfalso
    obtain ⟨p, hp, q, hq, l, hl1, hk, htk, rfl⟩ :=
      mem_canonicalFalsifiers.mp he
    obtain ⟨p', hp', l', hl2, rfl⟩ := mem_canonicalPins.mp he'
    have hlit : l'.norm = l.negate.norm := hlit0
    have h1 := congrArg (fun x : Literal => x.atom.slot) hlit
    rw [literal_negate_norm_atom_slot, literal_norm_atom_slot,
      valueLiteral_atom_slot hl1, valueLiteral_atom_slot hl2] at h1
    obtain ⟨hlt, -⟩ := mem_zipIdx_iff'.mp hp'
    omega
  · -- falsifier / falsifier
    obtain ⟨p, hp, q, hq, l, hl1, hk, htk, rfl⟩ :=
      mem_canonicalFalsifiers.mp he
    obtain ⟨p', hp', q', hq', l', hl2, hk', htk', rfl⟩ :=
      mem_canonicalFalsifiers.mp he'
    have hlit : l'.negate.norm = l.negate.norm := hlit0
    rw [hlit]

/-- **F8 (distinctness)** for the canonical trail. -/
theorem canonicalTrail_distinct {orig : List Domain} {f : BranchFrame} :
    TrailLiteralsDistinct (canonicalTrail orig f) := by
  refine ⟨fun e he e' he' hl => canonicalTrail_norm_unique he he' hl, ?_⟩
  rw [canonicalTrail, List.nodup_append]
  refine ⟨canonicalPins_nodup f.2, canonicalFalsifiers_nodup, ?_⟩
  intro a ha b hb
  intro heq
  have has := canonicalPins_slot ha
  obtain ⟨p, hp, hbs⟩ := canonicalFalsifiers_slot hb
  rw [heq] at has
  rw [hbs] at has
  omega

/-- **R1 CORE: THE CANONICAL RESUME IS REACHABLE.** Every missing-checkpoint
resume's successor state satisfies the full eight-field `ReachableState`
of the frame's own box — the pending frame is its own retained snapshot. -/
theorem resumePendingBase_reachable {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {f : BranchFrame}
    (h : ReachableState leaf orig bs) (hb : PendingBacked orig f) :
    ReachableState leaf orig (resumePendingBase orig bs f) where
  length_ok := hb.full_len
  full_fits := hb.fit
  prefix_forced := prefix_forced_canonical hb.shape hb.pins hb.fit
  agrees := agrees_canonicalTrail hb.shape hb.fit hb.full_len
  narrowing_complete := narrowing_complete_canonical hb.shape hb.full_len
  wf := canonicalTrail_wellFormed h.wf.2.2.2.2
  sorted := canonicalTrail_sorted orig f
  distinct := canonicalTrail_distinct

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
    (hcp : checkpointAt cfg.checkpoints f.2.length = none)
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

/-- The prefix-pin discipline of a chosen prefix: every chosen position
carries a decision literal. This is exactly `PendingBacked.pins`, factored
out so the producers and the arm-preservation lemmas can name it. -/
def PrefixPinned (pre : Assignment) : Prop :=
  ∀ (s : Nat) (hs : s < pre.length),
    ∃ l : Literal, valueLiteral s (pre[s]'hs) = some l

/-- The `pins` field IS the prefix discipline (definitional). -/
theorem PendingBacked.prefixPinned {orig : List Domain} {f : BranchFrame}
    (hb : PendingBacked orig f) : PrefixPinned f.2 :=
  hb.pins

theorem prefixPinned_nil : PrefixPinned ([] : Assignment) := by
  intro s hs
  exact absurd hs (by simp)

/-- THE DECISION EXTENSION of the prefix discipline: appending the split's
pinned value at the next position keeps every chosen position pinned (the
new position is pinned by the split data's own literal). -/
theorem prefixPinned_append {pre : Assignment} {v : Value} {l : Literal}
    (hpre : PrefixPinned pre) (hl : valueLiteral pre.length v = some l) :
    PrefixPinned (pre ++ [v]) := by
  intro s hs
  rw [List.length_append, List.length_singleton] at hs
  by_cases hlt : s < pre.length
  · obtain ⟨l', hl'⟩ := hpre s hlt
    refine ⟨l', ?_⟩
    rw [List.getElem_append_left hlt]
    exact hl'
  · have hsp : s = pre.length := by omega
    subst hsp
    refine ⟨l, ?_⟩
    rw [List.getElem_append_right (Nat.le_refl pre.length)]
    simpa using hl

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

/-- Splitting the head remaining domain: the sibling's remaining domains
sit inside the parent's (the dropped head value `v` is prepended). -/
theorem getD_split_sibling_tail {v : Value} {vs : Domain} {doms : List Domain} :
    ∀ i w, w ∈ (vs :: doms).getD i [] → w ∈ ((v :: vs) :: doms).getD i [] := by
  intro i w hw
  cases i with
  | zero => exact List.mem_cons_of_mem v (by simpa using hw)
  | succ j => simpa using hw

/-- The sibling frame's full box is a pointwise subset of the parent's. -/
theorem fullDomains_sibling_subset {v : Value} {vs : Domain} {doms : List Domain}
    {pre : Assignment} :
    ∀ i w, w ∈ (fullDomains (vs :: doms, pre)).getD i [] →
      w ∈ (fullDomains ((v :: vs) :: doms, pre)).getD i [] := by
  intro i w hw
  show w ∈ ((pre.map fun x => [x]) ++ ((v :: vs) :: doms)).getD i []
  exact getD_append_subset getD_split_sibling_tail i w
    (show w ∈ ((pre.map fun x => [x]) ++ (vs :: doms)).getD i [] from hw)

/-- **R2a PRODUCER — THE PUSHED SIBLING.** The pending alternative pushed
by the decide arm of a reachable split is backed: `full_len` and `fit`
from the parent's box facts (the sibling's remaining domains are the
parent's, with the pinned head dropped), `pins` from the parent's prefix
discipline, `shape` from the run box. No density, depth or domain-Nodup
hypothesis. -/
theorem pendingBacked_split_sibling {orig : List Domain} {pre : Assignment}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hfull : (fullDomains (((v :: vs) :: doms), pre)).length = orig.length)
    (hfit : ∀ i w, w ∈ (fullDomains (((v :: vs) :: doms), pre)).getD i [] →
      w ∈ orig.getD i [])
    (hpins : PrefixPinned pre)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (vs :: doms, pre) := by
  refine ⟨?_, hpins, ?_, hshape⟩
  · show (fullDomains (vs :: doms, pre)).length = orig.length
    have hfull' : pre.length + (((v :: vs) :: doms).length) = orig.length := by
      have := hfull
      rw [fullDomains_length] at this
      exact this
    rw [fullDomains_length]
    simp only [List.length_cons] at hfull' ⊢
    omega
  · intro i w hw
    exact hfit i w (fullDomains_sibling_subset i w hw)

/-- **R2a PRODUCER — THE PINNED CHILD.** The child frame of a reachable
split is backed: its full box is inside the parent's (extension of the
prefix by the pinned value plus the same tail), its prefix discipline is
the parent's extended by the split data's own pin, and the run box types
it. -/
theorem pendingBacked_split_child {orig : List Domain} {pre : Assignment}
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hwl : valueLiteral pre.length v = some l)
    (hfull : (fullDomains (((v :: vs) :: doms), pre)).length = orig.length)
    (hfit : ∀ i w, w ∈ (fullDomains (((v :: vs) :: doms), pre)).getD i [] →
      w ∈ orig.getD i [])
    (hpins : PrefixPinned pre)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (doms, pre ++ [v]) := by
  refine ⟨?_, ?_, ?_, hshape⟩
  · show (fullDomains (doms, pre ++ [v])).length = orig.length
    have hfull' : pre.length + (((v :: vs) :: doms).length) = orig.length := by
      have := hfull
      rw [fullDomains_length] at this
      exact this
    rw [fullDomains_length, List.length_append, List.length_singleton]
    simp only [List.length_cons] at hfull' ⊢
    omega
  · exact prefixPinned_append hpins hwl
  · intro i w hw
    exact hfit i w (fullDomains_decide_subset (d := v :: vs) (rest := doms)
      (pre := pre) (List.mem_cons_self ..) i w hw)

/-- **R2a CONFIG-LEVEL PRODUCER — DECIDE PUSH.** The frame the decide arm
actually pushes (`(vs :: doms, cfg.branch.frame.2)`, the sibling of the
split) is backed, from the parent configuration's reachability, the
parent's prefix discipline and the run box's typing. -/
theorem pendingBacked_decide_push {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame.2)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (vs :: doms, cfg.branch.frame.2) := by
  have hfe : cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2) :=
    Prod.ext (splitData_eq_some_iff.mp hsplit).1 rfl
  have hfull := hreach.length_ok
  rw [hfe] at hfull
  refine pendingBacked_split_sibling (pre := cfg.branch.frame.2) hfull ?_ hpins
    hshape
  intro i w hw
  exact hreach.full_fits i w (by rw [hfe]; exact hw)

/-- **R2a CONFIG-LEVEL PRODUCER — THE PINNED CHILD** (the decide/skip arm's
new current frame). -/
theorem pendingBacked_decide_child {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame.2)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (doms, cfg.branch.frame.2 ++ [v]) := by
  have hparts := splitData_eq_some_iff.mp hsplit
  have hfe : cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2) :=
    Prod.ext hparts.1 rfl
  have hfull := hreach.length_ok
  rw [hfe] at hfull
  refine pendingBacked_split_child hparts.2 hfull ?_ hpins hshape
  intro i w hw
  exact hreach.full_fits i w (by rw [hfe]; exact hw)

/-! ### §5.3 Retained-frame preservation across the arms -/

theorem stepPropagate_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf}
    (d : ProductiveDeduction leaf cfg.branch)
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepPropagate cfg d).pending := by
  simpa only [stepPropagate_pending] using h

theorem stepDecideSkip_pendingBackedList {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {v : Value}
    {doms : List Domain} (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepDecideSkip cfg v doms).pending := by
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
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame.2)
    (hshape : ShapeTypedDomains orig)
    (h : PendingBackedList orig cfg.pending) :
    PendingBackedList orig (stepDecide cfg v vs doms l).pending := by
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
    (hcp : checkpointAt cfg.checkpoints f.2.length = none)
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

/-- Propagation narrows the frame by `filterFrame`, which keeps the
prefix. -/
theorem stepPropagate_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (d : ProductiveDeduction leaf cfg.branch)
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepPropagate cfg d).branch.frame.2 := by
  rw [stepPropagate_branch_frame, filterFrame_prefix d.filtered]
  exact h

/-- The split's pinned child extends the prefix by the split data's own
pin. -/
theorem stepDecide_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepDecide cfg v vs doms l).branch.frame.2 := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  show PrefixPinned (cfg.branch.frame.2 ++ [v])
  exact prefixPinned_append h hwl

/-- The redundant-pin skip's child extends the prefix by the split data's
own pin (the recorded pin is the same literal). -/
theorem stepDecideSkip_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepDecideSkip cfg v doms).branch.frame.2 := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  show PrefixPinned (cfg.branch.frame.2 ++ [v])
  exact prefixPinned_append h hwl

/-- The explained closure only ever narrows the frame by `filterFrame`
(each step's frame comes from the deduction's own `filtered` call), so it
never changes the chosen prefix. -/
theorem explainedClosure_prefix (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    (explainedClosure orig original props bs).frame.2 = bs.frame.2 := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      (explainedClosure orig original props bs).frame.2 = bs.frame.2 from
    h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle
      rw [explainedClosure]
      split
      · rfl
      · rename_i d _
        exfalso
        have := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle
      rw [explainedClosure]
      split
      · rfl
      · rename_i d _
        have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
          simp only [stepNarrowSync_frame]
          have := d.decreases
          omega
        rw [ih (stepNarrowSync orig bs d) hmass]
        simp only [stepNarrowSync_frame]
        exact filterFrame_prefix d.filtered

/-- The restored-and-narrowed state of a plan keeps the checkpoint frame's
prefix (`filterFrame` preserves it). -/
theorem restoreNarrow_prefix {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (h : p.restoreNarrow bs = some s) :
    PrefixPinned p.checkpoint.frame.2 → PrefixPinned s.frame.2 := by
  intro hp
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · next g hg =>
      cases h
      show PrefixPinned g.2
      rw [filterFrame_prefix hg]
      exact hp

/-- The complete learn/backjump/assert transition keeps the prefix of the
SELECTED checkpoint's frame (restoration keeps it, the assertion filter
keeps it, the resumed closure keeps it). The residual is exactly "the
selected checkpoint frame's prefix is pinned", which the run invariant
`PendingSideInv.checkpoints` maintains. -/
theorem perform_prefix {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    PrefixPinned p.checkpoint.frame.2 → PrefixPinned s.frame.2 := by
  intro hp
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none => rw [hr] at h; cases h
  | some t =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      show PrefixPinned (explainedClosure orig original props (syncAll orig t)).frame.2
      rw [explainedClosure_prefix, syncAll_frame]
      exact restoreNarrow_prefix hr hp

theorem stepLearnBackjumpAssert_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf}
    (hperf : p.perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hpcp : PrefixPinned p.checkpoint.frame.2) :
    PrefixPinned (stepLearnBackjumpAssert cfg p ev restored).branch.frame.2 := by
  show PrefixPinned restored.frame.2
  exact perform_prefix hperf hpcp

/-- Consume restores the pending head, whose discipline comes from its own
backing (never from the failed branch). -/
theorem stepConsume_prefixPinned {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (h : stepConsume cfg = some next)
    (hpend : PendingBackedList orig cfg.pending) :
    PrefixPinned next.branch.frame.2 := by
  obtain ⟨hframe, -, -, -, -⟩ := stepConsume_some_shape hp h
  rw [hframe]
  exact (hpend f (by rw [hp]; exact List.mem_cons_self ..)).prefixPinned

theorem stepAnalyzeConflict_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepAnalyzeConflict cfg c learned).branch.frame.2 := by
  show PrefixPinned cfg.branch.frame.2
  exact h

theorem stepAnalyzeConflictCounted_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause} {n : Nat}
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepAnalyzeConflictCounted cfg c learned n).branch.frame.2 := by
  show PrefixPinned cfg.branch.frame.2
  exact h

theorem stepLocalExclude_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepLocalExclude cfg learned r).branch.frame.2 := by
  show PrefixPinned cfg.branch.frame.2
  exact h

theorem stepChronologicalFallback_prefixPinned {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {r : DeadRegion}
    (h : PrefixPinned cfg.branch.frame.2) :
    PrefixPinned (stepChronologicalFallback cfg r).branch.frame.2 := by
  show PrefixPinned cfg.branch.frame.2
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
  branch : PrefixPinned cfg.branch.frame.2
  /-- every pending alternative is backed -/
  pending : PendingBackedList orig cfg.pending
  /-- every saved checkpoint's frame prefix is pinned -/
  checkpoints : ∀ cp ∈ cfg.checkpoints, PrefixPinned cp.frame.2

theorem PendingSideInv.init (orig : List Domain) (original : List Clause)
    (props : List Propagator) :
    PendingSideInv orig (SchedulerConfig.init (leaf := leaf) orig original props) where
  branch := prefixPinned_nil
  pending := pendingBackedList_nil orig
  checkpoints := by
    intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact prefixPinned_nil

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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (h : PendingSideInv orig cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    PendingSideInv orig (stepDecide cfg v vs doms l) where
  branch := stepDecide_prefixPinned hsplit h.branch
  pending := stepDecide_pendingBackedList hsplit hreach h.branch hshape h.pending
  checkpoints := by
    intro cp hcp
    have hck : (LeanFzn.Solver.UIP.stepDecide cfg v vs doms l).checkpoints
        = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
    rw [hck] at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · show PrefixPinned cfg.branch.frame.2
      exact h.branch
    · exact h.checkpoints cp hcp

theorem PendingSideInv.stepDecideSkip {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (h : PendingSideInv orig cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    PendingSideInv orig (stepDecideSkip cfg v doms) where
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
    (hpcp : PrefixPinned p.checkpoint.frame.2) :
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
      (BackjumpPlan.ofCheckpoint cp cfg.branch asserting learned).checkpoint.frame.2 :=
    h.checkpoints cp hcp
  exact h.stepLearnBackjumpAssert hperf hpcp

/-- A lookup's checkpoint frame prefix is pinned (the consumer shape of the
jump arm's premise, wired by `checkpointAt_mem`). -/
theorem PendingSideInv.prefixPinned_of_checkpointAt {orig : List Domain}
    {cfg : SchedulerConfig leaf} {target : Nat} {cp : DecisionCheckpoint leaf}
    (h : PendingSideInv orig cfg) (hat : checkpointAt cfg.checkpoints target = some cp) :
    PrefixPinned cp.frame.2 :=
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
