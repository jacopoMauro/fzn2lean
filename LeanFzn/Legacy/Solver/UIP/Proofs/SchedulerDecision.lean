/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerDecision.lean

Purpose:
  THE TYPED DECISION SITE. Two replacements for the C2a premises of
  `stepDecide_reachable` / `arm_decide_invariant`:

  * `hpin` — REPLACED by `DecidePinTyped`: the pin iff is claimed only at
    assignments the parent state REPRESENTS (frame-covered), where the
    head-domain typing makes the literal exact. The GLOBAL iff is FALSE
    (`pin_int_global_false`, D1a: `.bool false`/`.bool true` share
    `intView` 0/1). Site discharges: `decidePinTyped_bool` (global for
    Bool, from `valueLiteral_holds_iff`) and `decidePinTyped_int`
    (frame-restricted, from `pin_int_of_frameHead`). The int route's
    residual `∀ a, a[slot]? = some w → ∃ k, w = .int k` is NOT a theorem
    of the frozen definitions (`int_slot_not_typed_witness`), so
    `stepDecide_int_invariant_of_slotTyped` is a named conditional, not
    an activation ingredient: an int decision at a fresh level records
    `negNe s i`, which `.bool false` satisfies — the residual is exactly
    what the runtime would have to close with a typing-aware pin.
  * `hred` — the `TrailRedundant = false` runtime guard. The files here
    prove why it is necessary (`stepDecide_redundant_not_distinct`, C2a)
    and what the skip alternative buys when the guard FAILS:
    `stepDecide_redundant_forces_pin` (every represented assignment
    already carries the pinned value) and
    `stepDecide_redundant_no_alternative` (every parent-covered
    assignment is already covered by the pinned child), so a redundant
    decision can be SKIPPED without losing an alternative — the sibling
    carries no represented leaf. `stepDecide_singleton_sibling_empty`
    covers the forced/singleton case through L1's empty-frame routing.

  INVARIANT CLOSURE:
  * `CheckpointsBelow` for the decision: `checkpointsBelow_decide`
    (SchedulerForward) — re-exported as
    `stepDecide_checkpointsBelow`.
  * explanation provenance: `stepDecide_learnedProvenance` — `decide`
    touches neither the learned database nor the reasons, and the
    `RecordedWith` falsifier set is trail-monotone
    (`recordedWith_mono_trail`, L1), so L1's `LearnedProvenance`
    transfers UNCONDITIONALLY. `stepDecide_bool_reachableLearnedProvenance`
    consumes L1's `ReachableLearnedProvenance` interface for the Bool
    successor.
  * `stepDecide_bool_invariant` — the FULL `SchedulerInvariant` for the
    Bool decision, unconditional given `hred` (no `hpin` premise, via
    `stepDecide_bool_reachable`).

  CONCRETE CHECKS: int 0/1 vs bool false/true separation at an int-typed
  frame, singleton split data, empty-domain boundary, singleton frame.

Dependencies (all below in the DAG; no runtime module imports this):
  - LeanFzn.Solver.UIP.Proofs.SchedulerForward: `stepDecide_*` field lemmas,
    `checkpointsBelow_decide`, `splitData_eq_some_iff` re-use.
  - LeanFzn.Solver.UIP.Proofs.CompiledScheduler (D1a): `IntTypedDomain`,
    `pin_int_of_frameHead`, `pin_int_iff_of_intSlot`, `pin_int_global_false`,
    `frameCovers_head_mem`.
  - LeanFzn.Solver.UIP.Proofs.LearnedExplanation (L1): `LearnedProvenance`,
    `ReachableLearnedProvenance`, `recordedWith_mono_trail`,
    `not_frameCovers_of_empty_domain`.

Registration line owed by the coordinator (umbrella `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`):
  import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerForward
import LeanFzn.Legacy.Solver.UIP.Proofs.CompiledScheduler
import LeanFzn.Legacy.Solver.UIP.Proofs.LearnedExplanation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The typed decision pin (replacement interface for `hpin`) -/

/-- **S1 REPLACEMENT INTERFACE for the decision pin.** The pin iff is
claimed ONLY at assignments the parent configuration represents
(frame-covered): there the head domain's typing makes the literal exact
(`decidePinTyped_bool` / `decidePinTyped_int`). The historical global
`∀ a` iff is FALSE for ints — `.bool false`/`.bool true` share the
integer view 0/1 (`pin_int_global_false`, D1a) — so no consumer may take
it; consumers take this predicate plus a site discharge. -/
def DecidePinTyped {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (k : Nat) (l : Literal) (v : Value) : Prop :=
  ∀ a, FrameCovers cfg.branch.frame a →
    (l.norm.eval a = some true ↔ a[k]? = some v)

/-- The Bool site discharge: `valueLiteral`'s Boolean pin is exact
GLOBALLY, hence in particular at every frame-covered assignment. -/
theorem decidePinTyped_bool {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {b : Bool}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .bool b, vs)) :
    DecidePinTyped cfg k l (.bool b) := by
  intro a _
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  rw [Literal.norm_eval]
  simpa using valueLiteral_holds_iff hwl a

/-- The Int site discharge, frame-restricted (D1a's `pin_int_of_frameHead`):
at an int-typed head domain the integer pin is exact at every
frame-covered assignment. -/
theorem decidePinTyped_int {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {i : Int}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .int i, vs))
    (htyp : ∀ w ∈ vs, ∃ j : Int, w = .int j) :
    DecidePinTyped cfg k l (.int i) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have hl : l = negNe k i := by
    have h := hwl
    rw [valueLiteral_int] at h
    exact (Option.some.inj h).symm
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hklt : k < cfg.branch.frame.doms.length :=
    (List.getElem?_eq_some_iff.mp hd).1
  intro a hcov
  rw [hl]
  refine pin_int_of_slot (f := cfg.branch.frame) (k := k) (i := i)
    hklt ?_ a hcov
  intro w hw
  have hwE : w ∈ Dom.enum (cfg.branch.frame.doms.getD k Dom.empty) :=
    (DomainLike.mem_iff _ _).mp hw
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some, hde] at hwE
  rcases List.mem_cons.mp hwE with rfl | hwE
  · exact ⟨i, rfl⟩
  · exact htyp w ((DomainLike.mem_iff _ _).mpr
      (by simpa [domElems_eq_enum] using hwE))

/-- **THE INT RESIDUAL, NAMED.** `reachable_decide` consumes the GLOBAL
pin; bridging `DecidePinTyped` to it needs the slot to be int-typed at
EVERY assignment (that is all `pin_int_iff_of_intSlot` needs). This
predicate is exactly that residual. It is NOT an invariant of the frozen
tree: `pin_int_global_false` refutes it at `a = [.bool false]`, and the
root trail is empty, so an int decision is currently unreachable —
which is why no activation may consume an int decision until the runtime
pin or the reachable invariant is made typing-aware (integration). -/
def SlotIntTyped {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (k : Nat) : Prop :=
  ∀ (a : Assignment), ∀ w, a[k]? = some w → ∃ j : Int, w = Value.int j

/-- The bridge from the global typing residual to the global pin the
frozen `reachable_decide` wants (`pin_int_iff_of_intSlot`). PROVED,
conditional on `SlotIntTyped` (see its doc: refuted in general). -/
theorem decidePin_global_of_slotIntTyped {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {i : Int} (h : SlotIntTyped cfg k) :
    ∀ a, (negNe k i).norm.eval a = some true ↔
      a[k]? = some (Value.int i) :=
  fun a => pin_int_iff_of_intSlot (s := k) (i := i) (a := a) (h a)

/-- **S1 FINDING (kernel-checked witness).** The global typing residual
fails at the concrete collision value, so the int decision's global pin
premise is uninstantiable on the frozen definitions. The typed interface
`DecidePinTyped` is the only true form. -/
theorem int_slot_not_typed_witness :
    ¬ (∃ k : Int, (Value.bool false) = Value.int k) := by
  rintro ⟨k, h⟩
  cases h

/-- At an int-typed head frame, NO represented assignment takes a Boolean
value at the split slot: this is the separation that makes the typed pin
non-vacuous and excludes the `pin_int_global_false` collision from the
int route. -/
theorem frameCovers_intSlot_not_bool {f : BranchFrame} {k : Nat}
    (hd : f.doms[k]? = some (f.doms.getD k Dom.empty))
    (htyp : IntTypedDomain (f.doms.getD k Dom.empty))
    {a : Assignment} (hcov : FrameCovers f a) :
    ∀ b : Bool, a[k]? ≠ some (.bool b) := by
  obtain ⟨v0, hv0, hget⟩ := frameCovers_slot_mem hd hcov
  obtain ⟨j, hj⟩ := htyp v0 hv0
  rw [hj] at hget
  intro b hb
  rw [hget] at hb
  cases Option.some.inj hb

/-! ## §1b The Fits-restricted pin producers (PLAN B2a)

The GLOBAL pin iff is kernel-refuted for int pins with constant `0`/`1`
(`pin_int_global_false`: `.bool false` shares the integer view `0`), and
`prefix_forced` is correspondingly restricted to the typed/represented
assignments `a.Fits orig`. The producers below discharge that
Fits-restricted form for the supported fragment, whose run boxes are
shape-typed (every domain is int-shaped or bool-shaped — the compiled
declaration forms; exotic domains never produce `splitData` pins). -/

/-- SHAPE DISCIPLINE of the run's original box: every domain is int-shaped
or bool-shaped (the supported fragment's declaration forms). -/
def ShapeTypedDomains (orig : List Domain) : Prop :=
  ∀ d ∈ orig, (∀ v ∈ d, ∃ k : Int, v = Value.int k) ∨
    (∀ v ∈ d, ∃ b : Bool, v = Value.bool b)

/-- A reachable domain that carries an int value is int-shaped: the shape
discipline excludes the bool-shaped alternative. -/
theorem intShaped_of_mem_int {orig : List Domain} {s : Nat} {i : Int}
    (hshape : ShapeTypedDomains orig) (h : Value.int i ∈ orig.getD s Dom.empty) :
    ∀ w ∈ orig.getD s Dom.empty, ∃ k : Int, w = Value.int k := by
  have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s) (a := (Dom.empty : Domain))
  cases hgt : orig[s]? with
  | none =>
      rw [hlook, hgt] at h
      simp only [Option.getD_none] at h
      simp at h
  | some d =>
      have hd : d ∈ orig := List.mem_of_getElem? hgt
      have hh : Value.int i ∈ d := by
        rw [hlook, hgt] at h
        simpa using h
      intro w hw
      have hw' : w ∈ d := by
        rw [hlook, hgt] at hw
        simpa using hw
      rcases hshape _ hd with hint | hbool
      · exact hint w hw'
      · obtain ⟨b, hb⟩ := hbool (Value.int i) hh
        cases hb

/-- From a shape-typed original box: a slot-int value at slot `s` of a
fitting assignment is literally the `.int` value. -/
theorem getElem_of_slotInt_typed {a : Assignment} {orig : List Domain}
    {s : Nat} {k : Int} (hfit : a.Fits orig)
    (hint : ∀ w ∈ orig.getD s Dom.empty, ∃ j : Int, w = Value.int j)
    (hslot : slotInt a s = some k) :
    a[s]? = some (Value.int k) := by
  rw [slotInt] at hslot
  obtain ⟨w, hw, hiv⟩ := Option.bind_eq_some_iff.mp hslot
  obtain ⟨j, rfl⟩ := hint w (hfit.2 s w hw)
  have hjk : j = k := by simpa [Value.intView] using hiv
  rw [hjk] at hw
  exact hw

/-- The pinned head value sits in the run box's domain at the split slot. -/
theorem pinHead_mem_orig {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch) :
    v ∈ orig.getD k Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  refine hreach.full_fits k v ?_
  change v ∈ cfg.branch.frame.doms.getD k Dom.empty
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
  exact (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)

/-- The sibling domain of a split is inside the run box's domain at the
split slot. -/
theorem pinSibling_mem_orig {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : ReachableState leaf orig cfg.branch) :
    ∀ w ∈ vs, w ∈ orig.getD k Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  intro w hw
  refine hreach.full_fits k w ?_
  show w ∈ cfg.branch.frame.doms.getD k Dom.empty
  rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
  exact (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_of_mem _
      (by simpa [domElems_eq_enum] using (DomainLike.mem_iff _ _).mp hw))

/-- **THE INT FRESH-PIN PRODUCER (B2a)**: at a reachable split site of a
shape-typed run box, the int pin's typed/represented semantics holds — the
correct, non-refuted replacement of the global iff consumed by
`reachable_decide`. -/
theorem decidePinFits_int {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {i : Int}
    {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, Value.int i, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔
        a[k]? = some (Value.int i)) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have hl : l = negNe k i := by
    rw [valueLiteral_int] at hwl
    exact (Option.some.inj hwl).symm
  have hint := intShaped_of_mem_int hshape
    (pinHead_mem_orig hsplit hreach)
  intro a hfit
  rw [hl]
  constructor
  · intro hev
    obtain ⟨j, hj, hji⟩ := (eval_negNe_iff a _ i).mp hev
    have hget := getElem_of_slotInt_typed hfit hint hj
    rw [hji] at hget
    exact hget
  · intro hget
    show (negNe k i).eval a = some true
    exact (eval_negNe_iff a _ i).mpr
      ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩

/-- The frame-restricted int pin (`hpinSkip`'s gate) under the same shape
discipline: the sibling's literal typing follows from the run box. -/
theorem decidePinTyped_int_of_shape {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {i : Int} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .int i, vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    DecidePinTyped cfg k l (.int i) := by
  refine decidePinTyped_int hsplit ?_
  intro w hw
  exact intShaped_of_mem_int hshape (pinHead_mem_orig hsplit hreach) w
    (pinSibling_mem_orig hsplit hreach w hw)

/-! ## §2 Freshness, redundancy and the skip alternative -/

/-- **THE GUARD'S CONTENT.** When the absence check FAILS (the normalized
decision literal is already recorded), the typed pin shows that every
represented assignment ALREADY carries the pinned value at the split
slot: the decision adds no information, and the runtime may skip it. -/
theorem stepDecide_redundant_forces_pin {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {l : Literal} {v : Value}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hpin : DecidePinTyped cfg k l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers cfg.branch.frame a →
      a[k]? = some v := by
  obtain ⟨e, he, heq⟩ := trailRedundant_iff.mp hred
  intro a hcov
  have hlit := hreach.agrees e he a hcov
  rw [heq] at hlit
  exact (hpin a hcov).mp hlit

/-- **SKIP LOSES NO ALTERNATIVE (the represented half).** Under the
redundant guard and the typed pin, every parent-covered assignment is
already covered by the pinned child `(doms, pre ++ [v])`: the sibling
alternative carries no represented leaf, so replacing the parent by the
child (instead of deciding again) preserves the covered set. -/
theorem stepDecide_redundant_no_alternative {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {l : Literal} {v : Value}
    {vs : Domain}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : DecidePinTyped cfg k l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers cfg.branch.frame a →
      FrameCovers (cfg.branch.frame.pin k v) a := by
  have hforce := stepDecide_redundant_forces_pin hreach hpin hred
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hklt : k < cfg.branch.frame.doms.length :=
    (List.getElem?_eq_some_iff.mp hd).1
  intro a hcov
  have hslot := hforce a hcov
  have hv : v ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    rw [List.getD_eq_getElem?_getD, hd, Option.getD_some]
    exact (DomainLike.mem_iff _ _).mpr (by
      rw [domElems_eq_enum, hde]
      exact List.mem_cons_self ..)
  show a ∈ allAssigns (cfg.branch.frame.doms.set k (Dom.ofList [v]))
  exact mem_allAssigns_set_of_read hcov hklt hv hslot

/-! ## §3 Invariant closure beyond `hpin`/`hred`

NOTE (M5): the former `stepDecide_singleton_sibling_empty` (a singleton
split's empty-head sibling) is RETIRED: the S1 `selectSlot`-based
`splitData` only selects LIVE slots (`vs ≠ []`), so the singleton-split
shape no longer occurs through the dispatcher. -/

/-- `decide` keeps the checkpoint-level discipline
(`checkpointsBelow_decide` of the forward module). -/
theorem stepDecide_checkpointsBelow {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {v : Value} {vs : Domain}
    {l : Literal} (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecide cfg k v vs l) :=
  checkpointsBelow_decide h

/-- **EXPLANATION PROVENANCE, UNCONDITIONAL:** `decide` touches neither
the learned database nor the compiled reasons; the trail only GROWS, and
`RecordedWith`'s falsifier set is trail-monotone
(`recordedWith_mono_trail`, L1). So L1's `LearnedProvenance` transfers
from any predecessor. -/
theorem stepDecide_learnedProvenance {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {l : Literal} {v : Value}
    {vs : Domain} (hprov : LearnedProvenance leaf cfg.branch) :
    LearnedProvenance leaf (stepDecide cfg k v vs l).branch := by
  have hmono : ∀ e ∈ cfg.branch.trail,
      e ∈ (stepDecide cfg k v vs l).branch.trail := by
    intro e he
    simp only [stepDecide, BranchState.decide]
    exact List.mem_append.mpr (Or.inl he)
  intro c hc
  obtain ⟨p, hp⟩ := hprov c hc
  exact ⟨p, recordedWith_mono_trail hp hmono⟩

/-- **FULL CLOSURE FOR THE BOOL DECISION** (no `hpin` premise, the guard
only): `stepDecide_bool_reachable` replaces the int-impossible pin, and
every other field is a C2a lemma. -/
theorem stepDecide_bool_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {b : Bool}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .bool b, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg k (.bool b) vs l) :=
  ⟨stepDecide_bool_reachable hinv hsplit hred,
    stepDecide_checkpoints_identify hinv hlevel hsplit,
    stepDecide_pending_fits hinv hsplit,
    stepDecide_branch_fits hinv hsplit,
    hinv.log_sound,
    stepDecide_covers hinv hsplit,
    hinv.learned_entailed⟩

/-- **L1 CONSUMPTION:** the Bool successor's database provenance follows
from the branch-level `ReachableLearnedProvenance` interface (L1) — no
per-clause work at the call site. -/
theorem stepDecide_bool_reachableLearnedProvenance {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {b : Bool}
    {vs : Domain}
    (hrl : ReachableLearnedProvenance leaf (ReachableState leaf cfg.orig))
    (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .bool b, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    LearnedProvenance leaf (stepDecide cfg k (.bool b) vs l).branch :=
  hrl _ (stepDecide_bool_reachable hinv hsplit hred)

/-- **INT DECISION, THE NAMED RESIDUAL ROUTE.** The full invariant for an
int decision exists exactly when `SlotIntTyped` holds (then the global
pin is `decidePin_global_of_slotIntTyped`). CONDITIONAL: the residual is
refuted in general (`int_slot_not_typed_witness` / `pin_int_global_false`),
so this is a reusable component — NOT an activation ingredient. -/
theorem stepDecide_int_invariant_of_slotTyped {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {i : Int}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .int i, vs))
    (htyp : SlotIntTyped cfg k)
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg k (.int i) vs l) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have hl : l = negNe k i := by
    have h := hwl
    rw [valueLiteral_int] at h
    exact (Option.some.inj h).symm
  refine stepDecide_invariant hinv hlevel hsplit ?_ hred
  rw [hl]
  exact fun a _ => decidePin_global_of_slotIntTyped htyp a

/-! ## §4 Concrete checks (kernel-checked) -/

/-- Int 0/1 vs Bool false/true: the shared integer view, the collision
source. -/
example : (Value.intView (Value.bool false)) = some 0 := rfl
example : (Value.intView (Value.bool true)) = some 1 := rfl

/-- The collision instance at a singleton int-typed frame: `negNe 0 0`
evaluates TRUE at `[.bool false]` while the slot is not `.int 0`. -/
example : (negNe 0 0).norm.eval ([Value.bool false] : Assignment) = some true := by
  rw [Literal.norm_eval, eval_negNe_iff]
  exact ⟨0, by simp [slotInt, Value.intView], rfl⟩

/-- ... and that assignment is NOT covered by the int-typed frame, so the
typed interface excludes it. -/
example : ¬ FrameCovers (⟨[Dom.ofList [Value.int 0]], []⟩ : BranchFrame)
    [Value.bool false] := by
  rintro hcov
  obtain ⟨v, hv, a', _, heq⟩ := mem_allAssigns_cons_iff.mp hcov
  have hv' : v = Value.int 0 := by
    have hvE : v ∈ Dom.enum (Dom.ofList [Value.int 0]) :=
      (DomainLike.mem_iff _ _).mp hv
    rw [Dom.enum_ofList, List.mem_singleton] at hvE
    exact hvE
  subst hv'
  have hnil : a' = [] := (List.cons.inj heq).2.symm
  subst hnil
  exact absurd (List.cons.inj heq).1 (by intro h; cases h)

/-- An all-singleton box has no live slot, so `splitData` refuses it
(the S1 selector only splits non-singleton domains). -/
example : splitData (⟨[Dom.ofList [Value.int 0]], []⟩ : BranchFrame) = none := rfl

/-- Empty-domain boundary: `splitData` refuses an exhausted box. -/
example : splitData (⟨[Dom.empty], []⟩ : BranchFrame) = none := rfl

/-- Singleton frame: the one-slot singleton-domain frame covers exactly
its pinned value. -/
example : FrameCovers (⟨[Dom.ofList [Value.int 0]], []⟩ : BranchFrame)
    [Value.int 0] :=
  (mem_allAssigns_cons_iff.mpr
    ⟨Value.int 0, by simp, [],
      by simp [allAssigns], rfl⟩)

/-- ... and an empty-domain frame covers nothing. -/
example : ¬ FrameCovers (⟨[Dom.empty], []⟩ : BranchFrame) ([] : Assignment) := by
  intro h
  exact not_frameCovers_of_empty_domain
    (f := (⟨[Dom.empty], []⟩ : BranchFrame)) (a := ([] : Assignment))
    ⟨Dom.empty, List.mem_cons_self .., Dom.enum_empty⟩ h

end LeanFzn.Solver.UIP
