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
  import LeanFzn.Solver.UIP.Proofs.SchedulerDecision
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerForward
import LeanFzn.Solver.UIP.Proofs.CompiledScheduler
import LeanFzn.Solver.UIP.Proofs.LearnedExplanation
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
    (l : Literal) (v : Value) : Prop :=
  ∀ a, FrameCovers cfg.branch.frame a →
    (l.norm.eval a = some true ↔
      a[cfg.branch.frame.2.length]? = some v)

/-- The Bool site discharge: `valueLiteral`'s Boolean pin is exact
GLOBALLY, hence in particular at every frame-covered assignment. -/
theorem decidePinTyped_bool {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms)) :
    DecidePinTyped cfg l (.bool b) := by
  intro a _
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  rw [Literal.norm_eval]
  simpa using valueLiteral_holds_iff hwl a

/-- The Int site discharge, frame-restricted (D1a's `pin_int_of_frameHead`):
at an int-typed head domain the integer pin is exact at every
frame-covered assignment. -/
theorem decidePinTyped_int {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {i : Int} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, .int i, vs, doms))
    (htyp : ∀ w ∈ vs, ∃ k : Int, w = .int k) :
    DecidePinTyped cfg l (.int i) := by
  have hslots := (splitData_eq_some_iff.mp hsplit).1
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have hl : l = negNe cfg.branch.frame.2.length i := by
    have h := hwl
    rw [valueLiteral_int] at h
    exact (Option.some.inj h).symm
  intro a hcov
  rw [hl]
  have hcov' : FrameCovers (((Value.int i :: vs) :: doms),
      cfg.branch.frame.2) a := by
    rw [← hslots]
    exact hcov
  exact pin_int_of_frameHead (d := Value.int i :: vs) (rest := doms)
    (pre := cfg.branch.frame.2) (i := i)
    (fun w hw => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨i, rfl⟩
      · exact htyp w hw) a hcov'

/-- **THE INT RESIDUAL, NAMED.** `reachable_decide` consumes the GLOBAL
pin; bridging `DecidePinTyped` to it needs the slot to be int-typed at
EVERY assignment (that is all `pin_int_iff_of_intSlot` needs). This
predicate is exactly that residual. It is NOT an invariant of the frozen
tree: `pin_int_global_false` refutes it at `a = [.bool false]`, and the
root trail is empty, so an int decision is currently unreachable —
which is why no activation may consume an int decision until the runtime
pin or the reachable invariant is made typing-aware (integration). -/
def SlotIntTyped {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop :=
  ∀ (a : Assignment), ∀ w, a[cfg.branch.frame.2.length]? = some w → ∃ k : Int, w = Value.int k

/-- The bridge from the global typing residual to the global pin the
frozen `reachable_decide` wants (`pin_int_iff_of_intSlot`). PROVED,
conditional on `SlotIntTyped` (see its doc: refuted in general). -/
theorem decidePin_global_of_slotIntTyped {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {i : Int} (h : SlotIntTyped cfg) :
    ∀ a, (negNe cfg.branch.frame.2.length i).norm.eval a = some true ↔
      a[cfg.branch.frame.2.length]? = some (Value.int i) :=
  fun a => pin_int_iff_of_intSlot (s := cfg.branch.frame.2.length)
    (i := i) (a := a) (h a)

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
theorem frameCovers_intHead_slot_not_bool {d : Domain} {rest : List Domain}
    {pre : Assignment} {a : Assignment} (htyp : IntTypedDomain d)
    (hcov : FrameCovers ((d :: rest), pre) a) :
    ∀ b : Bool, a[pre.length]? ≠ some (.bool b) := by
  obtain ⟨v0, hv0, hget⟩ := frameCovers_head_mem hcov
  obtain ⟨k, hk⟩ := htyp v0 hv0
  rw [hk] at hget
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
    (hshape : ShapeTypedDomains orig) (h : Value.int i ∈ orig.getD s []) :
    ∀ w ∈ orig.getD s [], ∃ k : Int, w = Value.int k := by
  have hlook := List.getD_eq_getElem?_getD (l := orig) (i := s) (a := ([] : Domain))
  cases hgt : orig[s]? with
  | none =>
      rw [hlook, hgt] at h
      simp only [Option.getD_none, List.not_mem_nil] at h
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
    (hint : ∀ w ∈ orig.getD s [], ∃ j : Int, w = Value.int j)
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch) :
    v ∈ orig.getD (cfg.branch.frame.2.length) [] := by
  have hslots := (splitData_eq_some_iff.mp hsplit).1
  have hmem : v ∈ (fullDomains cfg.branch.frame).getD
      (cfg.branch.frame.2.length) [] := by
    rw [List.getD_eq_getElem?_getD]
    have hfr := fullDomains_remaining (f := cfg.branch.frame) (i := 0)
    rw [Nat.add_zero, hslots] at hfr
    rw [hfr]
    simp
  exact hreach.full_fits _ _ hmem

/-- The sibling domain of a split is inside the run box's domain at the
split slot. -/
theorem pinSibling_mem_orig {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch) :
    ∀ w ∈ vs, w ∈ orig.getD (cfg.branch.frame.2.length) [] := by
  have hslots := (splitData_eq_some_iff.mp hsplit).1
  have hfull : (fullDomains cfg.branch.frame).getD
      (cfg.branch.frame.2.length) [] = v :: vs := by
    rw [List.getD_eq_getElem?_getD]
    have hfr := fullDomains_remaining (f := cfg.branch.frame) (i := 0)
    rw [Nat.add_zero, hslots] at hfr
    rw [hfr]
    simp
  intro w hw
  exact hreach.full_fits _ _ (by rw [hfull]; exact List.mem_cons_of_mem _ hw)

/-- **THE INT FRESH-PIN PRODUCER (B2a)**: at a reachable split site of a
shape-typed run box, the int pin's typed/represented semantics holds — the
correct, non-refuted replacement of the global iff consumed by
`reachable_decide`. -/
theorem decidePinFits_int {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {i : Int} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, Value.int i, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔
        a[cfg.branch.frame.2.length]? = some (Value.int i)) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have hl : l = negNe cfg.branch.frame.2.length i := by
    rw [valueLiteral_int] at hwl
    exact (Option.some.inj hwl).symm
  have hint := intShaped_of_mem_int hshape
    (pinHead_mem_orig hsplit hreach)
  intro a hfit
  rw [hl]
  constructor
  · intro hev
    obtain ⟨k, hk, hki⟩ := (eval_negNe_iff a _ i).mp hev
    have hget := getElem_of_slotInt_typed hfit hint hk
    rw [hki] at hget
    exact hget
  · intro hget
    show (negNe cfg.branch.frame.2.length i).eval a = some true
    exact (eval_negNe_iff a _ i).mpr
      ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩

/-- The frame-restricted int pin (`hpinSkip`'s gate) under the same shape
discipline: the sibling's literal typing follows from the run box. -/
theorem decidePinTyped_int_of_shape {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {i : Int} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, .int i, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    DecidePinTyped cfg l (.int i) := by
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hpin : DecidePinTyped cfg l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers cfg.branch.frame a →
      a[cfg.branch.frame.2.length]? = some v := by
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : DecidePinTyped cfg l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers cfg.branch.frame a →
      FrameCovers ((doms, cfg.branch.frame.2 ++ [v])) a := by
  have hforce := stepDecide_redundant_forces_pin hreach hpin hred
  have hslots := (splitData_eq_some_iff.mp hsplit).1
  intro a hcov
  have hslot := hforce a hcov
  obtain ⟨tail, htail, heq⟩ := hcov
  have htail' : tail ∈ allAssigns ((v :: vs) :: doms) := by
    rwa [← hslots]
  obtain ⟨w, hw, suffix, hsuffix, rfl⟩ :=
    (mem_allAssigns_singleton v vs doms tail).mp htail'
  have hwv : w = v := by
    have hget : (cfg.branch.frame.2 ++ (w :: suffix))[
        cfg.branch.frame.2.length]? = some w := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [heq, hget] at hslot
    exact Option.some.inj hslot
  subst hwv
  refine ⟨suffix, hsuffix, ?_⟩
  rw [heq]
  simp only [List.append_assoc, List.singleton_append]

/-- **THE FORCED/SINGLETON CASE.** A singleton split's sibling frame
`([] :: doms, pre)` has an empty head domain, so it covers NO assignment
(L1's `not_frameCovers_of_empty_domain`): skipping the redundant forced
decision drops no alternative at all — the empty-frame exclusion route,
not inhabited-frame reasoning. -/
theorem stepDecide_singleton_sibling_empty {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, [], doms)) :
    ∀ a, ¬ FrameCovers (([] :: doms), cfg.branch.frame.2) a :=
  fun a h => not_frameCovers_of_empty_domain
    (f := (([] :: doms), cfg.branch.frame.2)) (a := a)
    ⟨[], List.mem_cons_self .., rfl⟩ h

/-! ## §3 Invariant closure beyond `hpin`/`hred` -/

/-- `decide` keeps the checkpoint-level discipline
(`checkpointsBelow_decide` of the forward module). -/
theorem stepDecide_checkpointsBelow {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {v : Value} {vs : Domain}
    {doms : List Domain} {l : Literal} (h : CheckpointsBelow cfg) :
    CheckpointsBelow (stepDecide cfg v vs doms l) :=
  checkpointsBelow_decide h

/-- **EXPLANATION PROVENANCE, UNCONDITIONAL:** `decide` touches neither
the learned database nor the compiled reasons; the trail only GROWS, and
`RecordedWith`'s falsifier set is trail-monotone
(`recordedWith_mono_trail`, L1). So L1's `LearnedProvenance` transfers
from any predecessor. -/
theorem stepDecide_learnedProvenance {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hprov : LearnedProvenance leaf cfg.branch) :
    LearnedProvenance leaf (stepDecide cfg v vs doms l).branch := by
  have hmono : ∀ e ∈ cfg.branch.trail,
      e ∈ (stepDecide cfg v vs doms l).branch.trail := by
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
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg (.bool b) vs doms l) :=
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
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain}
    (hrl : ReachableLearnedProvenance leaf (ReachableState leaf cfg.orig))
    (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    LearnedProvenance leaf (stepDecide cfg (.bool b) vs doms l).branch :=
  hrl _ (stepDecide_bool_reachable hinv hsplit hred)

/-- **INT DECISION, THE NAMED RESIDUAL ROUTE.** The full invariant for an
int decision exists exactly when `SlotIntTyped` holds (then the global
pin is `decidePin_global_of_slotIntTyped`). CONDITIONAL: the residual is
refuted in general (`int_slot_not_typed_witness` / `pin_int_global_false`),
so this is a reusable component — NOT an activation ingredient. -/
theorem stepDecide_int_invariant_of_slotTyped {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {i : Int} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame = some (l, .int i, vs, doms))
    (htyp : SlotIntTyped cfg)
    (hred : TrailRedundant cfg.branch.trail l = false) :
    SchedulerInvariant (stepDecide cfg (.int i) vs doms l) := by
  have hslots := (splitData_eq_some_iff.mp hsplit).1
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have hl : l = negNe cfg.branch.frame.2.length i := by
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
example : ¬ FrameCovers ((([Value.int 0] : List Value) :: []),
    ([] : Assignment)) [Value.bool false] := by
  rintro ⟨tail, htail, heq⟩
  have htail' : tail = [Value.int 0] := by simpa [allAssigns] using htail
  subst htail'
  cases heq

/-- Singleton split data (forced decision): the head `[.int 0]` splits
with an empty sibling `vs`. -/
example : splitData ((([Value.int 0] : List Value) :: []),
    ([] : Assignment)) =
    some (negNe 0 0, Value.int 0, [], []) := rfl

/-- Empty-domain boundary: `splitData` refuses an exhausted head. -/
example : splitData ((([] : List Value) :: []), ([] : Assignment)) = none := rfl

/-- Singleton frame: the one-slot singleton-domain frame covers exactly
its pinned value. -/
example : FrameCovers ((([Value.int 0] : List Value) :: []),
    ([] : Assignment)) [Value.int 0] :=
  ⟨[Value.int 0], by decide, rfl⟩

/-- ... and the empty-head sibling of a forced split covers nothing. -/
example : ¬ FrameCovers ((([] : List Value) :: []), ([] : Assignment))
    ([] : Assignment) := by
  intro h
  exact not_frameCovers_of_empty_domain
    (f := ((([] : List Value) :: []), ([] : Assignment)))
    (a := ([] : Assignment))
    ⟨[], List.mem_cons_self .., rfl⟩ h

end LeanFzn.Solver.UIP
