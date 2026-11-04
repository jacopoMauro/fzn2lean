/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerDecideSkip.lean

Purpose:
  THE REDUNDANT `.decide` GUARD. S1 (`SchedulerDecision.lean`) proved that a
  decision whose normalized pin literal is already recorded duplicates the
  trail entry and destroys `ReachableState.distinct`
  (`stepDecide_redundant_not_distinct`), and supplied the no-loss content of
  the skip (`stepDecide_redundant_forces_pin`, `stepDecide_redundant_no_
  alternative`). This file settles the option question and lands the skip
  constructor's proved core:

  * §1 — OPTION (a) IS FALSE. The redundant case is NOT excluded by the
    branch invariants: a unit clause whose literal IS the pin narrows the
    head to the pinned singleton, the closure is then stable
    (`explainedDeduction = none`), and `stableStep` fires `.decide` with the
    redundant literal (kernel-checked evaluation witnesses below) whose
    successor has a duplicated trail entry. Option (a)'s only true half is
    the genuine-branch case (second head value + completable tail ⇒ the pin
    is unforced ⇒ fresh), where A1's `fresh_of_not_forced` applies.
  * §2 — the skip constructor `stepDecideSkip` (runtime,
    `LeanFzn/Solver/UIP/SchedulerStep.lean`): frame advances to the pinned child,
    trail/level/checkpoints/pending untouched, sibling DROPPED. Proved here:
    the shape equations, the child⊆parent coverage direction, and the
    no-alternative-loss coverage EQUALITY (S1's lemma + that direction).
  * §3 — the named residual: the skip's `PrefixForced` obligation is
    `DecideSkipPrefixTyped`, discharged unconditionally for Bool (the pin
    is globally exact) and refuted in general for Int (the `.bool false`
    value collision, `int_slot_not_typed_witness`); the int skip is a named
    conditional exactly like `stepDecide_int_invariant_of_slotTyped`.
  * §4 — the dispatcher gate `stableStepGuarded` (runtime, new name).

  REMAINING FIELD-BY-FIELD OBLIGATIONS for the Bool skip's full
  `ReachableState` preservation (owner: whoever rewires the dispatcher):
  1. length_ok  — `fullDomains (doms, pre ++ [v])).length = orig.length`
     (one shift; from `hreach.length_ok`).
  2. full_fits  — the child box is a pointwise sub-box of the parent's
     (`v ∈ v :: vs`), then `hreach.full_fits`.
  3. prefix_forced — §3's `stepDecideSkip_prefixForced_of_typed`; Bool
     residual discharged globally by `valueLiteral_holds_iff`, Int is the
     named conditional.
  4. agrees — child-covered ⟹ parent-covered (§2's
     `covers_parent_of_covers_pinChild`), then `hreach.agrees`.
  5. narrowing_complete — index shift by one (parent index i+1 = child
     index i); the slot `pre.length` becomes a prefix slot and needs no
     witness.
  6. wf / sorted / distinct — trail UNCHANGED, so `hreach.wf`,
     `hreach.sorted`, `hreach.distinct` transfer by definitional equality.
  Coverage frontier accounting (`CoversRemainingLeaves` rows) uses §2's
  equality: the dropped sibling covers nothing the child does not.

Dependencies (all below in the DAG):
  - LeanFzn.Solver.UIP.Proofs.SchedulerDecision (S1: the redundant-pin lemmas,
    `DecidePinTyped`).
  - runtime `LeanFzn/Solver/UIP/SchedulerStep.lean` (`stepDecideSkip`,
    `stableStepGuarded`) via SchedulerForward.
Registration line owed by the coordinator (umbrella `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`):
  import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecideSkip
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerJumpProgress
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 NOTE (M5): the historical redundant-site WITNESS is RETIRED

The former witness (a unit pin `slot 0 = 0` on the box `{0,1}`, the head
narrowed to the singleton `[.int 0]`, `splitData` returning the already
recorded pin) is OBSOLETE under the S1 `selectSlot` policy: a narrowed
SINGLETON head is not LIVE, so `splitData` returns `none` there and the
dispatch takes the local-exclusion arm, never the redundant decide. The
redundant-pin skip arm of `stableStepGuarded` remains (the guard itself
is unchanged); whether a redundant site is reachable under the S1 policy
is an integration question (owner D1/runtime), not a proof-layer one —
the guard's correctness lemmas below hold for every site that fires it. -/

/-! ## §2 The skip constructor: shape and coverage core -/

/-- The skip's branch: pinned child frame, same trail/level. -/
theorem stepDecideSkip_branch {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).branch
      = { cfg.branch with frame := cfg.branch.frame.pin k v } := rfl

/-- The skip records NO entry. -/
theorem stepDecideSkip_trail {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).branch.trail = cfg.branch.trail := rfl

/-- The skip keeps the level (no fresh decision level: the pin is recorded
already). -/
theorem stepDecideSkip_level {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).branch.level = cfg.branch.level := rfl

/-- The skip DROPS the sibling: no pending entry is pushed. -/
theorem stepDecideSkip_pending {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).pending = cfg.pending := rfl

/-- The skip pushes no checkpoint (not a branch point). -/
theorem stepDecideSkip_checkpoints {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).checkpoints = cfg.checkpoints := rfl

/-- The new frontier replaces the parent by the pinned child. -/
theorem stepDecideSkip_frontier {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).frontier
      = cfg.branch.frame.pin k v :: cfg.pending := rfl

/-- CHILD ⊆ PARENT IN COVERAGE: the pinned child covers only assignments
the parent already covered (the pinned value is the parent head's first
value). -/
theorem covers_parent_of_covers_pinChild {f : BranchFrame} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    {σ : List Nat} (h : splitData f σ = some (l, k, v, vs)) :
    ∀ a, FrameCovers (f.pin k v) a → FrameCovers f a := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData h
  have hv : v ∈ d := (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)
  exact fun a hcov => FrameCovers_pin_subset hd hv hcov

/-- **THE NO-ALTERNATIVE-LOSS COVERAGE EQUALITY.** At the redundant site
(typed pin + recorded literal) the pinned child and the parent cover
EXACTLY the same assignments: S1's `stepDecide_redundant_no_alternative`
gives parent ⊆ child, and the child⊆parent direction is structural. Hence
the skip may drop the sibling, and the skip's frame move is
coverage-neutral for `ReachableState.agrees` (child-covered ⟹ parent-
covered) and for the frontier accounting (no represented leaf lost). -/
theorem stepDecideSkip_covers_iff {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : DecidePinTyped cfg k l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers (cfg.branch.frame.pin k v) a ↔
      FrameCovers cfg.branch.frame a :=
  fun a =>
    ⟨covers_parent_of_covers_pinChild hsplit a,
     stepDecide_redundant_no_alternative hreach hsplit hpin hred a⟩

/-! ## §3 The named residual: the extended prefix's forcing -/

/-- **THE SKIP'S `PrefixForced` RESIDUAL, NAMED.** Every trail-satisfying
assignment takes the PINNED VALUE at the split slot — exactly what
`PrefixForced` needs for the extended prefix `pre ++ [v]`. Bool: globally
true (the Boolean pin `posBool s b` holds iff the slot is literally
`.bool b`, `valueLiteral_holds_iff` — no residual); Int: refuted in
general (an assignment whose split slot is `.bool false` satisfies
`negNe s 0` yet is not `.int 0`; `int_slot_not_typed_witness`,
`pin_int_global_false`), so the int skip route is a named conditional like
`stepDecide_int_invariant_of_slotTyped`. -/
def DecideSkipPrefixTyped {leaf : Assignment → Bool}
    (orig : List Domain) (cfg : SchedulerConfig leaf) (k : Nat)
    (v : Value) : Prop :=
  ∀ a, (∀ e ∈ cfg.branch.trail, e.literal.eval a = some true) →
    a.Fits orig → a[k]? = some v

/-- The skip's `PinsForced` follows from the parent's plus the named
typed residual at the pinned slot: the pin only writes slot `k`, so every
parent-decided slot keeps its recorded singleton and its forcing. -/
theorem stepDecideSkip_pinsForced_of_typed {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} {orig : List Domain}
    (hprefix : PinsForced cfg.branch.trail orig cfg.branch.frame)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (htyped : DecideSkipPrefixTyped orig cfg k v) :
    PinsForced cfg.branch.trail orig
      (stepDecideSkip cfg k v).branch.frame := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hklt : k < cfg.branch.frame.doms.length :=
    (List.getElem?_eq_some_iff.mp hd).1
  intro j hj
  rw [stepDecideSkip_branch, BranchFrame.pin_order] at hj
  rw [stepDecideSkip_branch]
  rw [List.mem_append] at hj
  by_cases hjk : j = k
  · -- the pinned slot itself: the typed residual is its forcing
    subst hjk
    exact ⟨v, by
      rw [BranchFrame.pin_doms, List.getElem?_set_self hklt]
      simp,
      fun a ha hfit => htyped a ha hfit⟩
  · -- an already-decided slot: the pin writes only `k`
    have hjorder : j ∈ cfg.branch.frame.order := by
      rcases hj with hj | hj
      · exact hj
      · exact absurd (List.mem_singleton.mp hj) hjk
    obtain ⟨v', hv', hforce⟩ := hprefix j hjorder
    refine ⟨v', ?_, hforce⟩
    rw [BranchFrame.pin_doms, getElem?_set_of_ne hjk, hv']

/-! ## §4 The dispatcher gate -/

/-- The guard's two arms are exactly the fresh and the redundant cases (the
split's literal is the branch's own check). -/
theorem stableStepGuarded_decide_shape {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    stableStepGuarded cfg =
      if TrailRedundant cfg.branch.trail l then
        .decide (stepDecideSkip cfg k v) l
      else .decide (stepDecide cfg k v vs l) l := by
  simp only [stableStepGuarded, hw, hsplit]

/-- The fresh arm: the guarded dispatch agrees with the unguarded one. -/
theorem stableStepGuarded_of_fresh {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    stableStepGuarded cfg = .decide (stepDecide cfg k v vs l) l := by
  rw [stableStepGuarded_decide_shape hw hsplit, hred]
  simp

/-- The redundant arm: the skip successor, no duplicate entry. -/
theorem stableStepGuarded_of_redundant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    stableStepGuarded cfg = .decide (stepDecideSkip cfg k v) l := by
  rw [stableStepGuarded_decide_shape hw hsplit, hred]
  simp

/-! ## §5 The skip's rank decrease

The redundant-pin skip replaces the head frame `((v :: vs) :: doms, pre)`
by the pinned child `(doms, pre ++ [v])`. The remaining-domain list loses
its nonempty head, so the chronological component strictly drops; the
learned database, the status and the pending stack are untouched, so P3's
`PhaseRank` and P4's sorted-shape `PhaseRankSorted` strictly decrease in
that component. The rank-agnostic frontier drop and the P3 lemma live in
`Proofs/SchedulerRank.lean` (`P3.frontierCost_stepDecideSkip_lt`,
`P3.phaseRank_lt_decideSkip`) so the P5 assembly can consume them without
an import cycle; the P4 wrapper stays here. -/

open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.P3 LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.P4

/-- **THE SORTED-SHAPE RANK DECREASE AT THE SKIP.** The same statement for
P4's order-insensitive rank `PhaseRankSorted`: component 1 is unchanged
(the skip writes no learned clause) and component 2.1 strictly drops
(`P3.frontierCost_stepDecideSkip_lt`). -/
theorem phaseLtSorted_stepDecideSkip (orig : List Domain)
    {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hall : ∀ e ∈ cfg.branch.frame.doms, e.enum ≠ []) :
    PhaseLt (PhaseRankSorted orig (stepDecideSkip cfg k v))
      (PhaseRankSorted orig cfg) :=
  P4.phaseRankSorted_lt_decideSkip orig cfg k v vs l hsplit hall

/-! ## §6 B1 round 2: the skip successor is a reachable branch state

The skip advances the frame to the pinned child
(`(doms, pre ++ [v])`) with NO trail and NO level change, so the
trail-indexed fields (`agrees`, `wf`, `sorted`, `distinct`) transfer
directly, while the frame-indexed fields
(`length_ok`/`full_fits`/`prefix_forced`/`narrowing_complete`) mirror
`reachable_decide`'s frame move (the parent head `(v :: vs) :: doms` loses
its head domain and the prefix gains `v`; the child box is a pointwise
subset of the parent box). The only named residual is the typed pin
(`DecideSkipPrefixTyped`, globally discharged for Bool by
`decidePinTyped_bool`, conditional for Int by `decidePinTyped_int`). -/

/-- **THE SKIP SUCCESSOR IS REACHABLE**: the redundant-pin skip applied to a
reachable branch state, at a real split site, with the typed pin residual,
yields a reachable branch state of the SAME original box. This is the B1
trace step the arm/reachability assemblies consume; no successor
reachability field is assumed. -/
theorem reachable_decideSkip {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (h : ReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (htyped : DecideSkipPrefixTyped orig cfg k v) :
    ReachableState leaf orig (stepDecideSkip cfg k v).branch := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hklt : k < cfg.branch.frame.doms.length :=
    (List.getElem?_eq_some_iff.mp hd).1
  have hsub : ∀ w ∈ (Dom.ofList [v] : Domain), w ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    intro w hw
    have hwv : w = v := by
      have hwE : w ∈ Dom.enum (Dom.ofList [v]) := (DomainLike.mem_iff _ _).mp hw
      rwa [Dom.enum_ofList, List.mem_singleton] at hwE
    subst hwv
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum, List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]
    exact List.mem_cons_self ..
  rw [stepDecideSkip_branch]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length_ok: the pin preserves the slot count
    show (fullDomains (cfg.branch.frame.pin k v)).length = orig.length
    rw [fullDomains, Frame.domains, BranchFrame.pin_doms, List.length_set]
    exact h.length_ok
  · -- full_fits: pinning narrows the box, it never invents values
    show ∀ i w, w ∈ (fullDomains (cfg.branch.frame.pin k v)).getD i Dom.empty →
      w ∈ orig.getD i Dom.empty
    intro i w hw
    exact h.full_fits i w (getD_set_subset hsub i w hw)
  · -- pins_forced: the typed residual covers the pinned slot
    exact stepDecideSkip_pinsForced_of_typed h.pins_forced hsplit htyped
  · -- agrees: the child frame covers only parent-covered assignments
    show ∀ e ∈ cfg.branch.trail, ∀ a,
      FrameCovers (cfg.branch.frame.pin k v) a →
        e.literal.eval a = some true
    intro e he a ha
    exact h.agrees e he a (covers_parent_of_covers_pinChild hsplit a ha)
  · -- narrowing_complete: the pin writes only the split slot
    show NarrowingComplete cfg.branch.trail orig (cfg.branch.frame.pin k v)
    intro j hj w hw hnot
    have hjparent : j ∉ cfg.branch.frame.order := fun hmem => hj (
      List.mem_append.mpr (Or.inl hmem))
    have hne : j ≠ k := fun heq => hj (by
      rw [BranchFrame.pin_order, List.mem_append]
      exact Or.inr (List.mem_singleton.mpr heq))
    have hnotparent : w ∉ cfg.branch.frame.doms.getD j Dom.empty := by
      intro hmem
      apply hnot
      rw [BranchFrame.pin_doms, List.getD_eq_getElem?_getD,
        getElem?_set_of_ne hne]
      exact hmem
    obtain ⟨e, he, hslot, hval⟩ :=
      h.narrowing_complete j hjparent w hw hnotparent
    exact ⟨e, he, hslot, hval⟩
  · -- wf: trail and learned database are untouched
    exact h.wf
  · -- sorted: trail untouched
    exact h.sorted
  · -- distinct: trail untouched
    exact h.distinct

/-! ## §7 B1 round 3: the Boolean typed-pin discharge

The skip's named residual `DecideSkipPrefixTyped` asks that every
trail-satisfying assignment takes the pinned value at the split slot. At a
redundant site the pin literal itself is already recorded (`TrailRedundant`),
so the residual reduces to the pin's own semantics —
`valueLiteral_holds_iff`, which is EXACT for Boolean values and is exactly
the global equivalence. For Int values the same road does not exist
(`negNe s k` holds at any value `≠ k`, not at one fixed value;
`int_slot_not_typed_witness`), which is why the Int route keeps its named
Slot-int-typed gate. -/

/-- The Boolean site discharge: a redundant Boolean pin has NO
`PrefixForced` residual. -/
theorem decideSkipPrefixTyped_bool {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {b : Bool} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, (.bool b : Value), vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    DecideSkipPrefixTyped orig cfg k (.bool b) := by
  intro a htrail _
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have heval : l.eval a = some true := by
    have h1 : e.literal.eval a = some true := htrail e he
    rwa [hil, Literal.norm_eval] at h1
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have h := (valueLiteral_holds_iff hwl a).mp heval
  simpa using h

/-- **THE INT SKIP PRODUCER (B2a)**: at a redundant int-pin site of a
shape-typed run box, the extended-prefix residual holds — the correct,
non-refuted replacement of the global skip residual (whose instantiation
is refuted at the `.bool false` collision witness). -/
theorem decideSkipPrefixTyped_int {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {i : Int} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, (.int i : Value), vs))
    (hreach : ReachableState leaf orig cfg.branch)
    (hred : TrailRedundant cfg.branch.trail l = true)
    (hshape : ShapeTypedDomains orig) :
    DecideSkipPrefixTyped orig cfg k (.int i) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have hl : l = negNe k i := by
    have h := hwl
    rw [valueLiteral_int] at h
    exact (Option.some.inj h).symm
  have hint := intShaped_of_mem_int hshape
    (pinHead_mem_orig hsplit hreach)
  intro a htrail hfit
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have h1 : (l.norm).eval a = some true := by
    have h3 := htrail e he
    rwa [hil] at h3
  rw [hl] at h1
  obtain ⟨j, hj, hji⟩ := (eval_negNe_iff a _ i).mp h1
  have hget := getElem_of_slotInt_typed hfit hint hj
  rw [hji] at hget
  exact hget

/-- **THE BOOLEAN SKIP IS REACHABLE-SAFE, NO RESIDUAL**: the redundant Bool
site's successor is a reachable branch state of the same box with the typed
pin discharged internally. -/
theorem reachable_decideSkip_bool {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {b : Bool} {vs : Domain}
    (h : ReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, (.bool b : Value), vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ReachableState leaf orig (stepDecideSkip cfg k (.bool b)).branch :=
  reachable_decideSkip h hsplit (decideSkipPrefixTyped_bool hsplit hred)

/-! ## §8 B1 round 4: the skip's invariant arm (for B4's assembly)

`schedulerNext`'s `.decide` arm can now be the redundant-pin skip, so the
reachable-invariant assembly must handle the skip successor. Compared with
`stepDecide`'s successor, the skip keeps the trail and level, pushes no
checkpoint and no sibling; the frame move to the pinned child
`(doms, pre ++ [v])` is the same. The named gates are the typed pin
`DecidePinTyped` (coverage: the dropped sibling carries no represented
leaf) and the extended-prefix residual `DecideSkipPrefixTyped`
(reachability); both are global for Boolean values
(`decideSkipPrefixTyped_bool`, `decidePinTyped_bool`) and conditional for
Int (`decidePinTyped_int`). -/

/-- PENDING PROVENANCE: the skip leaves the pending stack untouched. -/
theorem stepDecideSkip_pending_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {k : Nat} {v : Value}
    (hinv : SchedulerInvariant cfg) :
    ∀ f ∈ (stepDecideSkip cfg k v).pending, ∀ i w,
      w ∈ (Frame.domains f).getD i Dom.empty → w ∈ cfg.orig.getD i Dom.empty :=
  fun f hf i w hw => hinv.pending_fits f (by simpa [stepDecideSkip] using hf) i w hw

/-- BRANCH SUB-BOX: the pinned child's full box is a pointwise subset of
the parent's (the child replaces the head domain by the pinned value). -/
theorem stepDecideSkip_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ i w, w ∈ (Frame.domains (stepDecideSkip cfg k v).branch.frame).getD i Dom.empty →
      w ∈ cfg.orig.getD i Dom.empty := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hsub : ∀ w ∈ (Dom.ofList [v] : Domain), w ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    intro w hw
    have hwv : w = v := by
      have hwE : w ∈ Dom.enum (Dom.ofList [v]) := (DomainLike.mem_iff _ _).mp hw
      rwa [Dom.enum_ofList, List.mem_singleton] at hwE
    subst hwv
    refine (DomainLike.mem_iff _ _).mpr ?_
    rw [domElems_eq_enum, List.getD_eq_getElem?_getD, hd, Option.getD_some, hde]
    exact List.mem_cons_self ..
  intro i w hw'
  exact hinv.branch_fits i w (getD_set_subset hsub i w hw')

/-- CHECKPOINT IDENTITY of the skip: the checkpoints are untouched, the
trail and level are untouched, and the frame only descends to the pinned
child — so every old checkpoint still identifies the new branch at its own
level. No `CheckpointsBelow` input is needed (unlike `stepDecide`, which
raises the level). -/
theorem stepDecideSkip_checkpoints_identify {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ cp ∈ (stepDecideSkip cfg k v).checkpoints,
      cp.Identifies (stepDecideSkip cfg k v).branch cp.level := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hv : v ∈ d := (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)
  have hchild : FrameDescendsFrom (cfg.branch.frame.pin k v)
      cfg.branch.frame :=
    fun a ha => FrameCovers_pin_subset hd hv ha
  intro cp hcp
  obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ :=
    hinv.checkpoints_identify cp (by simpa [stepDecideSkip] using hcp)
  exact ⟨hlev, ⟨mid, by simpa [stepDecideSkip] using htrail, hmid⟩,
    fun a ha => hdesc a (hchild a ha)⟩

/-- FIELD-ONLY VARIANT of `stepDecideSkip_checkpoints_identify` (J1 hident
wrapper): the supported identifies+chain induction carries only the
`checkpoints_identify` conjunct. -/
theorem stepDecideSkip_checkpoints_identify_of_identifies
    {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain}
    (hident : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    ∀ cp ∈ (stepDecideSkip cfg k v).checkpoints,
      cp.Identifies (stepDecideSkip cfg k v).branch cp.level := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_splitData hsplit
  have hv : v ∈ d := (DomainLike.mem_iff _ _).mpr (by
    rw [domElems_eq_enum, hde]
    exact List.mem_cons_self ..)
  have hchild : FrameDescendsFrom (cfg.branch.frame.pin k v)
      cfg.branch.frame :=
    fun a ha => FrameCovers_pin_subset hd hv ha
  intro cp hcp
  obtain ⟨hlev, ⟨mid, htrail, hmid⟩, hdesc⟩ :=
    hident cp (by simpa [stepDecideSkip] using hcp)
  exact ⟨hlev, ⟨mid, by simpa [stepDecideSkip] using htrail, hmid⟩,
    fun a ha => hdesc a (hchild a ha)⟩

/-- COVERAGE of the skip: the parent frame is replaced by the pinned child,
and under the redundant guard + typed pin the child covers EVERY assignment
the parent covered (`stepDecide_redundant_no_alternative`), so the frontier
loses no leaf solution; pending and database are untouched. -/
theorem stepDecideSkip_covers {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : DecidePinTyped cfg k l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    (stepDecideSkip cfg k v).coverage := by
  intro a hleaf
  rcases hinv.coverage a hleaf with ⟨f, hf, hcov⟩ | hdb
  · have hf' : f = cfg.branch.frame ∨ f ∈ cfg.pending := by
      simpa [SchedulerConfig.frontier] using hf
    rcases hf' with rfl | hf
    · left
      exact ⟨cfg.branch.frame.pin k v, List.mem_cons_self ..,
        stepDecide_redundant_no_alternative hinv.reachable hsplit hpin hred a
          hcov⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ (by simpa [stepDecideSkip] using hf),
        hcov⟩
  · right
    exact hdb

/-- **INVARIANT PRESERVATION AT THE SKIP**, field by field. Gates: the typed
pin (coverage) and the extended-prefix residual (reachability); the log and
the learned database are carried through unchanged. -/
theorem stepDecideSkip_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : DecidePinTyped cfg k l v)
    (htyped : DecideSkipPrefixTyped cfg.orig cfg k v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    SchedulerInvariant (stepDecideSkip cfg k v) :=
  ⟨reachable_decideSkip hinv.reachable hsplit htyped,
    stepDecideSkip_checkpoints_identify hinv hsplit,
    stepDecideSkip_pending_fits hinv,
    stepDecideSkip_branch_fits hinv hsplit,
    hinv.log_sound,
    stepDecideSkip_covers hinv hsplit hpin hred,
    hinv.learned_entailed⟩

/-- **THE BOOLEAN SKIP'S INVARIANT ARM, NO RESIDUALS**: both typed gates are
globally discharged for Boolean pins. -/
theorem stepDecideSkip_invariant_bool {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {b : Bool}
    {vs : Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, (.bool b : Value), vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    SchedulerInvariant (stepDecideSkip cfg k (.bool b)) :=
  stepDecideSkip_invariant hinv hsplit (decidePinTyped_bool hsplit)
    (decideSkipPrefixTyped_bool hsplit hred) hred

end LeanFzn.Solver.UIP
