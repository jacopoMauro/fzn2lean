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
  import LeanFzn.Solver.UIP.Proofs.SchedulerDecideSkip
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Solver.UIP.Proofs.SchedulerJumpProgress
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 OPTION (a) IS FALSE — the redundant site is REACHABLE

The witness: the learned database carries the unit pin `slot 0 = 0`
(`negNe 0 0`) on the box `{0,1}`. The closure selects it, `narrowState`
narrows the head to `[.int 0]` and records the pin at level 0; the closure
is then STABLE (the clause is satisfied and re-derives nothing productive),
so the dispatch reaches `stableStep` with `splitData` returning exactly the
already-recorded pin. The engine's branch invariants do NOT exclude this:
`ReachableState.agrees` is one-directional (trail ⟹ covered frame), so the
frame may lag behind the trail; the only excluded shape is the genuine
branch (second value + completable tail). -/

/-- The witness root: box `{0,1}`, empty trail, the unit pin in the database. -/
def skipWitnessRoot : BranchState (fun _ : Assignment => true) :=
  { frame := ([[.int 0, .int 1]], []), trail := [], level := 0,
    learned := [[negNe 0 0]] }

/-- The closure selects the unit pin (kernel-checked evaluation). -/
example : (explainedDeduction [] [] skipWitnessRoot).map
    (fun d => d.literal) = some (negNe 0 0) := rfl

/-- The propagated successor: head narrowed to the pinned singleton, the
pin recorded at level 0 (exactly `stepPropagate`'s `narrowState` shape). -/
def skipWitnessBranch : BranchState (fun _ : Assignment => true) :=
  narrowState skipWitnessRoot ([[.int 0]], []) (negNe 0 0) [negNe 0 0] []

example : skipWitnessBranch.frame = ([[.int 0]], []) := rfl
example : skipWitnessBranch.learned = [[negNe 0 0]] := rfl

/-- The split of the narrowed head returns the ALREADY RECORDED pin. -/
example : splitData skipWitnessBranch.frame
    = some (negNe 0 0, .int 0, [], []) := rfl

/-- ... so the runtime's absence check fails at this site. -/
example : TrailRedundant skipWitnessBranch.trail (negNe 0 0) = true := rfl

/-- ... and the closure is STABLE here (the `.decide` arm's gate). -/
example : explainedDeduction [] [] skipWitnessBranch = none := rfl

/-- The configuration reaching the real `.decide` arm. -/
def skipWitnessCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { orig := [[.int 0, .int 1]], original := [], props := [],
    branch := skipWitnessBranch, checkpoints := [], pending := [], log := {} }

/-- THE CURRENT RUNTIME FIRES THE REDUNDANT DECISION (kernel-checked). -/
theorem skipWitness_stableStep_decide :
    stableStep skipWitnessCfg
      = .decide (stepDecide skipWitnessCfg (.int 0) [] [] (negNe 0 0))
          (negNe 0 0) := rfl

/-- ... AND THE SUCCESSOR IS NOT DISTINCT: the recorded pin plus the fresh
decision entry duplicate the trail literal, so the unguarded `.decide` arm
breaks `ReachableState.distinct` at this reachable state. This is the
kernel-checked refutation of option (a) (the irrelevant-branch question):
the guard describes a REAL runtime case, not a hypothetical. -/
theorem skipWitness_successor_not_distinct :
    ¬ TrailLiteralsDistinct
      (stepDecide skipWitnessCfg (.int 0) [] [] (negNe 0 0)).branch.trail :=
  TrailLiteralsDistinct.decide_duplicates
    ⟨{ literal := (negNe 0 0).norm, level := 0,
       reason := some { clause := [negNe 0 0] } },
     by simp [skipWitnessCfg, skipWitnessBranch, skipWitnessRoot, narrowState],
     rfl, by decide⟩

/-! ## §2 The skip constructor: shape and coverage core -/

/-- The skip's branch: pinned child frame, same trail/level. -/
theorem stepDecideSkip_branch {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).branch
      = { cfg.branch with frame := (doms, cfg.branch.frame.2 ++ [v]) } := rfl

/-- The skip records NO entry. -/
theorem stepDecideSkip_trail {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).branch.trail = cfg.branch.trail := rfl

/-- The skip keeps the level (no fresh decision level: the pin is recorded
already). -/
theorem stepDecideSkip_level {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).branch.level = cfg.branch.level := rfl

/-- The skip DROPS the sibling: no pending entry is pushed. -/
theorem stepDecideSkip_pending {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).pending = cfg.pending := rfl

/-- The skip pushes no checkpoint (not a branch point). -/
theorem stepDecideSkip_checkpoints {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).checkpoints = cfg.checkpoints := rfl

/-- The new frontier replaces the parent by the pinned child. -/
theorem stepDecideSkip_frontier {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    (stepDecideSkip cfg v doms).frontier
      = (doms, cfg.branch.frame.2 ++ [v]) :: cfg.pending := rfl

/-- CHILD ⊆ PARENT IN COVERAGE: the pinned child covers only assignments
the parent already covered (the pinned value is the parent head's first
value). -/
theorem covers_parent_of_covers_pinChild {f : BranchFrame} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (h : splitData f = some (l, v, vs, doms)) :
    ∀ a, FrameCovers (doms, f.2 ++ [v]) a → FrameCovers f a := by
  obtain ⟨slots, chosen⟩ := f
  cases slots with
  | nil => simp [splitData] at h
  | cons d rest =>
      cases d with
      | nil => simp [splitData] at h
      | cons w ws =>
          cases hl : valueLiteral (List.length chosen) w with
          | none => simp [splitData, hl] at h
          | some l' =>
              simp only [splitData, hl, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              intro a hcov
              obtain ⟨tail, htail, rfl⟩ := hcov
              exact ⟨w :: tail,
                allAssigns_cons_of_mem (List.mem_cons_self ..) htail,
                by simp only [List.append_assoc, List.singleton_append]⟩

/-- **THE NO-ALTERNATIVE-LOSS COVERAGE EQUALITY.** At the redundant site
(typed pin + recorded literal) the pinned child and the parent cover
EXACTLY the same assignments: S1's `stepDecide_redundant_no_alternative`
gives parent ⊆ child, and the child⊆parent direction is structural. Hence
the skip may drop the sibling, and the skip's frame move is
coverage-neutral for `ReachableState.agrees` (child-covered ⟹ parent-
covered) and for the frontier accounting (no represented leaf lost). -/
theorem stepDecideSkip_covers_iff {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : DecidePinTyped cfg l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a ↔
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
    (orig : List Domain) (cfg : SchedulerConfig leaf) (v : Value) : Prop :=
  ∀ a, (∀ e ∈ cfg.branch.trail, e.literal.eval a = some true) →
    a.Fits orig →
    a[cfg.branch.frame.2.length]? = some v

/-- The skip's `PrefixForced` follows from the parent's plus the named
typed residual. -/
theorem stepDecideSkip_prefixForced_of_typed {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {v : Value} {doms : List Domain}
    {orig : List Domain}
    (hprefix : PrefixForced cfg.branch.trail orig cfg.branch.frame.2)
    (htyped : DecideSkipPrefixTyped orig cfg v) :
    PrefixForced cfg.branch.trail orig
      (stepDecideSkip cfg v doms).branch.frame.2 := by
  intro a ha hfit i hi
  show a[i]? = (cfg.branch.frame.2 ++ [v])[i]?
  by_cases hlt : i < cfg.branch.frame.2.length
  · rw [List.getElem?_append, if_pos hlt]
    exact hprefix a ha hfit i hlt
  · have hi' : i = cfg.branch.frame.2.length := by
      have hlen : (stepDecideSkip cfg v doms).branch.frame.2.length
          = cfg.branch.frame.2.length + 1 := by
        simp [stepDecideSkip]
      omega
    subst hi'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    exact htyped a ha hfit

/-! ## §4 The dispatcher gate -/

/-- The guard's two arms are exactly the fresh and the redundant cases (the
split's literal is the branch's own check). -/
theorem stableStepGuarded_decide_shape {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    stableStepGuarded cfg =
      if TrailRedundant cfg.branch.trail l then
        .decide (stepDecideSkip cfg v doms) l
      else .decide (stepDecide cfg v vs doms l) l := by
  simp only [stableStepGuarded, hw, hsplit]

/-- The fresh arm: the guarded dispatch agrees with the unguarded one. -/
theorem stableStepGuarded_of_fresh {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    stableStepGuarded cfg = .decide (stepDecide cfg v vs doms l) l := by
  rw [stableStepGuarded_decide_shape hw hsplit, hred]
  simp

/-- The redundant arm: the skip successor, no duplicate entry. -/
theorem stableStepGuarded_of_redundant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    stableStepGuarded cfg = .decide (stepDecideSkip cfg v doms) l := by
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
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    PhaseLt (PhaseRankSorted orig (stepDecideSkip cfg v doms))
      (PhaseRankSorted orig cfg) :=
  Or.inr ⟨rfl, Or.inl (frontierCost_stepDecideSkip_lt hsplit)⟩

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
    {v : Value} {vs : Domain} {doms : List Domain}
    (h : ReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (htyped : DecideSkipPrefixTyped orig cfg v) :
    ReachableState leaf orig (stepDecideSkip cfg v doms).branch := by
  obtain ⟨hslots, _⟩ := splitData_eq_some_iff.mp hsplit
  have hframe : cfg.branch.frame = ((v :: vs) :: doms, cfg.branch.frame.2) :=
    Prod.ext hslots rfl
  rw [stepDecideSkip_branch]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length_ok: the head domain is replaced by one prefix value
    show (fullDomains (doms, cfg.branch.frame.2 ++ [v])).length = orig.length
    have hp := h.length_ok
    rw [hframe] at hp
    refine Eq.trans ?_ hp
    simp only [fullDomains, Frame.domains, List.length_append,
      List.length_cons, List.length_map, List.length_nil]
    omega
  · -- full_fits: pinning narrows the box, it never invents values
    show ∀ i w, w ∈ (fullDomains (doms, cfg.branch.frame.2 ++ [v])).getD i [] →
      w ∈ orig.getD i []
    have hfit := h.full_fits
    rw [hframe] at hfit
    intro i w hw
    exact hfit i w (fullDomains_decide_subset (List.mem_cons_self ..) i w hw)
  · -- prefix_forced: the extended prefix's last value is the typed pin
    show PrefixForced cfg.branch.trail orig (cfg.branch.frame.2 ++ [v])
    exact stepDecideSkip_prefixForced_of_typed (doms := doms)
      h.prefix_forced htyped
  · -- agrees: the child frame covers only parent-covered assignments
    show ∀ e ∈ cfg.branch.trail, ∀ a,
      FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a →
        e.literal.eval a = some true
    intro e he a ha
    exact h.agrees e he a (covers_parent_of_covers_pinChild hsplit a ha)
  · -- narrowing_complete: same remaining domains, shifted prefix index
    show NarrowingComplete cfg.branch.trail orig (doms, cfg.branch.frame.2 ++ [v])
    intro i w horig hnot
    have hi1 : (cfg.branch.frame.2 ++ [v]).length + i
        = cfg.branch.frame.2.length + (i + 1) := by
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨e, he, hslot, hval⟩ :=
      h.narrowing_complete (i + 1) w (by rw [hi1] at horig; exact horig) (by
        rw [hslots]
        simpa using hnot)
    exact ⟨e, he, by rw [hi1]; exact hslot, hval⟩
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
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    DecideSkipPrefixTyped orig cfg (.bool b) := by
  intro a htrail _
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have heval : l.eval a = some true := by
    have h1 : e.literal.eval a = some true := htrail e he
    rwa [hil, Literal.norm_eval] at h1
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have h := (valueLiteral_holds_iff hwl a).mp heval
  simpa using h

/-- **THE INT SKIP PRODUCER (B2a)**: at a redundant int-pin site of a
shape-typed run box, the extended-prefix residual holds — the correct,
non-refuted replacement of the global skip residual (whose instantiation
is refuted at the `.bool false` collision witness). -/
theorem decideSkipPrefixTyped_int {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {i : Int} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, .int i, vs, doms))
    (hreach : ReachableState leaf orig cfg.branch)
    (hred : TrailRedundant cfg.branch.trail l = true)
    (hshape : ShapeTypedDomains orig) :
    DecideSkipPrefixTyped orig cfg (.int i) := by
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have hl : l = negNe cfg.branch.frame.2.length i := by
    rw [valueLiteral_int] at hwl
    exact (Option.some.inj hwl).symm
  have hint := intShaped_of_mem_int hshape
    (pinHead_mem_orig hsplit hreach)
  intro a htrail hfit
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have h1 : (l.norm).eval a = some true := by
    have h3 := htrail e he
    rwa [hil] at h3
  rw [hl] at h1
  obtain ⟨k, hk, hki⟩ := (eval_negNe_iff a _ i).mp h1
  have hget := getElem_of_slotInt_typed hfit hint hk
  rw [hki] at hget
  exact hget

/-- **THE BOOLEAN SKIP IS REACHABLE-SAFE, NO RESIDUAL**: the redundant Bool
site's successor is a reachable branch state of the same box with the typed
pin discharged internally. -/
theorem reachable_decideSkip_bool {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {b : Bool} {vs : Domain} {doms : List Domain}
    (h : ReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ReachableState leaf orig (stepDecideSkip cfg (.bool b) doms).branch :=
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
    {cfg : SchedulerConfig leaf} {v : Value} {doms : List Domain}
    (hinv : SchedulerInvariant cfg) :
    ∀ f ∈ (stepDecideSkip cfg v doms).pending, ∀ i w,
      w ∈ (Frame.domains f).getD i [] → w ∈ cfg.orig.getD i [] :=
  fun f hf i w hw => hinv.pending_fits f (by simpa [stepDecideSkip] using hf) i w hw

/-- BRANCH SUB-BOX: the pinned child's full box is a pointwise subset of
the parent's (the child replaces the head domain by the pinned value). -/
theorem stepDecideSkip_branch_fits {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ i w, w ∈ (Frame.domains (stepDecideSkip cfg v doms).branch.frame).getD i [] →
      w ∈ cfg.orig.getD i [] := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hfe : cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2) :=
    Prod.ext hdom rfl
  have hw : v ∈ (v :: vs : Domain) := List.mem_cons_self ..
  intro i w hw'
  refine hinv.branch_fits i w ?_
  rw [hfe]
  exact fullDomains_decide_subset hw i w
    (by simpa only [fullDomains, stepDecideSkip] using hw')

/-- CHECKPOINT IDENTITY of the skip: the checkpoints are untouched, the
trail and level are untouched, and the frame only descends to the pinned
child — so every old checkpoint still identifies the new branch at its own
level. No `CheckpointsBelow` input is needed (unlike `stepDecide`, which
raises the level). -/
theorem stepDecideSkip_checkpoints_identify {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ cp ∈ (stepDecideSkip cfg v doms).checkpoints,
      cp.Identifies (stepDecideSkip cfg v doms).branch cp.level := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hchild : FrameDescendsFrom (doms, cfg.branch.frame.2 ++ [v])
      cfg.branch.frame := by
    rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
      from Prod.ext hdom rfl]
    exact fun a ha => FrameCovers_decide (List.mem_cons_self ..) ha
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hident : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    ∀ cp ∈ (stepDecideSkip cfg v doms).checkpoints,
      cp.Identifies (stepDecideSkip cfg v doms).branch cp.level := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  have hchild : FrameDescendsFrom (doms, cfg.branch.frame.2 ++ [v])
      cfg.branch.frame := by
    rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
      from Prod.ext hdom rfl]
    exact fun a ha => FrameCovers_decide (List.mem_cons_self ..) ha
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : DecidePinTyped cfg l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    (stepDecideSkip cfg v doms).coverage := by
  intro a hleaf
  rcases hinv.coverage a hleaf with ⟨f, hf, hcov⟩ | hdb
  · have hf' : f = cfg.branch.frame ∨ f ∈ cfg.pending := by
      simpa [SchedulerConfig.frontier] using hf
    rcases hf' with rfl | hf
    · left
      exact ⟨(doms, cfg.branch.frame.2 ++ [v]), List.mem_cons_self ..,
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
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : DecidePinTyped cfg l v)
    (htyped : DecideSkipPrefixTyped cfg.orig cfg v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    SchedulerInvariant (stepDecideSkip cfg v doms) :=
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
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {doms : List Domain} (hinv : SchedulerInvariant cfg)
    (hsplit : splitData cfg.branch.frame = some (l, .bool b, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    SchedulerInvariant (stepDecideSkip cfg (.bool b) doms) :=
  stepDecideSkip_invariant hinv hsplit (decidePinTyped_bool hsplit)
    (decideSkipPrefixTyped_bool hsplit hred) hred

end LeanFzn.Solver.UIP
