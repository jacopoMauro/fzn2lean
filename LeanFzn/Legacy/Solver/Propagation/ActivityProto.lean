/-
File: LeanFzn/Solver/Propagation/ActivityProto.lean

Purpose (PLAN task S2 prototype: dynamic activity and phase selection):

  A STANDALONE, UNWIRED prototype of the S2 heuristic layer on top of the
  S0/S1 sparse-frame vocabulary (`DecisionProto.lean`): per-slot conflict
  ACTIVITY metadata, deterministic bounded update with a proved rescale
  step, optional PHASE saving (last decided value per slot), and an
  activity-aware variable-selection rule that falls back to the S1
  minimum-cardinality rule when scores tie or are absent.

  Nothing here is imported by any runtime module; no shared file is
  edited; the semantic search state (`Frame`) is never touched. The
  metadata lives in a separate structure `Meta` that is threaded ALONGSIDE
  the frame (PLAN §8 S2: "keep heuristic metadata separate from semantic
  state").

  Contents:

  * §1 `bestOfAct` — the S2 scan over the aligned (scores, box) pair: the
    live slot maximizing the activity score; ties broken by the S1
    minimum-cardinality rule, then by the smallest slot index. `BestActSpec`
    is its exact specification and `bestOfAct_spec` its proof (one
    structural pass, exact `Nat` scores, no floats).
  * §2 `selectSlotAct` and its specification `selectSlotAct_live` /
    `selectSlotAct_min` / `selectSlotAct_complete` / `selectSlotAct_none_iff`;
    `KeyActLE` and the determinism facts `selectSlotAct_eq_of_min` /
    `selectSlotAct_unique_min`; `selectSlotAct_const` (scores tied ⇒ exactly
    the S1 rule) and the absent-score instance `selectSlotAct_zero`.
  * §3 `Meta` — activity scores + saved phases, aligned with the box;
    `Meta.WF` metadata validity; `bumpAt`/`maxOf`/`step`/`update` with the
    proved finiteness bound `RESCALE_BOUND` (`Meta.Bounded`, `step_bounded`,
    `update_bounded`) and the exact-step dichotomy `step_bump_or_halve`
    (the only score changes are "+1 on a recorded slot" or "halve all");
    `Meta.bump` (pure conflict recording) with `Meta.bump_empty`,
    `Meta.bump_mono`, `Meta.bump_scoreAt_of_not_mem` (activity is read only
    from the recorded conflict slots) and the WF preservation
    `Meta.WF.bump` / `Meta.WF.update`; `bumpAt_scoreAt_eq_or_succ`
    (exactness of one bump).
  * §4 optional phase saving: `valEqB` (sound boolean value equality),
    `hasValB`, `eraseVal`, `moveToFront` (a proved permutation), `savePhase`
    / `phaseAt` and `suggest`; facts `moveToFront_perm`,
    `moveToFront_ne_nil`, `Meta.WF.savePhase`, `Meta.savePhase_scoreAt`,
    `Meta.suggest_perm`, `Meta.suggest_of_phaseAt_none`.
  * §5 `splitAct` — the activity/phase split: `splitAct_slot`
    (the slot is a pure function of box+scores: phase never changes which
    slot is chosen), `splitAct_perm`, `splitAct_live`,
    `splitAct_covers` (exhaustive at an arbitrary slot, phase permutation
    included), `splitAct_mass_lt` / `splitAct_cost_lt` (strict progress of
    both children), `splitAct_complete`; plus the permuted-coverage bridge
    `covers_pin_or_retire_perm` and `mem_allAssigns_set_perm`.
  * §6 tiny-model demonstration: the selector changes under recorded
    updates (`tinyBox_act_zero` vs `tinyBox_act_updated`), the rescale
    keeps the choice and the bound (`tinyBox_rescale64`,
    `tinyBox_rescale_hit`, `tinyBox_rescale_select`,
    `tinyBox_rescale_bounded`), phase saving reorders only the value order
    (`tinySmallLast_phase_suggest`, `tinySmallLast_split_phase`), the S2
    split covers the parent (`tinySmallLast_branch`) and strictly
    progresses (`tinySmallLast_progress`), reads back at the original slot
    (`tinySmallLast_read`), and equals the S1 split without phase
    (`tinySmallLast_eq_split`).

  Design invariants (PLAN §8 S2):
  * exact/finite scores: `Nat` with the proved bound
    `∀ s ∈ (m.update c).scores, s ≤ 64` (`Meta.Bounded`);
  * no floating point; no `DecidableEq Value` needed (the phase equality
    `valEqB` is a sound `Bool` oracle; `Value.array` is conservatively
    unequal — a missed phase recommendation, never an unsoundness);
  * every choice is legal and the split exhaustive for ARBITRARY metadata
    (all coverage/progress theorems are quantified over `m : Meta`);
    rescaling and ties cannot break progress because they only change
    `m`;
  * activity never drops values: the update layer has no access to
    `Frame`/`Domain`; phase only permutes a selected domain's order.

  Dependencies: LeanFzn.Solver.Propagation.DecisionProto (S0/S1 vocabulary:
  `Frame`, `Live`, `Card`, `selectSlot`, `covers_pin_or_retire`,
  `mem_allAssigns_cons_iff`, `sumMass_set_lt`, `branchCost_set_lt`, ...).
  DAG check: `DecisionProto` imports only `FrontierSemantics` and no module
  imports `DecisionProto` except `SparseFrame`; this module imports only
  `DecisionProto`, so the dependency remains acyclic and this file stays a
  leaf.

  Not wired: this module is a prototype. The runtime A/B (PLAN S2
  acceptance: time-to-first/time-to-proof, decisions/conflicts, ablations
  vs static ordering and S1-only) requires the M2 sparse-frame migration
  and a dispatcher hook that records REAL conflicts
  (`AnalysisEvents`/backjump), as recorded in `S0-decision-design.md` §8.

  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no proof escapes.
-/
import LeanFzn.Legacy.Solver.Propagation.DecisionProto

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation.ActivityProto
open LeanFzn.Solver.Propagation.DecisionProto

/-! ## §1 The S2 activity scan and its specification -/

/-- The S2 scan over the aligned `(scores, box)` pair: among the live slots,
the one maximizing its activity score `σ.getD j 0`; ties are broken by the
S1 minimum-cardinality key `(Card, index)`. Returns the key
`(score, cardinality, slot index)` of the winner. One structural pass: the
recursion consumes one score and one domain per slot. -/
def bestOfAct : List Nat → List Domain → Option (Nat × Nat × Nat)
  | [], _ => none
  | _, [] => none
  | s :: ss, d :: ds =>
      if 2 ≤ d.length then
        match bestOfAct ss ds with
        | none => some (s, d.length, 0)
        | some (s', c', i') =>
            if s < s' then some (s', c', i' + 1)
            else if s' < s then some (s, d.length, 0)
            else if c' < d.length then some (s', c', i' + 1)
            else some (s, d.length, 0)
      else
        (bestOfAct ss ds).map fun p => (p.1, p.2.1, p.2.2 + 1)

/-- Definitional unfolding of `bestOfAct` at a live head (so condition
branches can be rewritten with `if_pos`/`if_neg` instead of reducing the
compiled match). -/
theorem bestOfAct_cons (s : Nat) (ss : List Nat) (d : Domain) (ds : List Domain) :
    bestOfAct (s :: ss) (d :: ds) =
      (if 2 ≤ d.length then
        (match bestOfAct ss ds with
        | none => some (s, d.length, 0)
        | some (s', c', i') =>
            if s < s' then some (s', c', i' + 1)
            else if s' < s then some (s, d.length, 0)
            else if c' < d.length then some (s', c', i' + 1)
            else some (s, d.length, 0))
      else
        (bestOfAct ss ds).map fun p => (p.1, p.2.1, p.2.2 + 1)) := rfl

/-- `Live` one slot into the list. -/
theorem live_cons_succ (d : Domain) (rest : List Domain) (k : Nat) :
    Live (d :: rest) (k + 1) ↔ Live rest k := by
  simp [Live]

/-- `Live` at slot `0` is "the head domain has at least two values". -/
theorem live_zero_iff (d : Domain) (rest : List Domain) :
    Live (d :: rest) 0 ↔ 2 ≤ d.length := by
  rw [live_iff_bigSlot, BigSlot, Card]
  simp

/-- The exact specification of the S2 scan: either no live slot exists, or
the scan returns the `(score, cardinality, index)` key of a live slot that
maximizes the score and, among maximal scores, is S1-minimal for
`(cardinality, index)`. -/
def BestActSpec (σ : List Nat) (ds : List Domain) : Prop :=
  (bestOfAct σ ds = none ∧ ∀ j, ¬ Live ds j) ∨
    ∃ s c i, bestOfAct σ ds = some (s, c, i) ∧ Live ds i ∧ c = Card ds i ∧
      σ.getD i 0 = s ∧
      ∀ j, Live ds j → σ.getD j 0 ≤ s ∧
        (σ.getD j 0 = s → c ≤ Card ds j) ∧
        (σ.getD j 0 = s → Card ds j = c → i ≤ j)

/-- THE S2 SCAN IS CORRECT (PLAN §8 S2 selection rule): the scores are
aligned (`ds.length ≤ σ.length`, supplied by `Meta.WF`), `getD` gives the
total zero-score fallback, and the returned key maximizes activity, then
minimizes `(cardinality, index)` exactly like S1. -/
theorem bestOfAct_spec : ∀ (σ : List Nat) (ds : List Domain),
    ds.length ≤ σ.length → BestActSpec σ ds := by
  intro σ ds
  induction ds generalizing σ with
  | nil =>
      intro _
      left
      exact ⟨by cases σ <;> rfl, fun j => by simp [Live]⟩
  | cons d rest ih =>
      intro hlen
      cases σ with
      | nil => simp at hlen
      | cons s ss =>
          have hlen' : rest.length ≤ ss.length := by simpa using hlen
          have ih' := ih ss hlen'
          by_cases hd : 2 ≤ d.length
          · cases hr : bestOfAct ss rest with
            | none =>
                have hno : ∀ j, ¬ Live rest j := by
                  rcases ih' with ⟨-, hno⟩ | ⟨s', c', i', hs, -⟩
                  · exact hno
                  · rw [hr] at hs; cases hs
                right
                refine ⟨s, d.length, 0, ?_, ?_, ?_, ?_, ?_⟩
                · simp only [bestOfAct_cons, if_pos hd, hr]
                · exact (live_zero_iff d rest).mpr hd
                · simp [Card]
                · simp
                · intro j hj
                  cases j with
                  | zero =>
                      simp only [List.getD_cons_zero, Card]
                      exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩
                  | succ k =>
                      exact absurd ((live_cons_succ d rest k).mp hj) (hno k)
            | some p =>
                obtain ⟨s', c', i'⟩ := p
                have hfacts : Live rest i' ∧ c' = Card rest i' ∧ ss.getD i' 0 = s' ∧
                    ∀ j, Live rest j → ss.getD j 0 ≤ s' ∧
                      (ss.getD j 0 = s' → c' ≤ Card rest j) ∧
                      (ss.getD j 0 = s' → Card rest j = c' → i' ≤ j) := by
                  rcases ih' with ⟨hn, -⟩ | ⟨s'', c'', i'', hs, hl, hc, hsc, hm⟩
                  · rw [hr] at hn; cases hn
                  · rw [hr] at hs
                    simp only [Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs
                    exact ⟨hl, hc, hsc, hm⟩
                obtain ⟨hl', hc', hsc', hm'⟩ := hfacts
                by_cases hlt : s < s'
                · right
                  refine ⟨s', c', i' + 1, ?_, ?_, ?_, ?_, ?_⟩
                  · simp only [bestOfAct_cons, if_pos hd, hr, if_pos hlt]
                  · exact (live_cons_succ d rest i').mpr hl'
                  · simpa [Card] using hc'
                  · simpa using hsc'
                  · intro j hj
                    cases j with
                    | zero =>
                        simp only [List.getD_cons_zero, Card]
                        exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩
                    | succ k =>
                        have hk : Live rest k := (live_cons_succ d rest k).mp hj
                        obtain ⟨hle, hcle, hidx⟩ := hm' k hk
                        refine ⟨by simpa [List.getD_cons_succ] using hle, ?_, ?_⟩
                        · intro heq
                          exact hcle (by simpa [List.getD_cons_succ] using heq)
                        · intro heq hcd
                          have hi : i' ≤ k :=
                            hidx (by simpa [List.getD_cons_succ] using heq)
                              (by simpa [Card] using hcd)
                          omega
                · by_cases hgt : s' < s
                  · right
                    refine ⟨s, d.length, 0, ?_, ?_, ?_, ?_, ?_⟩
                    · simp only [bestOfAct_cons, if_pos hd, hr, if_neg hlt, if_pos hgt]
                    · exact (live_zero_iff d rest).mpr hd
                    · simp [Card]
                    · simp
                    · intro j hj
                      cases j with
                      | zero =>
                          simp only [List.getD_cons_zero, Card]
                          exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩
                      | succ k =>
                          have hk : Live rest k := (live_cons_succ d rest k).mp hj
                          obtain ⟨hle, hcle, hidx⟩ := hm' k hk
                          refine ⟨by simpa [List.getD_cons_succ] using (by omega : ss.getD k 0 ≤ s),
                            ?_, ?_⟩
                          · intro heq
                            have heq' : ss.getD k 0 = s :=
                              by simpa [List.getD_cons_succ] using heq
                            omega
                          · intro heq hcd
                            have heq' : ss.getD k 0 = s :=
                              by simpa [List.getD_cons_succ] using heq
                            omega
                  · by_cases hcLt : c' < d.length
                    · right
                      refine ⟨s', c', i' + 1, ?_, ?_, ?_, ?_, ?_⟩
                      · simp only [bestOfAct_cons, if_pos hd, hr, if_neg hlt, if_neg hgt,
                          if_pos hcLt]
                      · exact (live_cons_succ d rest i').mpr hl'
                      · simpa [Card] using hc'
                      · simpa using hsc'
                      · intro j hj
                        cases j with
                        | zero =>
                            simp only [List.getD_cons_zero, Card]
                            exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩
                        | succ k =>
                            have hk : Live rest k := (live_cons_succ d rest k).mp hj
                            obtain ⟨hle, hcle, hidx⟩ := hm' k hk
                            refine ⟨by simpa [List.getD_cons_succ] using hle, ?_, ?_⟩
                            · intro heq
                              exact hcle (by simpa [List.getD_cons_succ] using heq)
                            · intro heq hcd
                              have hi : i' ≤ k :=
                                hidx (by simpa [List.getD_cons_succ] using heq)
                                  (by simpa [Card] using hcd)
                              omega
                    · right
                      refine ⟨s, d.length, 0, ?_, ?_, ?_, ?_, ?_⟩
                      · simp only [bestOfAct_cons, if_pos hd, hr, if_neg hlt, if_neg hgt,
                          if_neg hcLt]
                      · exact (live_zero_iff d rest).mpr hd
                      · simp [Card]
                      · simp
                      · intro j hj
                        cases j with
                        | zero =>
                            simp only [List.getD_cons_zero, Card]
                            exact ⟨by omega, (fun _ => by omega), (fun _ _ => by omega)⟩
                        | succ k =>
                            have hk : Live rest k := (live_cons_succ d rest k).mp hj
                            obtain ⟨hle, hcle, hidx⟩ := hm' k hk
                            refine ⟨by simpa [List.getD_cons_succ] using (by omega : ss.getD k 0 ≤ s),
                              ?_, ?_⟩
                            · intro heq
                              have heq' : ss.getD k 0 = s :=
                                by simpa [List.getD_cons_succ] using heq
                              have h1 : ss.getD k 0 = s' := by omega
                              have h2 : c' ≤ Card rest k := hcle h1
                              have h3 : d.length ≤ c' := by omega
                              have h4 : Card (d :: rest) (k + 1) = Card rest k := by simp [Card]
                              omega
                            · intro _ _; omega
          · cases hr : bestOfAct ss rest with
            | none =>
                have hno : ∀ j, ¬ Live rest j := by
                  rcases ih' with ⟨-, hno⟩ | ⟨s', c', i', hs, -⟩
                  · exact hno
                  · rw [hr] at hs; cases hs
                left
                refine ⟨?_, ?_⟩
                · simp only [bestOfAct_cons, if_neg hd, hr]
                  rfl
                · intro j hj
                  cases j with
                  | zero => exact absurd ((live_zero_iff d rest).mp hj) hd
                  | succ k => exact hno k ((live_cons_succ d rest k).mp hj)
            | some p =>
                obtain ⟨s', c', i'⟩ := p
                have hfacts : Live rest i' ∧ c' = Card rest i' ∧ ss.getD i' 0 = s' ∧
                    ∀ j, Live rest j → ss.getD j 0 ≤ s' ∧
                      (ss.getD j 0 = s' → c' ≤ Card rest j) ∧
                      (ss.getD j 0 = s' → Card rest j = c' → i' ≤ j) := by
                  rcases ih' with ⟨hn, -⟩ | ⟨s'', c'', i'', hs, hl, hc, hsc, hm⟩
                  · rw [hr] at hn; cases hn
                  · rw [hr] at hs
                    simp only [Option.some.injEq, Prod.mk.injEq] at hs
                    obtain ⟨rfl, rfl, rfl⟩ := hs
                    exact ⟨hl, hc, hsc, hm⟩
                obtain ⟨hl', hc', hsc', hm'⟩ := hfacts
                right
                refine ⟨s', c', i' + 1, ?_, ?_, ?_, ?_, ?_⟩
                · simp only [bestOfAct_cons, if_neg hd, hr, Option.map_some]
                · exact (live_cons_succ d rest i').mpr hl'
                · simpa [Card] using hc'
                · simpa using hsc'
                · intro j hj
                  cases j with
                  | zero => exact absurd ((live_zero_iff d rest).mp hj) hd
                  | succ k =>
                      have hk : Live rest k := (live_cons_succ d rest k).mp hj
                      obtain ⟨hle, hcle, hidx⟩ := hm' k hk
                      refine ⟨by simpa [List.getD_cons_succ] using hle, ?_, ?_⟩
                      · intro heq
                        exact hcle (by simpa [List.getD_cons_succ] using heq)
                      · intro heq hcd
                        have hi : i' ≤ k :=
                          hidx (by simpa [List.getD_cons_succ] using heq)
                            (by simpa [Card] using hcd)
                        omega

/-- Positive extraction from `bestOfAct_spec`. -/
theorem bestOfAct_some_spec {σ : List Nat} {ds : List Domain} {s c i : Nat}
    (hlen : ds.length ≤ σ.length) (h : bestOfAct σ ds = some (s, c, i)) :
    Live ds i ∧ c = Card ds i ∧ σ.getD i 0 = s ∧
      ∀ j, Live ds j → σ.getD j 0 ≤ s ∧
        (σ.getD j 0 = s → c ≤ Card ds j) ∧
        (σ.getD j 0 = s → Card ds j = c → i ≤ j) := by
  rcases bestOfAct_spec σ ds hlen with ⟨hn, -⟩ | ⟨s', c', i', hs, hl, hc, hsc, hm⟩
  · rw [h] at hn; cases hn
  · rw [h] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨hl, hc, hsc, hm⟩

/-- Negative extraction from `bestOfAct_spec`. -/
theorem bestOfAct_none_spec {σ : List Nat} {ds : List Domain}
    (hlen : ds.length ≤ σ.length) (h : bestOfAct σ ds = none) :
    ∀ j, ¬ Live ds j := by
  rcases bestOfAct_spec σ ds hlen with ⟨-, hno⟩ | ⟨s', c', i', hs, -⟩
  · exact hno
  · rw [h] at hs; cases hs

/-- EVERY returned candidate is live, with NO alignment hypothesis: the
scan only ever records candidates at domains with two or more values, so a
successful scan never returns a singleton or dead slot. -/
theorem bestOfAct_some_live : ∀ (σ : List Nat) (ds : List Domain) (s c i : Nat),
    bestOfAct σ ds = some (s, c, i) → Live ds i := by
  intro σ ds
  induction ds generalizing σ with
  | nil => intro s c i h; cases σ <;> simp [bestOfAct] at h
  | cons d rest ih =>
      intro s c i h
      cases σ with
      | nil => simp [bestOfAct] at h
      | cons s0 ss =>
          rw [bestOfAct_cons] at h
          by_cases hd : 2 ≤ d.length
          · rw [if_pos hd] at h
            cases hr : bestOfAct ss rest with
            | none =>
                simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, -, rfl⟩ := h
                exact (live_zero_iff d rest).mpr hd
            | some p =>
                obtain ⟨s', c', i'⟩ := p
                rw [hr] at h
                by_cases hlt : s0 < s'
                · simp only [if_pos hlt, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, -, rfl⟩ := h
                  exact (live_cons_succ d rest i').mpr (ih ss s' c' i' hr)
                · by_cases hgt : s' < s0
                  · simp only [if_neg hlt, if_pos hgt, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, -, rfl⟩ := h
                    exact (live_zero_iff d rest).mpr hd
                  · by_cases hcLt : c' < d.length
                    · simp only [if_neg hlt, if_neg hgt, if_pos hcLt,
                        Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨-, -, rfl⟩ := h
                      exact (live_cons_succ d rest i').mpr (ih ss s' c' i' hr)
                    · simp only [if_neg hlt, if_neg hgt, if_neg hcLt,
                        Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨-, -, rfl⟩ := h
                      exact (live_zero_iff d rest).mpr hd
          · rw [if_neg hd] at h
            cases hr : bestOfAct ss rest with
            | none => simp [hr] at h
            | some p =>
                obtain ⟨s', c', i'⟩ := p
                rw [hr] at h
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, -, rfl⟩ := h
                exact (live_cons_succ d rest i').mpr (ih ss s' c' i' hr)

/-! ## §2 The S2 selection rule -/

/-- THE S2 POLICY HOOK: among the live slots, maximize the activity score
`σ.getD j 0`; ties are broken by the S1 minimum-cardinality rule
(`Card`, then slot index). Absent or misaligned scores read as `0` through
`getD`, so the S1 rule is the total legal fallback. A pure function of
(box, scores): the phase metadata is not consulted. -/
def selectSlotAct (ds : List Domain) (σ : List Nat) : Option Nat :=
  (bestOfAct σ ds).map fun p => p.2.2

/-- The S2 key comparison at slot `k` against slot `j`: `k` wins when its
score is at least `j`'s; among equal scores its cardinality is at most
`j`'s; among full ties its index is at most `j`'s. -/
def KeyActLE (σ : List Nat) (ds : List Domain) (k j : Nat) : Prop :=
  σ.getD j 0 ≤ σ.getD k 0 ∧
  (σ.getD j 0 = σ.getD k 0 → Card ds k ≤ Card ds j) ∧
  (σ.getD j 0 = σ.getD k 0 → Card ds j = Card ds k → k ≤ j)

/-- The key order is antisymmetric: two mutual winners are the same slot. -/
theorem KeyActLE_antisymm {σ : List Nat} {ds : List Domain} {k j : Nat}
    (hkj : KeyActLE σ ds k j) (hjk : KeyActLE σ ds j k) : k = j := by
  obtain ⟨h1, h2, h3⟩ := hkj
  obtain ⟨h4, h5, h6⟩ := hjk
  have hs : σ.getD k 0 = σ.getD j 0 := by omega
  have hc : Card ds k = Card ds j := by
    have ha := h2 hs.symm
    have hb := h5 hs
    omega
  have hk : k ≤ j := h3 hs.symm hc.symm
  have hj : j ≤ k := h6 hs hc
  omega

/-- LEGALITY: every selected slot is live (a legal decision exists there),
with no alignment hypothesis: misaligned metadata can only lose candidates,
never fabricate one. -/
theorem selectSlotAct_live {ds : List Domain} {σ : List Nat} {k : Nat}
    (h : selectSlotAct ds σ = some k) : Live ds k := by
  rw [selectSlotAct] at h
  cases hb : bestOfAct σ ds with
  | none => simp [hb] at h
  | some p =>
      obtain ⟨s, c, i⟩ := p
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact h ▸ bestOfAct_some_live σ ds s c i hb

/-- THE S2 RULE, precisely: the selected slot is live, maximizes the score
among live slots, and among equal scores is S1-minimal for
`(cardinality, index)`. This is the frozen selection specification. -/
theorem selectSlotAct_min {ds : List Domain} {σ : List Nat} {k : Nat}
    (hlen : ds.length ≤ σ.length) (h : selectSlotAct ds σ = some k) :
    Live ds k ∧ ∀ j, Live ds j → KeyActLE σ ds k j := by
  rw [selectSlotAct] at h
  cases hb : bestOfAct σ ds with
  | none => simp [hb] at h
  | some p =>
      obtain ⟨s, c, i⟩ := p
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hspec := bestOfAct_some_spec hlen hb
      subst h
      refine ⟨hspec.1, ?_⟩
      intro j hj
      obtain ⟨hsc, hcard, hidx⟩ := hspec.2.2.2 j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hspec.2.2.1]
        exact hsc
      · intro heq
        simpa [← hspec.2.1] using hcard (heq.trans hspec.2.2.1)
      · intro heq hcd
        exact hidx (heq.trans hspec.2.2.1) (hcd.trans hspec.2.1.symm)

/-- COMPLETENESS: a live slot always admits a selection (with aligned
metadata the scan cannot skip it). -/
theorem selectSlotAct_complete {ds : List Domain} {σ : List Nat}
    (hlen : ds.length ≤ σ.length) (hl : ∃ k, Live ds k) :
    ∃ k, selectSlotAct ds σ = some k := by
  cases hb : bestOfAct σ ds with
  | none =>
      obtain ⟨k, hk⟩ := hl
      exact absurd hk (bestOfAct_none_spec hlen hb k)
  | some p =>
      exact ⟨p.2.2, by rw [selectSlotAct, hb]; rfl⟩

/-- No live slot means selection is exhausted: the negative half of the S2
selection specification. -/
theorem selectSlotAct_none_iff {ds : List Domain} {σ : List Nat}
    (hlen : ds.length ≤ σ.length) :
    selectSlotAct ds σ = none ↔ ¬ ∃ k, Live ds k := by
  constructor
  · intro h hlive
    obtain ⟨k, hk⟩ := selectSlotAct_complete hlen hlive
    rw [h] at hk
    cases hk
  · intro h
    cases hb : bestOfAct σ ds with
    | none => rw [selectSlotAct, hb]; rfl
    | some p =>
        exact absurd ⟨p.2.2, (bestOfAct_some_spec hlen hb).1⟩ h

/-- DETERMINISM / UNIQUENESS UNDER THE TIE RULE: any live slot that is
minimal for the S2 key is exactly the selected one. The tie rule therefore
determines the choice, and the selector — a pure function of (box, scores)
— admits no second answer. -/
theorem selectSlotAct_eq_of_min {ds : List Domain} {σ : List Nat} {k : Nat}
    (hlen : ds.length ≤ σ.length) (hk : Live ds k)
    (hmin : ∀ j, Live ds j → KeyActLE σ ds k j) :
    selectSlotAct ds σ = some k := by
  obtain ⟨i, hi⟩ := selectSlotAct_complete hlen ⟨k, hk⟩
  have hik : KeyActLE σ ds i k := (selectSlotAct_min hlen hi).2 k hk
  have hki : KeyActLE σ ds k i := hmin i (selectSlotAct_live hi)
  have heq : i = k := KeyActLE_antisymm hik hki
  rw [← heq]
  exact hi

/-- Two live slots satisfying the S2 tie rule are equal. -/
theorem selectSlotAct_unique_min {ds : List Domain} {σ : List Nat} {k k' : Nat}
    (hlen : ds.length ≤ σ.length) (hk : Live ds k) (hk' : Live ds k')
    (hmink : ∀ j, Live ds j → KeyActLE σ ds k j)
    (hmink' : ∀ j, Live ds j → KeyActLE σ ds k' j) :
    k = k' := by
  have h1 := selectSlotAct_eq_of_min hlen hk hmink
  have h2 := selectSlotAct_eq_of_min hlen hk' hmink'
  rw [h1] at h2
  exact Option.some.inj h2

/-- S1 FALLBACK (ties): when every live slot carries the SAME score, the S2
rule is exactly the S1 minimum-cardinality rule (so activity that ties
cannot perturb the S1 choice). -/
theorem selectSlotAct_const {ds : List Domain} {σ : List Nat} {c : Nat}
    (hlen : ds.length ≤ σ.length) (hc : ∀ j, Live ds j → σ.getD j 0 = c) :
    selectSlotAct ds σ = selectSlot ds := by
  cases hsel : selectSlot ds with
  | none =>
      have hl : ¬ ∃ k, Live ds k := selectSlot_none_iff.mp hsel
      exact (selectSlotAct_none_iff hlen).mpr hl
  | some k =>
      have hsl := selectSlot_min hsel
      have hmin : ∀ j, Live ds j → KeyActLE σ ds k j := by
        intro j hj
        have h1 : σ.getD j 0 = c := hc j hj
        have h2 : σ.getD k 0 = c := hc k hsl.1
        rcases hsl.2 j hj with hlt | ⟨heq, hidx⟩
        · refine ⟨by omega, ?_, ?_⟩
          · intro _; omega
          · intro _ _; omega
        · refine ⟨by omega, ?_, ?_⟩
          · intro _; omega
          · intro _ _; omega
      rw [selectSlotAct_eq_of_min hlen hsl.1 hmin]

/-- ABSENT SCORES: with all-zero metadata (no recorded conflict), S2 IS S1.
This is the executable fallback the S2 rule inherits from S1. -/
theorem selectSlotAct_zero {ds : List Domain} {σ : List Nat}
    (hlen : ds.length ≤ σ.length) (hzero : ∀ j, σ.getD j 0 = 0) :
    selectSlotAct ds σ = selectSlot ds :=
  selectSlotAct_const hlen fun j _ => hzero j

/-! ## §3 Activity metadata: recording, decay/rescale, and the proved bound

The metadata is a separate structure threaded alongside the frame; the
update functions take `Meta` and a `Conflict` record only — they have no
access to `Frame`, `Domain` or `Value` (activity cannot drop values). All
scores are exact `Nat`s; the decay is the exact halving of `step`, and the
policy keeps every score at most `RESCALE_BOUND` (`Meta.Bounded`). -/

/-- Per-slot heuristic metadata, aligned with the box: activity scores and
optional saved phases (last decided value per slot). This is NOT part of
the semantic state; nothing in `Frame` mentions it. -/
structure Meta where
  /-- Per-slot conflict activity (exact `Nat` scores, never floats). -/
  scores : List Nat
  /-- Optional phase saving: the last suggested value per slot. -/
  phase : List (Option Value)

/-- Metadata validity: the score and phase lists are aligned with the box.
`Meta.WF m ds` is the hypothesis every selector specification consumes. -/
def Meta.WF (m : Meta) (ds : List Domain) : Prop :=
  m.scores.length = ds.length ∧ m.phase.length = ds.length

/-- The activity score at a slot (`0` when absent: the total fallback). -/
def Meta.scoreAt (m : Meta) (j : Nat) : Nat := m.scores.getD j 0

/-- The saved phase at a slot (`none` when absent). -/
def Meta.phaseAt (m : Meta) (j : Nat) : Option Value := m.phase.getD j none

/-- A recorded conflict: the slots that participated. The activity layer
reads nothing else from a conflict. -/
structure Conflict where
  /-- The conflict's participating slots (a list; duplicates bump twice). -/
  slots : List Nat

/-! ### The unit bump -/

/-- Bump the score at slot `k` by one; identity out of range. The ONLY
operation that turns a recorded conflict into activity. -/
def bumpAt : List Nat → Nat → List Nat
  | [], _ => []
  | s :: ss, 0 => (s + 1) :: ss
  | s :: ss, k + 1 => s :: bumpAt ss k

theorem bumpAt_length (l : List Nat) (k : Nat) : (bumpAt l k).length = l.length := by
  induction l generalizing k with
  | nil => simp [bumpAt]
  | cons s ss ih =>
      cases k with
      | zero => simp [bumpAt]
      | succ k => simp [bumpAt, ih]

/-- A bump changes exactly one slot. -/
theorem bumpAt_scoreAt_of_ne : ∀ (l : List Nat) (k j : Nat), j ≠ k →
    (bumpAt l k).getD j 0 = l.getD j 0 := by
  intro l
  induction l with
  | nil => intro k j _; simp [bumpAt]
  | cons s ss ih =>
      intro k j h
      cases k with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j => simp [bumpAt]
      | succ k =>
          cases j with
          | zero => simp [bumpAt]
          | succ j =>
              simp only [bumpAt, List.getD_cons_succ]
              exact ih k j (by omega)

/-- A bump never lowers a score (at the bumped slot it raises it by one). -/
theorem bumpAt_mono : ∀ (l : List Nat) (k j : Nat),
    l.getD j 0 ≤ (bumpAt l k).getD j 0 := by
  intro l
  induction l with
  | nil => intro k j; simp [bumpAt]
  | cons s ss ih =>
      intro k j
      cases k with
      | zero =>
          cases j with
          | zero => simp [bumpAt]
          | succ j => simp [bumpAt]
      | succ k =>
          cases j with
          | zero => simp [bumpAt]
          | succ j =>
              simp only [bumpAt, List.getD_cons_succ]
              exact ih k j

/-- Exactness of one bump: the score at any slot either stays or grows by
exactly one (the bumped slot). -/
theorem bumpAt_scoreAt_eq_or_succ : ∀ (l : List Nat) (k j : Nat),
    (bumpAt l k).getD j 0 = l.getD j 0 ∨
      (bumpAt l k).getD j 0 = l.getD j 0 + 1 := by
  intro l
  induction l with
  | nil => intro k j; left; simp [bumpAt]
  | cons s ss ih =>
      intro k j
      cases k with
      | zero =>
          cases j with
          | zero => right; simp [bumpAt]
          | succ j => left; simp [bumpAt]
      | succ k =>
          cases j with
          | zero => left; simp [bumpAt]
          | succ j =>
              simp only [bumpAt, List.getD_cons_succ]
              exact ih k j

/-- The boundedness transfer of one bump: `≤ B` becomes `≤ B + 1`. -/
theorem bumpAt_bound : ∀ (l : List Nat) (k B : Nat), (∀ s ∈ l, s ≤ B) →
    ∀ s ∈ bumpAt l k, s ≤ B + 1 := by
  intro l
  induction l with
  | nil => intro k B _ s hs; simp [bumpAt] at hs
  | cons x xs ih =>
      intro k B h s hs
      have hx : x ≤ B + 1 := by
        have := h x (List.mem_cons_self ..)
        omega
      cases k with
      | zero =>
          simp only [bumpAt] at hs
          have hx' : x ≤ B := h x (List.mem_cons_self ..)
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa using hx'
          · have := h s (List.mem_cons_of_mem _ hs); omega
      | succ k =>
          simp only [bumpAt] at hs
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa using hx
          · exact ih k B (fun t ht => h t (List.mem_cons_of_mem _ ht)) s hs

/-! ### The maximum of the score list (for the rescale test) -/

/-- The maximum score of a list (`0` for the empty list). -/
def maxOf : List Nat → Nat
  | [] => 0
  | s :: ss => Nat.max s (maxOf ss)

/-- Every member is at most the maximum. -/
theorem le_maxOf {s : Nat} {l : List Nat} (h : s ∈ l) : s ≤ maxOf l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      rw [maxOf]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

/-- The maximum respects a uniform bound. -/
theorem maxOf_le {l : List Nat} {B : Nat} (h : ∀ s ∈ l, s ≤ B) :
    maxOf l ≤ B := by
  induction l with
  | nil => simp [maxOf]
  | cons x xs ih =>
      rw [maxOf]
      exact Nat.max_le.mpr ⟨h x (List.mem_cons_self ..), ih fun s hs =>
        h s (List.mem_cons_of_mem _ hs)⟩

/-! ### The decay: exact halving with a proved finiteness bound -/

/-- The rescale bound: after every update the scores stay at most `64`. -/
def RESCALE_BOUND : Nat := 64

/-- One slot's policy step: bump the recorded slot; if the bound is
exceeded, halve all scores EXACTLY (integer division by two — no floats).
The only two possibilities are "exact unit bump" and "exact halving"
(`step_bump_or_halve`). -/
def step (l : List Nat) (k : Nat) : List Nat :=
  if maxOf (bumpAt l k) ≤ RESCALE_BOUND then bumpAt l k
  else (bumpAt l k).map (fun s => s / 2)

/-- The exact-step dichotomy: an update step is either the unit bump of the
recorded slot or the exact halving of every score. -/
theorem step_bump_or_halve (l : List Nat) (k : Nat) :
    step l k = bumpAt l k ∨ step l k = (bumpAt l k).map (fun s => s / 2) := by
  rw [step]
  by_cases h : maxOf (bumpAt l k) ≤ RESCALE_BOUND
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- `step` preserves the score-list length. -/
theorem step_length (l : List Nat) (k : Nat) : (step l k).length = l.length := by
  rcases step_bump_or_halve l k with h | h <;> rw [h]
  · exact bumpAt_length l k
  · rw [List.length_map, bumpAt_length]

/-- THE PROVED RESCALE BOUND (single step): from `≤ 64` the step keeps every
score `≤ 64` — the bump can only reach `65`, which triggers the halving
(`65 / 2 = 32`). -/
theorem step_bounded {l : List Nat} {k : Nat}
    (h : ∀ s ∈ l, s ≤ RESCALE_BOUND) :
    ∀ s ∈ step l k, s ≤ RESCALE_BOUND := by
  have hb : ∀ s ∈ bumpAt l k, s ≤ RESCALE_BOUND + 1 :=
    bumpAt_bound l k RESCALE_BOUND h
  rw [step]
  by_cases ht : maxOf (bumpAt l k) ≤ RESCALE_BOUND
  · rw [if_pos ht]
    intro s hs
    exact Nat.le_trans (le_maxOf hs) ht
  · rw [if_neg ht]
    intro s hs
    rcases List.mem_map.mp hs with ⟨t, ht', rfl⟩
    have h1 : t ≤ RESCALE_BOUND + 1 := hb t ht'
    have h2 : t / 2 ≤ (RESCALE_BOUND + 1) / 2 := Nat.div_le_div_right h1
    have h3 : (RESCALE_BOUND + 1) / 2 = 32 := by decide
    omega

/-! ### Folded bulk operations (conflict records) -/

/-- Pure conflict recording: bump every listed slot. -/
def Meta.bump (m : Meta) (c : Conflict) : Meta :=
  { m with scores := c.slots.foldl (fun l k => bumpAt l k) m.scores }

/-- The deterministic bounded policy update: fold `step` over the recorded
slots. Every step is a unit bump on a recorded slot or an exact halving. -/
def Meta.update (m : Meta) (c : Conflict) : Meta :=
  { m with scores := c.slots.foldl (fun l k => step l k) m.scores }

/-- No recorded conflict, no change. -/
theorem Meta.bump_empty (m : Meta) : m.bump ⟨[]⟩ = m := rfl

/-- No recorded conflict, no change (the fold runs zero steps). -/
theorem Meta.update_empty (m : Meta) : m.update ⟨[]⟩ = m := rfl

/-- The recording depends only on the recorded slots. -/
theorem Meta.bump_ext {m : Meta} {c₁ c₂ : Conflict}
    (h : c₁.slots = c₂.slots) : m.bump c₁ = m.bump c₂ := by
  cases c₁
  cases c₂
  simp only at h
  subst h
  rfl

/-- The update depends only on the recorded slots. -/
theorem Meta.update_ext {m : Meta} {c₁ c₂ : Conflict}
    (h : c₁.slots = c₂.slots) : m.update c₁ = m.update c₂ := by
  cases c₁
  cases c₂
  simp only at h
  subst h
  rfl

/-- Folding bumps preserves the score-list length. -/
theorem foldl_bumpAt_length : ∀ (ks l : List Nat),
    (ks.foldl (fun l k => bumpAt l k) l).length = l.length := by
  intro ks
  induction ks with
  | nil => intro l; rfl
  | cons k ks ih =>
      intro l
      simp only [List.foldl_cons]
      rw [ih (bumpAt l k), bumpAt_length]

/-- Folding steps preserves the score-list length. -/
theorem foldl_step_length : ∀ (ks l : List Nat),
    (ks.foldl (fun l k => step l k) l).length = l.length := by
  intro ks
  induction ks with
  | nil => intro l; rfl
  | cons k ks ih =>
      intro l
      simp only [List.foldl_cons]
      rw [ih (step l k), step_length]

/-- Folding bumps never lowers a score. -/
theorem foldl_bumpAt_mono : ∀ (ks l : List Nat) (j : Nat),
    l.getD j 0 ≤ (ks.foldl (fun l k => bumpAt l k) l).getD j 0 := by
  intro ks
  induction ks with
  | nil => intro l j; simp
  | cons k ks ih =>
      intro l j
      simp only [List.foldl_cons]
      exact Nat.le_trans (bumpAt_mono l k j) (ih (bumpAt l k) j)

/-- ACTIVITY IS READ ONLY FROM RECORDED CONFLICTS: a slot that does not
occur in the record is not touched by the recording fold. -/
theorem foldl_bumpAt_scoreAt_of_not_mem : ∀ (ks l : List Nat) (j : Nat),
    j ∉ ks → (ks.foldl (fun l k => bumpAt l k) l).getD j 0 = l.getD j 0 := by
  intro ks
  induction ks with
  | nil => intro l j _; simp
  | cons k ks ih =>
      intro l j h
      have hjk : j ≠ k := fun heq => h (heq ▸ List.mem_cons_self ..)
      have hks : j ∉ ks := fun hmem => h (List.mem_cons_of_mem _ hmem)
      simp only [List.foldl_cons]
      rw [ih (bumpAt l k) j hks, bumpAt_scoreAt_of_ne l k j hjk]

/-- Folding steps preserves the bound. -/
theorem foldl_step_bounded : ∀ (ks l : List Nat),
    (∀ s ∈ l, s ≤ RESCALE_BOUND) →
      ∀ s ∈ ks.foldl (fun l k => step l k) l, s ≤ RESCALE_BOUND := by
  intro ks
  induction ks with
  | nil => intro l h; exact h
  | cons k ks ih =>
      intro l h
      simp only [List.foldl_cons]
      exact ih (step l k) (step_bounded h)

/-- Activity never decreases under recording. -/
theorem Meta.bump_mono (m : Meta) (c : Conflict) (j : Nat) :
    m.scoreAt j ≤ (m.bump c).scoreAt j :=
  foldl_bumpAt_mono c.slots m.scores j

/-- ACTIVITY IS READ ONLY FROM RECORDED CONFLICTS: an unrecorded slot keeps
its score under `bump`. This is the executable meaning of "updated from
actual conflicts" at the metadata layer. -/
theorem Meta.bump_scoreAt_of_not_mem {m : Meta} {c : Conflict} {j : Nat}
    (h : j ∉ c.slots) : (m.bump c).scoreAt j = m.scoreAt j :=
  foldl_bumpAt_scoreAt_of_not_mem c.slots m.scores j h

/-- `bump` preserves metadata validity. -/
theorem Meta.WF.bump {m : Meta} {ds : List Domain} (h : m.WF ds) (c : Conflict) :
    (m.bump c).WF ds := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  show (c.slots.foldl (fun l k => bumpAt l k) m.scores).length = ds.length
  rw [foldl_bumpAt_length, h1]

/-- `update` preserves metadata validity. -/
theorem Meta.WF.update {m : Meta} {ds : List Domain} (h : m.WF ds)
    (c : Conflict) : (m.update c).WF ds := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  show (c.slots.foldl (fun l k => step l k) m.scores).length = ds.length
  rw [foldl_step_length, h1]

/-- Metadata validity gives the aligned-score hypothesis of the selectors. -/
theorem Meta.WF.scores_length_le {m : Meta} {ds : List Domain} (h : m.WF ds) :
    ds.length ≤ m.scores.length :=
  Nat.le_of_eq h.1.symm

/-- The metadata invariant the policy maintains: every score is at most the
rescale bound. -/
def Meta.Bounded (m : Meta) : Prop := ∀ s ∈ m.scores, s ≤ RESCALE_BOUND

/-- THE PROVED FINITENESS BOUND of the update policy: starting from a
bounded metadata, every update keeps all scores `≤ 64`. Together with
`step_bump_or_halve` this is the exact/finite score guarantee (no floats,
no overflow: `Nat` is unbounded and the policy keeps it inside `64`). -/
theorem Meta.Bounded.update {m : Meta} (h : m.Bounded) (c : Conflict) :
    (m.update c).Bounded :=
  foldl_step_bounded c.slots m.scores h

/-! ## §4 Optional phase saving (a value-order tie-break)

The phase metadata stores the last suggested value per slot; the split
consults it only to reorder the SELECTED slot's domain so that the saved
value is tried first (`moveToFront`). This is a purely permutational
operation: `moveToFront_perm` proves it never changes the value set, so
exhaustiveness/progress transfer (`§5`). Value comparison uses the sound
boolean oracle `valEqB` (not `DecidableEq`, which does not exist in this
import cone); `Value.array` is conservatively "unequal", which can only
make the optional recommendation miss, never unsound. -/

/-- A sound boolean equality on values: `true` implies equality. The
`array` constructor is conservatively unequal (phase saving is optional;
missing is not unsoundness). This is a total `Bool` oracle, no floats, no
`DecidableEq Value` (absent in the propagation cone). -/
def valEqB : Value → Value → Bool
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .setOfInt a, .setOfInt b => decide (a = b)
  | _, _ => false

/-- SOUNDNESS of the phase equality oracle. -/
theorem valEqB_sound {v w : Value} (h : valEqB v w = true) : v = w := by
  cases v <;> cases w <;> simp_all [valEqB]

/-- Does the VALUE LIST contain (a `valEqB`-match of) the value `w`? -/
def hasValB (w : Value) : List Value → Bool
  | [] => false
  | x :: xs => valEqB x w || hasValB w xs

theorem hasValB_eq_true_iff {w : Value} : ∀ d : List Value,
    hasValB w d = true ↔ ∃ x ∈ d, valEqB x w = true := by
  intro d
  induction d with
  | nil => simp [hasValB]
  | cons x xs ih =>
      rw [hasValB, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨y, hy, hx⟩)
        · exact ⟨x, List.mem_cons_self .., h⟩
        · exact ⟨y, List.mem_cons_of_mem _ hy, hx⟩
      · rintro ⟨y, hy, hx⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl hx
        · exact Or.inr ⟨y, hy, hx⟩

/-- The false direction of `hasValB`, in elimination form. -/
theorem hasValB_false {w : Value} {d : List Value} (h : hasValB w d = false) :
    ∀ x ∈ d, valEqB x w = false := by
  intro x hx
  cases hv : valEqB x w with
  | false => rfl
  | true =>
      have htrue : hasValB w d = true := (hasValB_eq_true_iff d).mpr ⟨x, hx, hv⟩
      rw [h] at htrue
      exact Bool.noConfusion htrue

/-- Delete the first `valEqB`-match of `w` from a value list; identity
when absent. -/
def eraseVal (w : Value) : List Value → List Value
  | [] => []
  | x :: xs => if valEqB x w then xs else x :: eraseVal w xs

/-- With no occurrence, the deletion is the identity. -/
theorem eraseVal_eq_self_of_not {w : Value} {d : List Value}
    (h : hasValB w d = false) : eraseVal w d = d := by
  induction d with
  | nil => rfl
  | cons x xs ih =>
      have hx : valEqB x w = false := hasValB_false h x (List.mem_cons_self ..)
      have hxs : hasValB w xs = false := by
        rw [hasValB, Bool.or_eq_false_iff] at h
        exact h.2
      simp only [eraseVal, hx, Bool.false_eq_true, if_false, ih hxs]

/-- PERMUTATION FACT: prepending `w` to the deletion of a present `w`
permutes the value list (in particular it is nonempty). -/
theorem cons_eraseVal_perm {w : Value} : ∀ {d : List Value},
    hasValB w d = true → (w :: eraseVal w d).Perm d := by
  intro d
  induction d with
  | nil => intro h; simp [hasValB] at h
  | cons x xs ih =>
      intro h
      by_cases hx : valEqB x w = true
      · have hxx : x = w := valEqB_sound hx
        subst hxx
        simp only [eraseVal, hx, if_pos]
        exact List.Perm.refl _
      · have hxs : hasValB w xs = true := by
          rw [hasValB, Bool.or_eq_true] at h
          rcases h with h | h
          · exact absurd h hx
          · exact h
        simp only [eraseVal, hx, Bool.false_eq_true, if_false]
        exact List.Perm.trans (List.Perm.swap x w (eraseVal w xs))
          (List.Perm.cons x (ih hxs))

/-- Move the first `valEqB`-match of `w` to the front of a value list; the
identity when absent. The phase tie-break's only operation. -/
def moveToFront (w : Value) (d : List Value) : List Value :=
  if hasValB w d then w :: eraseVal w d else d

/-- `moveToFront` is a permutation: the value set is unchanged, so no value
is ever dropped by phase saving. -/
theorem moveToFront_perm (w : Value) (d : List Value) : (moveToFront w d).Perm d := by
  rw [moveToFront]
  by_cases h : hasValB w d = true
  · rw [if_pos h]
    exact cons_eraseVal_perm h
  · rw [if_neg h]

/-- `moveToFront` preserves nonemptiness (the split always has a head). -/
theorem moveToFront_ne_nil {w : Value} {d : List Value} (hd : d ≠ []) :
    moveToFront w d ≠ [] := by
  cases d with
  | nil => exact absurd rfl hd
  | cons x xs =>
      rw [moveToFront]
      by_cases h : hasValB w (x :: xs) = true
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp

/-- Without the saved value the list is untouched. -/
theorem moveToFront_eq_self_of_not {w : Value} {d : List Value}
    (h : hasValB w d = false) : moveToFront w d = d := by
  rw [moveToFront]
  rw [if_neg (by simpa using h)]

/-- Overwrite the phase slot `k` (identity out of range). -/
def setAt : List (Option Value) → Nat → Option Value → List (Option Value)
  | [], _, _ => []
  | _ :: xs, 0, x => x :: xs
  | y :: xs, k + 1, x => y :: setAt xs k x

theorem setAt_length : ∀ (l : List (Option Value)) (k : Nat) (x : Option Value),
    (setAt l k x).length = l.length := by
  intro l
  induction l with
  | nil => intro k x; simp [setAt]
  | cons y ys ih =>
      intro k x
      cases k with
      | zero => simp [setAt]
      | succ k => simp [setAt, ih]

theorem setAt_getD_self : ∀ (l : List (Option Value)) (k : Nat) (x : Option Value),
    k < l.length → (setAt l k x).getD k none = x := by
  intro l
  induction l with
  | nil => intro k x h; simp at h
  | cons y ys ih =>
      intro k x h
      cases k with
      | zero => simp [setAt]
      | succ k =>
          simp only [setAt, List.getD_cons_succ]
          exact ih k x (by simpa using h)

theorem setAt_getD_of_ne : ∀ (l : List (Option Value)) (k : Nat) (x : Option Value)
    (j : Nat), j ≠ k → (setAt l k x).getD j none = l.getD j none := by
  intro l
  induction l with
  | nil => intro k x j _; simp [setAt]
  | cons y ys ih =>
      intro k x j h
      cases k with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j => simp [setAt]
      | succ k =>
          cases j with
          | zero => simp [setAt]
          | succ j =>
              simp only [setAt, List.getD_cons_succ]
              exact ih k x j (by omega)

/-- Save `v` as the phase of slot `k` (scores untouched). -/
def Meta.savePhase (m : Meta) (k : Nat) (v : Value) : Meta :=
  { m with phase := setAt m.phase k (some v) }

/-- Phase saving preserves metadata validity. -/
theorem Meta.WF.savePhase {m : Meta} {ds : List Domain} (h : m.WF ds)
    (k : Nat) (v : Value) : (m.savePhase k v).WF ds := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  show (setAt m.phase k (some v)).length = ds.length
  rw [setAt_length, h2]

/-- Phase saving never changes activity: the two metadata components are
independent. -/
theorem Meta.savePhase_scoreAt (m : Meta) (k : Nat) (v : Value) (j : Nat) :
    (m.savePhase k v).scoreAt j = m.scoreAt j := rfl

/-- The saved phase is read back at its slot. -/
theorem Meta.savePhase_phaseAt_self {m : Meta} {k : Nat} {v : Value}
    (h : k < m.phase.length) : (m.savePhase k v).phaseAt k = some v := by
  show (setAt m.phase k (some v)).getD k none = some v
  exact setAt_getD_self m.phase k (some v) h

/-- Saving one slot's phase leaves the other slots' phases alone. -/
theorem Meta.savePhase_phaseAt_of_ne {m : Meta} {k j : Nat} {v : Value}
    (h : j ≠ k) : (m.savePhase k v).phaseAt j = m.phaseAt j := by
  show (setAt m.phase k (some v)).getD j none = m.phase.getD j none
  exact setAt_getD_of_ne m.phase k (some v) j h

/-- The phase suggestion for slot `k`'s domain: the enumeration with the
saved value first when present, else the enumeration unchanged. -/
def Meta.suggest (m : Meta) (k : Nat) (d : Domain) : List Value :=
  match m.phaseAt k with
  | some w => moveToFront w d.enum
  | none => d.enum

/-- The suggestion is a permutation of the domain enumeration: the phase
tie-break only reorders values. -/
theorem Meta.suggest_perm (m : Meta) (k : Nat) (d : Domain) :
    (m.suggest k d).Perm d.enum := by
  rw [Meta.suggest]
  split
  · exact moveToFront_perm _ _
  · exact List.Perm.refl _

/-- The suggestion preserves nonemptiness. -/
theorem Meta.suggest_ne_nil {m : Meta} {k : Nat} {d : Domain} (hd : d.enum ≠ []) :
    m.suggest k d ≠ [] := by
  rw [Meta.suggest]
  split
  · exact moveToFront_ne_nil hd
  · exact hd

/-- Without a saved phase the enumeration is untouched (phase is optional). -/
theorem Meta.suggest_of_phaseAt_none {m : Meta} {k : Nat} {d : Domain}
    (h : m.phaseAt k = none) : m.suggest k d = d.enum := by
  rw [Meta.suggest, h]

/-! ## §5 The activity/phase split: legality, exhaustiveness, progress -/

/-- Permuting the head domain's ENUMERATION does not change the frame's
coverage. -/
theorem mem_allAssigns_cons_perm {d d' : Domain} {rest : List Domain}
    {a : Assignment} (h : d.enum.Perm d'.enum) :
    a ∈ allAssigns (d :: rest) ↔ a ∈ allAssigns (d' :: rest) := by
  rw [mem_allAssigns_cons_iff, mem_allAssigns_cons_iff]
  constructor
  · rintro ⟨x, hx, a', ha', rfl⟩
    refine ⟨x, ?_, a', ha', rfl⟩
    rw [DomainLike.mem_iff, domElems_eq_enum] at hx ⊢
    exact h.mem_iff.mp hx
  · rintro ⟨x, hx, a', ha', rfl⟩
    refine ⟨x, ?_, a', ha', rfl⟩
    rw [DomainLike.mem_iff, domElems_eq_enum] at hx ⊢
    exact h.mem_iff.mpr hx

/-- Replacing one slot's domain by one with a permutation of its
enumeration does not change the frame's coverage. -/
theorem mem_allAssigns_set_perm : ∀ (ds : List Domain) (k : Nat) (d d' : Domain)
    (a : Assignment), ds[k]? = some d → d.enum.Perm d'.enum →
    (a ∈ allAssigns ds ↔ a ∈ allAssigns (ds.set k d')) := by
  intro ds
  induction ds with
  | nil => intro k d d' a h; simp at h
  | cons d₀ rest ih =>
      intro k
      cases k with
      | zero =>
          intro d d' a h hperm
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [List.set_cons_zero]
          exact mem_allAssigns_cons_perm hperm
      | succ k =>
          intro d d' a h hperm
          simp only [List.getElem?_cons_succ] at h
          simp only [List.set_cons_succ]
          rw [mem_allAssigns_cons_iff, mem_allAssigns_cons_iff]
          constructor
          · rintro ⟨x, hx, a', ha', rfl⟩
            exact ⟨x, hx, a', (ih k d d' a' h hperm).mp ha', rfl⟩
          · rintro ⟨x, hx, a', ha', rfl⟩
            exact ⟨x, hx, a', (ih k d d' a' h hperm).mpr ha', rfl⟩

/-- EXHAUSTIVENESS THROUGH A PERMUTATION: when the slot's enumeration is a
permutation `v :: vs.enum` of the current domain, pinning `v` and retiring
`vs` covers exactly the parent. This is the phase-aware form of
`covers_pin_or_retire` — activity and phase reorder the branch but never
drop a value. -/
theorem covers_pin_or_retire_perm {f : Frame} {k : Nat} {d : Domain}
    {v : Value} {vs : Domain} (hget : f.doms[k]? = some d)
    (hperm : d.enum.Perm (v :: vs.enum)) (a : Assignment) :
    f.Covers a ↔ (f.pin k v).Covers a ∨ (f.retire k vs).Covers a := by
  have hklt : k < f.doms.length := (List.getElem?_eq_some_iff.mp hget).1
  rw [Frame.Covers, Frame.Covers, Frame.Covers, Frame.pin_doms, Frame.retire_doms]
  rw [mem_allAssigns_set_perm f.doms k d (Dom.ofList (v :: vs.enum)) a hget
    (by simpa using hperm)]
  have hsplit := allAssigns_set_split
    (ds := f.doms.set k (Dom.ofList (v :: vs.enum))) (k := k) (v := v) (vs := vs)
    ?_ a
  · rw [List.set_set, List.set_set] at hsplit
    exact hsplit
  · rw [List.getElem?_set_self hklt]
    simp

/-- The activity/phase-aware split: select the slot by the S2 rule, then
order its enumeration by the saved phase (head first when present). `none`
when selection is exhausted or the slot is not live. -/
def splitAct (f : Frame) (m : Meta) : Option (Nat × Value × Domain) :=
  match selectSlotAct f.doms m.scores with
  | none => none
  | some k =>
      match f.doms[k]? with
      | some d =>
          match m.suggest k d with
          | [] => none
          | w :: ws => some (k, w, Dom.ofList ws)
      | none => none

/-- The split's slot is exactly the S2 selector's output. -/
theorem splitAct_slot {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) :
    selectSlotAct f.doms m.scores = some k := by
  unfold splitAct at h
  cases hs : selectSlotAct f.doms m.scores with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hsg : m.suggest j d with
          | nil => simp [hd, hsg] at h
          | cons w ws =>
              simp only [hd, hsg, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -, -⟩ := h
              rfl

/-- The split's canonical data: some domain `d` at the selected slot, with
the suggestion the enumeration `v :: ws`, and the returned sibling exactly
`Dom.ofList ws`. -/
private theorem splitAct_spec_canonical {f : Frame} {m : Meta} {k : Nat}
    {v : Value} {vs : Domain} (h : splitAct f m = some (k, v, vs)) :
    ∃ (d : Domain) (ws : List Value), f.doms[k]? = some d ∧
      m.suggest k d = v :: ws ∧ vs = Dom.ofList ws := by
  unfold splitAct at h
  cases hs : selectSlotAct f.doms m.scores with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hsg : m.suggest j d with
          | nil => simp [hd, hsg] at h
          | cons w ws =>
              simp only [hd, hsg, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨d, ws, hd, hsg, rfl⟩

/-- The split's data: some domain `d` at the selected slot with the
suggestion exactly `v :: vs.enum` (so the split's value is the phase-first
ordering of `d`). -/
theorem splitAct_spec {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) :
    ∃ d : Domain, f.doms[k]? = some d ∧ m.suggest k d = v :: vs.enum := by
  obtain ⟨d, ws, hd, hsg, hvs⟩ := splitAct_spec_canonical h
  refine ⟨d, hd, ?_⟩
  rw [hsg, hvs]
  simp

/-- The split's domain is a permutation of the suggested enumeration: phase
saving only reorders values. -/
theorem splitAct_perm {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) :
    ∃ d : Domain, f.doms[k]? = some d ∧ d.enum.Perm (v :: vs.enum) := by
  obtain ⟨d, hd, hsg⟩ := splitAct_spec h
  exact ⟨d, hd, by rw [← hsg]; exact (m.suggest_perm k d).symm⟩

/-- LEGALITY: the activity/phase split selects a live slot (a legal
decision exists), for ANY metadata — scores, rescaling and phase cannot
fabricate or invalidate a decision. -/
theorem splitAct_live {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) : Live f.doms k :=
  selectSlotAct_live (splitAct_slot h)

/-- The split's sibling enumeration is nonempty: the retired alternative is
a legal branch. -/
theorem splitAct_vs_ne_nil {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) : vs.enum ≠ [] := by
  obtain ⟨d, hd, hsg⟩ := splitAct_spec h
  have hperm : d.enum.Perm (v :: vs.enum) := by
    rw [← hsg]; exact (m.suggest_perm k d).symm
  obtain ⟨v', vs', hv', hne'⟩ := splitAct_live h
  rw [hd] at hv'
  have hden' : d.enum = v' :: vs'.enum := by simpa using hv'
  have hperm' : (v' :: vs'.enum).Perm (v :: vs.enum) := by
    rw [← hden']; exact hperm
  intro hnil
  have hlen : (v :: vs.enum).length = (v' :: vs'.enum).length :=
    hperm'.length_eq.symm
  rw [hnil] at hlen
  simp only [List.length_cons, List.length_nil] at hlen
  have hpos : 0 < vs'.enum.length := List.length_pos_iff.mpr hne'
  omega

/-- EXHAUSTIVENESS: the parent's coverage is exactly the union of the
pinned child and the retired sibling — the phase-aware branch never drops
a value ("activity does not justify dropping values"). -/
theorem splitAct_covers {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) (a : Assignment) :
    f.Covers a ↔ (f.pin k v).Covers a ∨ (f.retire k vs).Covers a := by
  obtain ⟨d, hd, hsg⟩ := splitAct_spec h
  have hperm : d.enum.Perm (v :: vs.enum) := by
    rw [← hsg]; exact (m.suggest_perm k d).symm
  exact covers_pin_or_retire_perm hd hperm a

/-- STRICT PROGRESS (sum measure): both children of the activity/phase
split strictly decrease the frame's sum-of-lengths measure, for ANY
metadata. Rescaling and ties cannot break progress: the theorems are
quantified over all `m : Meta`. -/
theorem splitAct_mass_lt {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs)) :
    (f.pin k v).mass < f.mass ∧ (f.retire k vs).mass < f.mass := by
  obtain ⟨d, hd, hsg⟩ := splitAct_spec h
  have hperm : d.enum.Perm (v :: vs.enum) := by
    rw [← hsg]; exact (m.suggest_perm k d).symm
  obtain ⟨v', vs', hv', hne'⟩ := splitAct_live h
  rw [hd] at hv'
  have hden' : d.enum = v' :: vs'.enum := by simpa using hv'
  have hcard : 2 ≤ d.length := by
    have hpos : 0 < vs'.enum.length := List.length_pos_iff.mpr hne'
    rw [Dom.length_eq_enum, hden', List.length_cons]
    omega
  have hlen : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hperm.length_eq]
    simp
  constructor
  · have hlt : (Dom.ofList [v]).length < d.length := by
      rw [length_ofList]
      simp only [List.length_singleton]
      omega
    change sumMass (f.doms.set k (Dom.ofList [v])) < sumMass f.doms
    exact sumMass_set_lt hd hlt
  · have hlt : vs.length < d.length := by
      rw [Dom.length_eq_enum (d := vs), hlen]
      omega
    change sumMass (f.doms.set k vs) < sumMass f.doms
    exact sumMass_set_lt hd hlt

/-- STRICT PROGRESS (decide-arm `branchCost`): both children of the
activity/phase split strictly decrease the shared per-frame cost, for ANY
metadata (nonempty-box route shape as in `cost_pin_lt`). -/
theorem splitAct_cost_lt {f : Frame} {m : Meta} {k : Nat} {v : Value}
    {vs : Domain} (h : splitAct f m = some (k, v, vs))
    (hall : ∀ e ∈ f.doms, e.enum ≠ []) :
    (f.pin k v).cost < f.cost ∧ (f.retire k vs).cost < f.cost := by
  obtain ⟨d, hd, hsg⟩ := splitAct_spec h
  have hperm : d.enum.Perm (v :: vs.enum) := by
    rw [← hsg]; exact (m.suggest_perm k d).symm
  obtain ⟨v', vs', hv', hne'⟩ := splitAct_live h
  rw [hd] at hv'
  have hden' : d.enum = v' :: vs'.enum := by simpa using hv'
  have hcard : 2 ≤ d.length := by
    have hpos : 0 < vs'.enum.length := List.length_pos_iff.mpr hne'
    rw [Dom.length_eq_enum, hden', List.length_cons]
    omega
  have hlen : d.length = vs.enum.length + 1 := by
    rw [Dom.length_eq_enum, hperm.length_eq]
    simp
  constructor
  · have hlt : (Dom.ofList [v]).length < d.length := by
      rw [length_ofList]
      simp only [List.length_singleton]
      omega
    change branchCost (f.doms.set k (Dom.ofList [v])) < branchCost f.doms
    exact branchCost_set_lt hd hlt hall
  · have hlt : vs.length < d.length := by
      rw [Dom.length_eq_enum (d := vs), hlen]
      omega
    change branchCost (f.doms.set k vs) < branchCost f.doms
    exact branchCost_set_lt hd hlt hall

/-- COMPLETENESS: with valid metadata, a live slot always yields a split —
the activity/phase layer cannot get stuck while a legal decision exists. -/
theorem splitAct_complete {f : Frame} {m : Meta} (hwf : m.WF f.doms)
    (hl : ∃ k, f.Live k) : ∃ k v vs, splitAct f m = some (k, v, vs) := by
  obtain ⟨k, hksel⟩ :=
    selectSlotAct_complete (Meta.WF.scores_length_le hwf) hl
  obtain ⟨v0, vs0, hv0, -⟩ := selectSlotAct_live hksel
  obtain ⟨d, hd, hden⟩ : ∃ d : Domain, f.doms[k]? = some d ∧
      d.enum = v0 :: vs0.enum := by
    cases hd0 : f.doms[k]? with
    | none => rw [hd0] at hv0; simp at hv0
    | some d => exact ⟨d, rfl, by simpa [hd0] using hv0⟩
  have hne : m.suggest k d ≠ [] := Meta.suggest_ne_nil (by rw [hden]; simp)
  cases hsg : m.suggest k d with
  | nil => exact absurd hsg hne
  | cons w ws =>
      refine ⟨k, w, Dom.ofList ws, ?_⟩
      unfold splitAct
      simp only [hksel, hd, hsg]

/-- Phase independence of the SLOT choice: two metadata with the same
scores make the same selection (the phase only orders values, never picks
the slot). -/
theorem splitAct_slot_eq_of_scores_eq {f : Frame} {m m' : Meta} {k k' : Nat}
    {v v' : Value} {vs vs' : Domain} (h : m.scores = m'.scores)
    (hm : splitAct f m = some (k, v, vs))
    (hm' : splitAct f m' = some (k', v', vs')) : k = k' := by
  have h1 := splitAct_slot hm
  have h2 := splitAct_slot hm'
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- RESCALING/TIES CANNOT BREAK PROGRESS (explicit instance): after any
recorded conflict (the bounded policy update), the split still strictly
decreases the sum measure on both children. -/
theorem splitAct_mass_lt_after_update {f : Frame} {m : Meta}
    {c : Conflict} {k : Nat} {v : Value} {vs : Domain}
    (h : splitAct f (m.update c) = some (k, v, vs)) :
    (f.pin k v).mass < f.mass ∧ (f.retire k vs).mass < f.mass :=
  splitAct_mass_lt h

/-- Canonical data of the S1 split: the returned sibling is exactly
`Dom.ofList ws` for the enumerated tail `ws`. -/
private theorem Frame.split_spec_canonical {f : Frame} {k : Nat} {v : Value}
    {vs : Domain} (h : f.split = some (k, v, vs)) :
    ∃ (d : Domain) (ws : List Value), f.doms[k]? = some d ∧
      d.enum = v :: ws ∧ vs = Dom.ofList ws := by
  unfold Frame.split at h
  cases hs : selectSlot f.doms with
  | none => simp [hs] at h
  | some j =>
      simp only [hs] at h
      cases hd : f.doms[j]? with
      | none => simp [hd] at h
      | some d =>
          cases hden : Dom.enum d with
          | nil => simp [hd, hden] at h
          | cons w ws =>
              simp only [hd, hden, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨d, ws, hd, hden, rfl⟩

/-- S1 FALLBACK AT THE SPLIT (pointwise form): with aligned all-zero
activity and no saved phase, the activity/phase split returns exactly the
S1 split's data on every input. -/
theorem splitAct_eq_some_iff {f : Frame} {m : Meta} (hwf : m.WF f.doms)
    (hzero : ∀ j, m.scoreAt j = 0) (hnophase : ∀ j, m.phaseAt j = none)
    (p : Nat × Value × Domain) :
    splitAct f m = some p ↔ f.split = some p := by
  have hsel0 : selectSlotAct f.doms m.scores = selectSlot f.doms :=
    selectSlotAct_zero (Meta.WF.scores_length_le hwf) hzero
  obtain ⟨k, v, vs⟩ := p
  constructor
  · intro hp
    obtain ⟨d, ws, hd, hsg, hvs⟩ := splitAct_spec_canonical hp
    have hsl : selectSlotAct f.doms m.scores = some k := splitAct_slot hp
    have hsel : selectSlot f.doms = some k := by rw [← hsel0]; exact hsl
    have hden : d.enum = v :: ws := by
      rw [← Meta.suggest_of_phaseAt_none (hnophase k)]
      exact hsg
    unfold Frame.split
    rw [hsel]
    simp only [hd, hden]
    rw [hvs]
  · intro hp
    obtain ⟨d, ws, hd, hden, hvs⟩ := Frame.split_spec_canonical hp
    have hsl : selectSlot f.doms = some k := Frame.split_slot hp
    have hsel : selectSlotAct f.doms m.scores = some k := by rw [hsel0]; exact hsl
    have hsg : m.suggest k d = v :: ws := by
      rw [Meta.suggest_of_phaseAt_none (hnophase k)]
      exact hden
    unfold splitAct
    rw [hsel]
    simp only [hd, hsg]
    rw [hvs]

/-- S1 FALLBACK AT THE SPLIT: with aligned all-zero activity and no saved
phase, the activity/phase split IS the S1 split `Frame.split`. -/
theorem splitAct_eq_split {f : Frame} {m : Meta} (hwf : m.WF f.doms)
    (hzero : ∀ j, m.scoreAt j = 0) (hnophase : ∀ j, m.phaseAt j = none) :
    splitAct f m = f.split := by
  have hiff := splitAct_eq_some_iff hwf hzero hnophase
  cases h1 : splitAct f m with
  | none =>
      have h2 : f.split = none := by
        cases h2' : f.split with
        | none => rfl
        | some p =>
            exact absurd ((hiff p).mpr h2') (by rw [h1]; simp)
      rw [h2]
  | some p =>
      rw [(hiff p).mp h1]

/-! ## §6 Tiny-model demonstration

Concrete boxes from the S0/S1 prototype (`tinyBox`: cardinalities
`[2, 2, 3]`; `tinySmallLast`: `[3, 2]`), with computed proofs. The
examples show the three S2 acceptance behaviours on a tiny model: the
selector CHANGES under a recorded conflict, the rescale keeps the choice
and the proved bound, phase saving reorders only the values of the
selected slot, and the phase-aware split still covers the parent with
strictly progressing children. -/

/-- The tiny three-slot metadata: zero activity, no saved phase (aligned
with `DecisionProto.tinyBox`). -/
def tinyMeta0 : Meta := ⟨[0, 0, 0], [none, none, none]⟩

/-- The tiny two-slot metadata (aligned with `DecisionProto.tinySmallLast`). -/
def tinyMeta2 : Meta := ⟨[0, 0], [none, none]⟩

theorem tinyMeta0_wf : tinyMeta0.WF tinyBox := by
  simp [Meta.WF, tinyMeta0, tinyBox]

theorem tinyMeta2_wf : tinyMeta2.WF tinySmallLast := by
  simp [Meta.WF, tinyMeta2, tinySmallLast]

/-- ZERO ACTIVITY = S1: without any recorded conflict the S2 rule selects
the S1 slot (the `[2, 2, 3]` box: minimum-cardinality tie of slots 0, 1
resolved to slot 0). -/
theorem tinyBox_act_zero : selectSlotAct tinyBox tinyMeta0.scores = some 0 := by
  decide

/-- TIES: uniform positive activity leaves the S1 choice unchanged. -/
theorem tinyBox_act_tie : selectSlotAct tinyBox [1, 1, 1] = some 0 := by
  decide

/-- One recorded conflict on slot 2 raises its score to 1. -/
theorem tinyBox_bump : (tinyMeta0.update ⟨[2]⟩).scores = [0, 0, 1] := by
  decide

/-- THE SELECTOR CHANGES UNDER AN UPDATE: after recording a conflict on
slot 2 (cardinality 3), activity dominance picks slot 2 over the S1 choice
slot 0 (cardinality 2). -/
theorem tinyBox_act_updated :
    selectSlotAct tinyBox (tinyMeta0.update ⟨[2]⟩).scores = some 2 := by
  decide

/-- The tiny zero metadata is bounded. -/
theorem tinyMeta0_bounded : (tinyMeta0 : Meta).Bounded := by
  show ∀ s ∈ ([0, 0, 0] : List Nat), s ≤ 64
  intro s hs
  simp at hs
  omega

set_option maxRecDepth 8192

/-- 64 recorded conflicts on one slot reach exactly the bound. -/
theorem tinyBox_rescale64 :
    (tinyMeta0.update ⟨List.replicate 64 2⟩).scoreAt 2 = 64 := by
  decide

/-- THE RESCALE FIRES: the 65th recorded conflict bumps to 65, which
exceeds the bound and is rescaled EXACTLY to `65 / 2 = 32`. -/
theorem tinyBox_rescale_hit :
    (tinyMeta0.update ⟨List.replicate 65 2⟩).scoreAt 2 = 32 := by
  decide

/-- RESCALING KEEPS THE CHOICE: the rescaled activity still picks slot 2. -/
theorem tinyBox_rescale_select :
    selectSlotAct tinyBox (tinyMeta0.update ⟨List.replicate 65 2⟩).scores = some 2 := by
  decide

/-- THE PROVED BOUND: any number of recorded conflicts keeps every score at
most `64` (the general `Meta.Bounded.update` instantiated on the tiny
metadata). -/
theorem tinyBox_rescale_bounded :
    (tinyMeta0.update ⟨List.replicate 200 2⟩).Bounded :=
  tinyMeta0_bounded.update _

/-- The tiny two-slot frame (no decisions yet). -/
def tinySmallLastFrame : Frame := { doms := tinySmallLast, order := [] }

/-- ZERO ACTIVITY = S1 on the `[3, 2]` box: the later, strictly smaller
slot wins (the S0/S1 `tinySmallLast_select` behaviour). -/
theorem tinySmallLast_zero : selectSlotAct tinySmallLast tinyMeta2.scores = some 1 := by
  decide

/-- PHASE SAVING ORDERS VALUES ONLY: saving `false` at slot 1 makes the
domain suggestion `[false, true]` — a permutation of the original. -/
theorem tinySmallLast_phase_suggest :
    (tinyMeta2.savePhase 1 (Value.bool false)).suggest 1
      (Dom.ofList [Value.bool true, Value.bool false]) =
        [Value.bool false, Value.bool true] := rfl

/-- The activity/phase split without phase: the plain S1 head split. -/
theorem tinySmallLast_split_zero :
    splitAct tinySmallLastFrame tinyMeta2 =
      some (1, Value.bool true, Dom.ofList [Value.bool false]) := rfl

/-- THE PHASE TIE-BREAK FIRES: with `false` saved, the split tries `false`
first at the SAME slot (the selector is unchanged). -/
theorem tinySmallLast_split_phase :
    splitAct tinySmallLastFrame (tinyMeta2.savePhase 1 (Value.bool false)) =
      some (1, Value.bool false, Dom.ofList [Value.bool true]) := rfl

/-- The phase-aware split and the plain S1 split succeed together (the
pointwise fallback instance). -/
theorem tinySmallLast_eq_split :
    splitAct tinySmallLastFrame tinyMeta2 = tinySmallLastFrame.split := by
  apply splitAct_eq_split tinyMeta2_wf
  · intro j
    show ([0, 0] : List Nat).getD j 0 = 0
    cases j with
    | zero => rfl
    | succ j =>
        cases j with
        | zero => rfl
        | succ j => rfl
  · intro j
    show ([none, none] : List (Option Value)).getD j none = none
    cases j with
    | zero => rfl
    | succ j =>
        cases j with
        | zero => rfl
        | succ j => rfl

/-- The concrete assignment `[1, true]` is covered by the tiny frame. -/
theorem tinySmallLast_covered :
    tinySmallLastFrame.Covers [Value.int 1, Value.bool true] := by
  unfold Frame.Covers tinySmallLastFrame tinySmallLast
  rw [mem_allAssigns_cons_iff]
  refine ⟨Value.int 1, by simp, [Value.bool true], ?_, rfl⟩
  rw [mem_allAssigns_cons_iff]
  refine ⟨Value.bool true, by simp, [], by simp [allAssigns], rfl⟩

/-- SEARCH STILL EXHAUSTIVE: the covered assignment lands in one of the
phase-aware split's children (the `splitAct_covers` instance on the tiny
model). -/
theorem tinySmallLast_branch :
    (tinySmallLastFrame.pin 1 (Value.bool false)).Covers
        [Value.int 1, Value.bool true] ∨
      (tinySmallLastFrame.retire 1 (Dom.ofList [Value.bool true])).Covers
        [Value.int 1, Value.bool true] :=
  (splitAct_covers tinySmallLast_split_phase _).mp tinySmallLast_covered

/-- STRICT PROGRESS on the tiny model: both phase-aware children strictly
decrease the sum measure. -/
theorem tinySmallLast_progress :
    (tinySmallLastFrame.pin 1 (Value.bool false)).mass < tinySmallLastFrame.mass ∧
      (tinySmallLastFrame.retire 1 (Dom.ofList [Value.bool true])).mass <
        tinySmallLastFrame.mass :=
  splitAct_mass_lt tinySmallLast_split_phase

/-- READ-BACK on the tiny model: a covered assignment of the phase-aware
pinned child reads the chosen value at its ORIGINAL slot index. -/
theorem tinySmallLast_read {a : Assignment}
    (ha : (tinySmallLastFrame.pin 1 (Value.bool false)).Covers a) :
    a[1]? = some (Value.bool false) :=
  covers_read ha (k := 1) (v := Value.bool false) rfl

end LeanFzn.Solver.Propagation.ActivityProto
