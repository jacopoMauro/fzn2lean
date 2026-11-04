/-
File: LeanFzn/Solver/Propagation/SelectPolicy.lean

Purpose (PLAN §3.0 item 5(a): the slot-selection POLICY INPUT).

  The scheduler's decision arm selects its branching slot through a priority
  vector `σ : List Nat` carried by the scheduler configuration (heuristic
  metadata, never semantic state):

  * `selectSlotP σ ds` — when `σ` covers the box (`ds.length ≤ σ.length`) it
    is the S2 activity rule `ActivityProto.selectSlotAct` (maximum score,
    ties by the S1 `(cardinality, index)` key); otherwise it is exactly the
    S1 rule `DecisionProto.selectSlot`. The empty vector therefore runs the
    S1 policy unchanged (`selectSlotP_nil`).
  * the legality/completeness facts every consumer needs, for ARBITRARY `σ`:
    `selectSlotP_live`, `selectSlotP_complete`, `selectSlotP_none_iff`.

  Static priorities (O1: objective slot first) and dynamic activity (S2:
  conflict bumps) are both values of `σ`; the decision arm's coverage,
  progress and legality depend only on the facts above.

Dependencies: ActivityProto (S2 rule and its specification), DecisionProto
(S1 rule). DAG: ActivityProto -> SelectPolicy -> SparseRun.
-/
import LeanFzn.Legacy.Solver.Propagation.ActivityProto

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation

namespace LeanFzn.Solver.Propagation.SelectPolicy
open LeanFzn.Solver.Propagation.DecisionProto

/-- The policy-driven slot selection: the S2 rule when the priority vector
covers the box, the S1 rule otherwise. -/
def selectSlotP (σ : List Nat) (ds : List Domain) : Option Nat :=
  if ds.length ≤ σ.length then ActivityProto.selectSlotAct ds σ else selectSlot ds

/-- The empty priority vector is the S1 policy. -/
theorem selectSlotP_nil (ds : List Domain) : selectSlotP [] ds = selectSlot ds := by
  unfold selectSlotP
  cases ds with
  | nil => rfl
  | cons d rest => simp

/-- Every selected slot is live, for any priority vector. -/
theorem selectSlotP_live {σ : List Nat} {ds : List Domain} {k : Nat}
    (h : selectSlotP σ ds = some k) : Live ds k := by
  unfold selectSlotP at h
  split at h
  · exact ActivityProto.selectSlotAct_live h
  · exact selectSlot_live h

/-- A live slot always admits a selection, for any priority vector. -/
theorem selectSlotP_complete {σ : List Nat} {ds : List Domain}
    (hl : ∃ k, Live ds k) : ∃ k, selectSlotP σ ds = some k := by
  unfold selectSlotP
  split
  · exact ActivityProto.selectSlotAct_complete (by omega) hl
  · exact selectSlot_complete hl

/-- Selection is exhausted exactly when no slot is live. -/
theorem selectSlotP_none_iff {σ : List Nat} {ds : List Domain} :
    selectSlotP σ ds = none ↔ ¬ ∃ k, Live ds k := by
  unfold selectSlotP
  split
  · exact ActivityProto.selectSlotAct_none_iff (by omega)
  · exact selectSlot_none_iff

/-! ## Dynamic activity (S2): conflict bumps with exact halving -/

/-- The S2 rescale threshold: when a bump pushes the maximum score above it,
every score is halved exactly (the decay). -/
def ACT_BOUND : Nat := 1024

/-- Record one conflict: bump every listed slot by one, then halve all scores
exactly if the bound is exceeded. Only the heuristic vector changes; the
length (box alignment) is preserved (`bumpPrio_length`). -/
def bumpPrio (σ : List Nat) (slots : List Nat) : List Nat :=
  let b := slots.foldl ActivityProto.bumpAt σ
  if ActivityProto.maxOf b ≤ ACT_BOUND then b else b.map (· / 2)

theorem bumpPrio_length (σ slots : List Nat) : (bumpPrio σ slots).length = σ.length := by
  unfold bumpPrio
  simp only
  split
  · exact ActivityProto.foldl_bumpAt_length slots σ
  · rw [List.length_map]; exact ActivityProto.foldl_bumpAt_length slots σ

end LeanFzn.Solver.Propagation.SelectPolicy
