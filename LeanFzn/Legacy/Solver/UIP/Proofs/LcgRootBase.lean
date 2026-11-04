/-
File: LeanFzn/Solver/UIP/Proofs/LcgRootBase.lean
H2e-2: `RootBase` (reason-less level-0 entries true at leaf solutions) is preserved by the
reasoned trail extensions: narrow, sync, explained closure, decide, restoration + asserting.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunGood
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRootTrue
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRootTrue
open LeanFzn.Solver.UIP.LcgRunGood

namespace LeanFzn.Solver.UIP.LcgRootBase

variable {leaf : Assignment → Bool}

theorem rootBase_append_reasoned {t ex : List TrailEntry} (h : RootBase leaf t)
    (hex : ∀ e ∈ ex, e.reason ≠ none) : RootBase leaf (t ++ ex) := by
  intro e he hl hr
  rcases List.mem_append.mp he with he | he
  · exact h e he hl hr
  · exact absurd hr (hex e he)

theorem rootBase_snoc_reasoned {t : List TrailEntry} (h : RootBase leaf t) (e : TrailEntry)
    (he : e.reason ≠ none) : RootBase leaf (t ++ [e]) :=
  rootBase_append_reasoned h (by intro x hx; rw [List.mem_singleton.mp hx]; exact he)

theorem rootBase_snoc_pos {t : List TrailEntry} (h : RootBase leaf t) (e : TrailEntry)
    (he : e.level ≠ 0) : RootBase leaf (t ++ [e]) := by
  intro x hx hl hr
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx hl hr
  · rw [List.mem_singleton.mp hx] at hl; exact absurd hl he

theorem narrowState_rootBase {bs : BranchState leaf} (h : RootBase leaf bs.trail)
    (g : BranchFrame) (l : Literal) (c : Clause) (learned : List Clause) :
    RootBase leaf (narrowState bs g l c learned).trail :=
  rootBase_snoc_reasoned h _ (by simp)

theorem syncOne_rootBase (orig : List Domain) {bs : BranchState leaf}
    (h : RootBase leaf bs.trail) (lit : Literal) :
    RootBase leaf (syncOne orig bs lit).trail := by
  unfold syncOne
  cases syncClause orig bs lit with
  | none => exact h
  | some c => exact narrowState_rootBase h _ _ _ _

theorem syncSlot_rootBase (orig : List Domain) {bs : BranchState leaf}
    (h : RootBase leaf bs.trail) (s : Nat) : RootBase leaf (syncSlot orig bs s).trail := by
  unfold syncSlot
  exact foldl_syncOne_inv (orig := orig) (P := fun b => RootBase leaf b.trail)
    (fun b lit hb => syncOne_rootBase orig hb lit) _ _ h

theorem syncAll_rootBase (orig : List Domain) {bs : BranchState leaf}
    (h : RootBase leaf bs.trail) : RootBase leaf (syncAll orig bs).trail := by
  unfold syncAll
  exact foldl_range_inv (orig := orig) (P := fun b => RootBase leaf b.trail) _
    (fun b i hb => syncSlot_rootBase orig hb _) _ _ h

theorem explainedClosure_rootBase (orig : List Domain) (original : List Clause)
    (props : List Propagator) {bs : BranchState leaf} (h : RootBase leaf bs.trail) :
    RootBase leaf (explainedClosure orig original props bs).trail :=
  explainedClosure_induction orig original props (fun b => RootBase leaf b.trail)
    (fun b d _ hb => syncSlot_rootBase orig (narrowState_rootBase hb _ _ _ _) _) bs h

theorem decide_rootBase {bs : BranchState leaf} (h : RootBase leaf bs.trail) (l : Literal) :
    RootBase leaf (bs.decide l).trail :=
  rootBase_snoc_pos h _ (by simp)

end LeanFzn.Solver.UIP.LcgRootBase
