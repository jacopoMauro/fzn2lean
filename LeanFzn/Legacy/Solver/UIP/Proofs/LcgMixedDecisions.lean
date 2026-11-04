/-
Purpose: exact decision pins and redundant-pin skip typing on mixed int/bool boxes.
Dependencies: LcgRunArms supplies semantic reachability and the head-domain fit bridge;
SchedulerDecision supplies sort-aware integer reads and exact Boolean pin semantics.
DAG: semantic branch reachability -> mixed decisions -> mixed run-state assembly.
Existing integer-kit statements remain unchanged.

M2 sparse-frame port: the split data is the scheduled `(l, k, v, vs)` tuple (the selected slot
`k` is `selectSlot f.doms`), and the pinning read is at the absolute slot `k`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunArms

namespace LeanFzn.Solver.UIP.LcgMixedDecisions
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunInv

/-- A split's actual value literal pins exactly the chosen value, including
Boolean slots; integer-view collisions are excluded by the original slot sort. -/
theorem lcgPinFits_shape {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig) :
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[k]? = some v) := by
  have hmem := pinHead_mem_orig' hsplit hreach
  have hval := (splitData_eq_some_iff.mp hsplit).2.2.1
  cases v with
  | int i =>
      have hl : l = negNe k i := by
        rw [valueLiteral_int] at hval
        exact (Option.some.inj hval).symm
      have hi := intShaped_of_mem_int hshape hmem
      intro a hfit
      rw [hl]
      constructor
      · intro hev
        obtain ⟨j, hj, hji⟩ := (eval_negNe_iff a _ i).mp hev
        have hget := getElem_of_slotInt_typed hfit hi hj
        rw [hji] at hget
        exact hget
      · intro hget
        exact (eval_negNe_iff a _ i).mpr
          ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      intro a _
      exact eval_posBool_iff a _ b
  | _ => simp [valueLiteral] at hval

/-- The skip's prefix obligation follows from the recorded value pin for
both supported sorts, without a no-Boolean-trail assumption. -/
theorem lcgSkipTyped_shape {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    DecideSkipPrefixTyped orig cfg k v := by
  intro a htrail hfit
  obtain ⟨e, he, hel⟩ := trailRedundant_iff.mp hred
  have hh : l.norm.eval a = some true := by
    have ht := htrail e he
    rwa [hel] at ht
  exact (lcgPinFits_shape hsplit hreach hshape a hfit).mp hh

end LeanFzn.Solver.UIP.LcgMixedDecisions
