/-
Purpose: exact decision pins and redundant-pin skip typing on mixed int/bool boxes.
Dependencies: LcgRunArms supplies semantic reachability and the head-domain fit bridge;
SchedulerDecision supplies sort-aware integer reads and exact Boolean pin semantics.
DAG: semantic branch reachability -> mixed decisions -> mixed run-state assembly.
Existing integer-kit statements remain unchanged.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunArms

namespace LeanFzn.Solver.UIP.LcgMixedDecisions
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunInv

/-- A split's actual value literal pins exactly the chosen value, including
Boolean slots; integer-view collisions are excluded by the original slot sort. -/
theorem lcgPinFits_shape {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig) :
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[cfg.branch.frame.2.length]? = some v) := by
  have hmem := pinHead_mem_orig' hsplit hreach
  have hval := (splitData_eq_some_iff.mp hsplit).2
  cases v with
  | int i =>
      have hl : l = negNe cfg.branch.frame.2.length i := by
        rw [valueLiteral_int] at hval
        exact (Option.some.inj hval).symm
      have hi := intShaped_of_mem_int hshape hmem
      intro a hfit
      rw [hl]
      constructor
      · intro hev
        obtain ⟨k, hk, hki⟩ := (eval_negNe_iff a _ i).mp hev
        have hget := getElem_of_slotInt_typed hfit hi hk
        rw [hki] at hget
        exact hget
      · intro hget
        exact (eval_negNe_iff a _ i).mpr
          ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩
  | bool b =>
      simp only [valueLiteral, Option.some.injEq] at hval
      subst l
      intro a _
      exact eval_posBool_iff a _ b
  | _ => cases hval

/-- The skip's prefix obligation follows from the recorded value pin for
both supported sorts, without a no-Boolean-trail assumption. -/
theorem lcgSkipTyped_shape {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : LcgReachableState leaf orig cfg.branch) (hshape : ShapeTypedDomains orig)
    (hred : TrailRedundant cfg.branch.trail l = true) : DecideSkipPrefixTyped orig cfg v := by
  intro a htrail hfit
  obtain ⟨e, he, hel⟩ := trailRedundant_iff.mp hred
  have hh : l.norm.eval a = some true := by
    have ht := htrail e he
    rwa [hel] at ht
  exact (lcgPinFits_shape hsplit hreach hshape a hfit).mp hh

end LeanFzn.Solver.UIP.LcgMixedDecisions
