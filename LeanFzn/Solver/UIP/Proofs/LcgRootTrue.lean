/-
File: LeanFzn/Solver/UIP/Proofs/LcgRootTrue.lean
H2e-2: level-0 trail entries are true at every leaf solution. Reasoned entries follow from
`TrailSem` + `reason_ent` + sortedness; only reason-less level-0 entries (`RootBase`) are a base.
-/
import LeanFzn.Solver.UIP.Proofs.LcgReachable
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgReachable

namespace LeanFzn.Solver.UIP.LcgRootTrue

variable {leaf : Assignment → Bool}

/-- Level-0 entries of the trail hold at every leaf solution. -/
def RootTrue (leaf : Assignment → Bool) (t : List TrailEntry) : Prop :=
  ∀ e ∈ t, e.level = 0 → ∀ a, leaf a = true → e.literal.eval a = some true

/-- The base: reason-less level-0 entries hold at every leaf solution. -/
def RootBase (leaf : Assignment → Bool) (t : List TrailEntry) : Prop :=
  ∀ e ∈ t, e.level = 0 → e.reason = none → ∀ a, leaf a = true → e.literal.eval a = some true

theorem RootTrue.base {t : List TrailEntry} (h : RootTrue leaf t) : RootBase leaf t :=
  fun e he hl _ => h e he hl

theorem rootTrue_of_base {orig : List Domain} {bs : BranchState leaf}
    (hr : LcgReachableState leaf orig bs) (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hb : RootBase leaf bs.trail) : RootTrue leaf bs.trail := by
  have key : ∀ i (hi : i < bs.trail.length), (bs.trail[i]).level = 0 →
      ∀ a, leaf a = true → (bs.trail[i]).literal.eval a = some true := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro hi hlev a ha
      have hfit := hfits a ha
      have hmem : bs.trail[i] ∈ bs.trail := List.getElem_mem hi
      cases hre : (bs.trail[i]).reason with
      | none => exact hb _ hmem hlev hre a ha
      | some r =>
        have hsem := hr.trail_sem i _ (List.getElem?_eq_getElem hi) r hre
        obtain ⟨hpiv, hothers⟩ := hsem
        obtain ⟨hent, -⟩ := hr.reason_ent _ hmem r hre
        obtain ⟨q, hq, hqe⟩ := hent r.clause (List.mem_singleton_self _) a ha
        have hnorm := hr.norm _ hmem
        by_cases hpq : litEqB q.norm (bs.trail[i]).literal.norm = true
        · have hqq := litEqB_iff.mp hpq
          have h1 : q.norm.eval a = some true := by rw [Literal.norm_eval]; exact hqe
          rw [hqq, Literal.norm_eval] at h1
          exact h1
        · exfalso
          have hpq' : litEqB q.norm (bs.trail[i]).literal.norm = false := by simpa using hpq
          rcases hothers q hq hpq' with hroot | ⟨e', he', himp⟩
          · exact litFalseAtRoot_sound hroot hfit hqe
          · obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp he'
            have hjlt : j < i := by
              have := hj; simp only [List.length_take] at this; omega
            have hjl : j < bs.trail.length := by omega
            have hee : e' = bs.trail[j] := by rw [← hje]; simp
            have hsorted := List.pairwise_iff_getElem.mp hr.sorted j i hjl hi hjlt
            have hl0 : (bs.trail[j]).level = 0 := by omega
            have htrue := ih j hjlt hjl hl0 a ha
            rw [hee] at himp
            have hfalse := impliesP_negate_sound himp hfit hqe
            rw [htrue] at hfalse
            cases hfalse
  intro e he hl a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  exact key i hi hl a ha

end LeanFzn.Solver.UIP.LcgRootTrue
