/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunArms.lean
H2c (part 3): `LcgReachableState` versions of the decide-skip, pinned-decide, learned-prepend and
canonical-resume arms (all legacy versions take `ReachableState`, i.e. `hbr`).
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunConflict
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood

namespace LeanFzn.Solver.UIP.LcgRunArms

variable {leaf : Assignment → Bool}

/-- Prepending an entailed payload keeps `LcgReachableState`. -/
theorem lcgReachable_prepend_learned {orig : List Domain} {bs : BranchState leaf}
    (h : LcgReachableState leaf orig bs) {payload : List Clause}
    (hp : LearnedEntailed leaf payload) :
    LcgReachableState leaf orig { bs with learned := payload ++ bs.learned } :=
  { h with learned_ent := fun c hc a ha =>
      (List.mem_append.mp hc).elim (fun h' => hp c h' a ha) (fun h' => h.learned_ent c h' a ha) }

/-- The pinned head value of a split sits in the run box's domain. -/
theorem pinHead_mem_orig' {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : LcgReachableState leaf orig cfg.branch) :
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

/-- **The int fresh-pin producer** at a split of an Lcg-reachable branch of an int box. -/
theorem lcgPinFits_int {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig) :
    ∃ i : Int, v = Value.int i ∧ l = negNe cfg.branch.frame.2.length i ∧
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[cfg.branch.frame.2.length]? = some v) := by
  have hmem := pinHead_mem_orig' hsplit hreach
  obtain ⟨i, rfl⟩ := allInt_getD hint _ v hmem
  have hwl := (splitData_eq_some_iff.mp hsplit).2
  have hl : l = negNe cfg.branch.frame.2.length i := by
    rw [valueLiteral_int] at hwl
    exact (Option.some.inj hwl).symm
  refine ⟨i, rfl, hl, ?_⟩
  have hint' := intShaped_of_mem_int (shape_of_allInt hint) hmem
  intro a hfit
  rw [hl]
  constructor
  · intro hev
    obtain ⟨k, hk, hki⟩ := (eval_negNe_iff a _ i).mp hev
    have hget := getElem_of_slotInt_typed hfit hint' hk
    rw [hki] at hget
    exact hget
  · intro hget
    show (negNe cfg.branch.frame.2.length i).eval a = some true
    exact (eval_negNe_iff a _ i).mpr
      ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩

/-- The redundant-pin skip's typed prefix residual, derived for an int box. -/
theorem lcgSkipTyped {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    DecideSkipPrefixTyped orig cfg v := by
  obtain ⟨i, rfl, hl, hpin⟩ := lcgPinFits_int hsplit hreach hint
  intro a htrail hfit
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have h1 : (l.norm).eval a = some true := by
    have h3 := htrail e he
    rwa [hil] at h3
  exact (hpin a hfit).mp h1

/-- The redundant-pin skip successor is Lcg-reachable. -/
theorem lcgReachable_decideSkip {orig : List Domain} {cfg : SchedulerConfig leaf}
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (h : LcgReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (htyped : DecideSkipPrefixTyped orig cfg v) :
    LcgReachableState leaf orig (stepDecideSkip cfg v doms).branch := by
  obtain ⟨hslots, _⟩ := splitData_eq_some_iff.mp hsplit
  have hframe : cfg.branch.frame = ((v :: vs) :: doms, cfg.branch.frame.2) :=
    Prod.ext hslots rfl
  rw [stepDecideSkip_branch]
  refine ⟨?_, ?_, ?_, ?_, ?_, h.levels, h.norm, h.reason_ent, h.trail_sem, h.learned_ent,
    h.sorted, h.distinct⟩
  · show (fullDomains (doms, cfg.branch.frame.2 ++ [v])).length = orig.length
    have hp := h.length_ok
    rw [hframe] at hp
    refine Eq.trans ?_ hp
    simp only [fullDomains, Frame.domains, List.length_append,
      List.length_cons, List.length_map, List.length_nil]
    omega
  · show ∀ i w, w ∈ (fullDomains (doms, cfg.branch.frame.2 ++ [v])).getD i [] →
      w ∈ orig.getD i []
    have hfit := h.full_fits
    rw [hframe] at hfit
    intro i w hw
    exact hfit i w (fullDomains_decide_subset (List.mem_cons_self ..) i w hw)
  · show PrefixForced cfg.branch.trail orig (cfg.branch.frame.2 ++ [v])
    exact stepDecideSkip_prefixForced_of_typed (doms := doms) h.prefix_forced htyped
  · show ∀ e ∈ cfg.branch.trail, ∀ a,
      FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a → e.literal.eval a = some true
    intro e he a ha
    exact h.agrees e he a (covers_parent_of_covers_pinChild hsplit a ha)
  · show NarrowingComplete cfg.branch.trail orig (doms, cfg.branch.frame.2 ++ [v])
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

/-- The canonical resume base is Lcg-reachable (needs only the entailed database). -/
theorem lcgResumeBase_reachable {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hl : LearnedEntailed leaf bs.learned) (hb : PendingBacked orig f) :
    LcgReachableState leaf orig (resumePendingBase orig bs f) := by
  have hwf := canonicalTrail_wellFormed (orig := orig) (f := f) (bs := bs) hl
  exact
    { length_ok := hb.full_len
      full_fits := hb.fit
      prefix_forced := prefix_forced_canonical hb.shape hb.pins hb.fit
      agrees := agrees_canonicalTrail hb.shape hb.fit hb.full_len
      narrowing_complete := narrowing_complete_canonical hb.shape hb.full_len
      levels := hwf.1
      norm := hwf.2.1
      reason_ent := hwf.2.2.1
      trail_sem := trailSem_of_wf hwf canonicalTrail_distinct.2
      learned_ent := hwf.2.2.2.2
      sorted := canonicalTrail_sorted orig f
      distinct := canonicalTrail_distinct }

theorem lcgResume_reachable {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hl : LearnedEntailed leaf bs.learned) (hb : PendingBacked orig f)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (resumePending orig bs f) :=
  syncAll_lcgReachable (lcgResumeBase_reachable hl hb) hfits

end LeanFzn.Solver.UIP.LcgRunArms
