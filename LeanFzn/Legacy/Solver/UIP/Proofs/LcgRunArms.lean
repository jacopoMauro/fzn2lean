/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunArms.lean
H2c (part 3): `LcgReachableState` versions of the decide-skip, pinned-decide, learned-prepend and
canonical-resume arms (all legacy versions take `ReachableState`, i.e. `hbr`).

M2 sparse-frame port: the split data is the scheduled `(l, k, v, vs)` tuple (the selected slot `k`
is `selectSlot f.doms`, not the positional `f.order.length`), the skip keeps the sparse pinned
frame `f.pin k v`, and the canonical resume is the frame-derived trail of `PendingBacked`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecision
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerDecideSkip
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
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch) :
    v ∈ orig.getD k Dom.empty := by
  have hspec := (splitData_eq_some_iff.mp hsplit).2.1
  have hmem : v ∈ cfg.branch.frame.doms.getD k Dom.empty :=
    (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum, enum_getD_of_enum_cons hspec]
      exact List.mem_cons_self)
  exact hreach.full_fits k v hmem

/-- **The int fresh-pin producer** at a split of an Lcg-reachable branch of an int box. -/
theorem lcgPinFits_int {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig) :
    ∃ i : Int, v = Value.int i ∧ l = negNe k i ∧
    ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[k]? = some v) := by
  have hmem := pinHead_mem_orig' hsplit hreach
  obtain ⟨i, rfl⟩ := allInt_getD hint k v ((DomainLike.mem_iff _ v).mp hmem)
  have hwl := (splitData_eq_some_iff.mp hsplit).2.2.1
  have hl : l = negNe k i := by
    rw [valueLiteral_int] at hwl
    exact (Option.some.inj hwl).symm
  refine ⟨i, rfl, hl, ?_⟩
  have hint' := intShaped_of_mem_int (shape_of_allInt hint) hmem
  intro a hfit
  rw [hl]
  constructor
  · intro hev
    obtain ⟨j, hj, hji⟩ := (eval_negNe_iff a _ i).mp hev
    have hget := getElem_of_slotInt_typed hfit hint' hj
    rw [hji] at hget
    exact hget
  · intro hget
    show (negNe k i).eval a = some true
    exact (eval_negNe_iff a _ i).mpr
      ⟨i, by simp [slotInt, hget, Value.intView], rfl⟩

/-- The redundant-pin skip's typed prefix residual, derived for an int box. -/
theorem lcgSkipTyped {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    DecideSkipPrefixTyped orig cfg k v := by
  obtain ⟨i, rfl, hl, hpin⟩ := lcgPinFits_int hsplit hreach hint
  intro a htrail hfit
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have h1 : (l.norm).eval a = some true := by
    have h3 := htrail e he
    rwa [hil] at h3
  exact (hpin a hfit).mp h1

/-- The redundant-pin skip successor is Lcg-reachable. -/
theorem lcgReachable_decideSkip {orig : List Domain} {cfg : SchedulerConfig leaf}
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (h : LcgReachableState leaf orig cfg.branch)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (htyped : DecideSkipPrefixTyped orig cfg k v) :
    LcgReachableState leaf orig (stepDecideSkip cfg k v).branch := by
  have hspec := (splitData_eq_some_iff.mp hsplit).2.1
  obtain ⟨dk, hdk, hdke⟩ := exists_dom_of_enum_cons hspec
  have hklt : k < cfg.branch.frame.doms.length :=
    (List.getElem?_eq_some_iff.mp hdk).1
  have hsub : ∀ w ∈ (Dom.ofList [v]), w ∈ cfg.branch.frame.doms.getD k Dom.empty := by
    intro w hw
    rw [List.getD_eq_getElem?_getD, hdk, Option.getD_some]
    rw [mem_ofList_iff, List.mem_singleton] at hw
    rw [hw]
    exact (DomainLike.mem_iff dk v).mpr (by rw [domElems_eq_enum, hdke]; exact List.mem_cons_self)
  rw [stepDecideSkip_branch]
  refine ⟨?_, ?_, ?_, ?_, ?_, h.levels, h.norm, h.reason_ent, h.trail_sem, h.learned_ent,
    h.sorted, h.distinct⟩
  · show (fullDomains (cfg.branch.frame.pin k v)).length = orig.length
    rw [fullDomains, Frame.domains, BranchFrame.pin_doms, List.length_set]
    exact h.length_ok
  · show ∀ i w, w ∈ (fullDomains (cfg.branch.frame.pin k v)).getD i Dom.empty →
      w ∈ orig.getD i Dom.empty
    intro i w hw
    exact h.full_fits i w (getD_set_subset hsub i w hw)
  · exact stepDecideSkip_pinsForced_of_typed h.pins_forced hsplit htyped
  · show ∀ e ∈ cfg.branch.trail, ∀ a,
      FrameCovers (cfg.branch.frame.pin k v) a → e.literal.eval a = some true
    intro e he a ha
    exact h.agrees e he a (covers_parent_of_covers_pinChild hsplit a ha)
  · show NarrowingComplete cfg.branch.trail orig (cfg.branch.frame.pin k v)
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

/-- The canonical resume base is Lcg-reachable (needs only the entailed database). -/
theorem lcgResumeBase_reachable {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hl : LearnedEntailed leaf bs.learned) (hb : PendingBacked orig f) :
    LcgReachableState leaf orig (resumePendingBase orig bs f) := by
  have hwf := canonicalTrail_wellFormed (orig := orig) (f := f) (bs := bs) hl
  exact
    { length_ok := hb.full_len
      full_fits := hb.fit
      pins_forced := pins_forced_canonical hb.shape hb.pins hb.fit
      agrees := agrees_canonicalTrail hb.shape hb.fit hb.full_len
      narrowing_complete := narrowing_complete_canonical hb.shape hb.full_len
      levels := hwf.1
      norm := hwf.2.1
      reason_ent := hwf.2.2.1
      trail_sem := trailSem_of_wf hwf (canonicalTrail_distinct hb.pins.1).2
      learned_ent := hwf.2.2.2.2
      sorted := canonicalTrail_sorted orig f
      distinct := canonicalTrail_distinct hb.pins.1 }

theorem lcgResume_reachable {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hl : LearnedEntailed leaf bs.learned) (hb : PendingBacked orig f)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (resumePending orig bs f) :=
  syncAll_lcgReachable (lcgResumeBase_reachable hl hb) hfits

end LeanFzn.Solver.UIP.LcgRunArms
