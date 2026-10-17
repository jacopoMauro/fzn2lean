/-
File: LeanFzn/Solver/UIP/Proofs/LcgReachable.lean
H2a: `LcgReachableState` = `ReachableState` with the exact-chronology conjunct of
`BranchState.WellFormed` replaced by the semantic `TrailSem` contract, and the
transfer lemmas re-proved over it. Per-event hypotheses are explicit premises
(the event contract is H2b).
-/
import LeanFzn.Solver.UIP.Proofs.LcgContract
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantReasons
import LeanFzn.Solver.UIP.Proofs.SchedulerBackjump
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv

namespace LeanFzn.Solver.UIP.LcgReachable

variable {leaf : Assignment → Bool}

/-- `ReachableState` with exact chronology replaced by `TrailSem`. -/
structure LcgReachableState (leaf : Assignment → Bool) (orig : List Domain)
    (bs : BranchState leaf) : Prop where
  length_ok : (fullDomains bs.frame).length = orig.length
  full_fits : ∀ i v, v ∈ (fullDomains bs.frame).getD i [] → v ∈ orig.getD i []
  prefix_forced : PrefixForced bs.trail orig bs.frame.2
  agrees : ∀ e ∈ bs.trail, ∀ a, FrameCovers bs.frame a →
    e.literal.eval a = some true
  narrowing_complete : NarrowingComplete bs.trail orig bs.frame
  /-- trail levels bounded by the current level -/
  levels : ∀ e ∈ bs.trail, e.level ≤ bs.level
  /-- trail literals are normalized -/
  norm : ∀ e ∈ bs.trail, e.literal = e.literal.norm
  /-- reasons are entailed and carry the literal as pivot -/
  reason_ent : ∀ e ∈ bs.trail, ∀ r ∈ e.reason,
    LearnedEntailed leaf [r.clause] ∧ (e.literal ∈ r.clause) = True
  /-- semantic chronology (replaces exact chronology) -/
  trail_sem : TrailSem orig bs.trail
  learned_ent : LearnedEntailed leaf bs.learned
  sorted : TrailLevelSorted bs.trail
  distinct : TrailLiteralsDistinct bs.trail

/-- Exact chronology (with distinct entries) implies the semantic contract. -/
theorem trailSem_of_wf {orig : List Domain} {bs : BranchState leaf}
    (h : bs.WellFormed) (hnd : List.Nodup bs.trail) : TrailSem orig bs.trail := by
  intro i e hi r hr
  have heM : e ∈ bs.trail := List.mem_of_getElem? hi
  have hEnorm := h.2.1 e heM
  obtain ⟨hent, hpiv⟩ := h.2.2.1 e heM r hr
  have hpiv' : e.literal ∈ r.clause := by simpa using hpiv
  refine ⟨by rw [← hEnorm]; exact hpiv', fun q hq hne => ?_⟩
  have hne' : q ≠ e.literal := by
    intro hq'
    subst hq'
    rw [← hEnorm] at hne
    simp [litEqB] at hne
  obtain ⟨e', he', heq, j', k, hj', hk, hje', hke, hjk⟩ := h.2.2.2.1 e heM r hr q hq hne'
  have hi' : i < bs.trail.length := (List.getElem?_eq_some_iff.mp hi).1
  have hik : k = i := by
    have h1 : bs.trail[k]'hk = bs.trail[i]'hi' := by
      rw [hke]; exact (List.getElem?_eq_some_iff.mp hi).2.symm
    exact (List.getElem_inj hnd).mp h1
  subst hik
  right
  refine ⟨e', ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨j', by simp [List.length_take]; omega, ?_⟩
    simp [List.getElem_take, hje']
  · have hn := h.2.1 e' he'
    have : q.negate.norm = e'.literal := by rw [← heq]; exact hn.symm
    rw [this]
    exact impliesP_refl _ _

/-- Every reachable state is an Lcg-reachable state. -/
theorem lcgReachable_of_reachable {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) : LcgReachableState leaf orig bs :=
  ⟨h.length_ok, h.full_fits, h.prefix_forced, h.agrees, h.narrowing_complete,
    h.wf.1, h.wf.2.1, h.wf.2.2.1, trailSem_of_wf h.wf h.distinct.2, h.wf.2.2.2.2, h.sorted, h.distinct⟩

theorem lcgReachable_decide {leaf : Assignment → Bool} {orig : List Domain}
    {bs : BranchState leaf} {d : Domain} {rest : List Domain} {w : Value}
    {l : Literal}
    (h : LcgReachableState leaf orig bs)
    (hdom : bs.frame.1 = d :: rest)
    (hw : w ∈ d)
    (hpin : ∀ a : Assignment, a.Fits orig →
      (l.norm.eval a = some true ↔ a[bs.frame.2.length]? = some w))
    (hfresh : ∀ e ∈ bs.trail, e.literal ≠ l.norm) :
    LcgReachableState leaf orig
      { (bs.decide l) with frame := (rest, bs.frame.2 ++ [w]) } := by
  -- the parent frame, for the subset transfer
  have hparentFrame : bs.frame = (d :: rest, bs.frame.2) :=
    Prod.ext hdom rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    have hp := h.length_ok
    rw [hparentFrame] at hp
    refine Eq.trans ?_ hp
    simp only [fullDomains, Frame.domains, List.length_append,
      List.length_singleton, List.length_cons, List.length_map,
      List.length_nil]
    omega
  · -- no invented values: the child box is a subset of the parent's
    have hfit := h.full_fits
    rw [hparentFrame] at hfit
    intro i v hv
    exact hfit i v (fullDomains_decide_subset hw i v (by
      simpa only [BranchState.decide] using hv))
  · -- the extended prefix is forced
    intro a htrail hfit i hi
    rw [BranchState.decide] at hi
    have hlen : (bs.frame.2 ++ [w]).length = bs.frame.2.length + 1 := by simp
    by_cases hlt : i < bs.frame.2.length
    · have hold := h.prefix_forced a (fun e he =>
        htrail e (List.mem_append.mpr (Or.inl he))) hfit i hlt
      rw [hold]
      rw [List.getElem?_append, if_pos hlt]
    · have hi' : i = bs.frame.2.length := by
        rw [List.length_append, List.length_singleton] at hi
        omega
      subst hi'
      have hentry : l.norm.eval a = some true :=
        htrail _ (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
      rw [show (bs.frame.2 ++ [w])[bs.frame.2.length]? = some w by simp]
      exact (hpin a hfit).mp hentry
  · -- every entry holds at every child-covered assignment
    intro e he a hcov
    rw [BranchState.decide] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact h.agrees e he a (by
        rw [hparentFrame]
        exact FrameCovers_decide hw hcov)
    · -- the fresh entry: the pinned value is the chosen prefix value
      simp only [BranchState.decide]
      obtain ⟨tail, htail, rfl⟩ := hcov
      rw [List.append_assoc]
      have hfitsW : (bs.frame.2 ++ (w :: tail)).Fits orig := by
        have hcov' : FrameCovers (rest, bs.frame.2 ++ [w])
            (bs.frame.2 ++ (w :: tail)) :=
          ⟨tail, htail, by simp [List.append_assoc]⟩
        have hf := FrameCovers.fits hcov'
        refine ⟨?_, ?_⟩
        · rw [hf.1]
          simp only [fullDomains, Frame.domains, List.length_append,
            List.length_cons, List.length_map, List.length_singleton,
            List.length_nil]
          have hp := h.length_ok
          rw [hparentFrame] at hp
          simp only [fullDomains, Frame.domains, List.length_append,
            List.length_cons, List.length_map, List.length_singleton,
            List.length_nil] at hp
          omega
        · intro i v hv
          have hm : v ∈ (fullDomains (rest, bs.frame.2 ++ [w])).getD i [] := by
            simpa only [fullDomains] using hf.2 i v hv
          have hm2 : v ∈ (fullDomains (d :: rest, bs.frame.2)).getD i [] :=
            fullDomains_decide_subset hw i v hm
          rw [← hparentFrame] at hm2
          exact h.full_fits i v hm2
      exact (hpin _ hfitsW).mpr (by simp)

  · -- narrowing is complete: the child's remaining domains are the
    -- parent's, shifted by one
    intro i u hu hnot
    have hcomp := h.narrowing_complete (i + 1) u
    rw [hparentFrame] at hcomp
    have hshift : (d :: rest).getD (i + 1) [] = rest.getD i [] := by
      simp [List.getD_cons_succ]
    have horig : u ∈ orig.getD (bs.frame.2.length + (i + 1)) [] := by
      have := hu
      rw [show (bs.frame.2 ++ [w]).length + i = bs.frame.2.length + (i + 1) by
        simp; omega] at this
      exact this
    have hnot' : u ∉ (d :: rest).getD (i + 1) [] := by
      rw [hshift]
      exact hnot
    obtain ⟨e, he, hslot, hfalse⟩ := hcomp horig hnot'
    refine ⟨e, ?_, ?_, hfalse⟩
    · exact List.mem_append.mpr (Or.inl he)
    · rw [hslot]
      simp only [List.length_append, List.length_singleton]
      omega
  · -- levels
    intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact Nat.le_trans (h.levels e he) (Nat.le_succ _)
    · simp only [BranchState.decide]
      simp
  · -- normalization
    intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact h.norm e he
    · simp only [BranchState.decide]
      rw [norm_norm]
  · -- entailed reasons with pivot
    intro e he r hr
    rcases trail_append_entry_mem he with he | rfl
    · exact h.reason_ent e he r hr
    · simp only [BranchState.decide] at hr
      cases hr
  · -- semantic chronology: a decision has no reason
    exact h.trail_sem.snoc_decision
  · exact h.learned_ent
  · -- the trail stays level-sorted: the fresh decision sits at the NEW
    -- level, which dominates every existing entry (well-formedness)
    rw [BranchState.decide]
    refine levelSorted_append h.sorted ?_
    intro e' he'
    have hle := h.levels e' he'
    show e'.level ≤ bs.level + 1
    omega
  · -- the duplicate-safe discipline: the decision is a BRANCHING PIN
    rw [BranchState.decide]
    exact TrailLiteralsDistinct.decisionEntry h.distinct h.norm hfresh


/-- Projection for consumers that need no chronology: the chronology-free
structural conjuncts of `BranchState.WellFormed`. -/
theorem LcgReachableState.wf_nochron {orig : List Domain} {bs : BranchState leaf}
    (h : LcgReachableState leaf orig bs) :
    (∀ e ∈ bs.trail, e.level ≤ bs.level) ∧ (∀ e ∈ bs.trail, e.literal = e.literal.norm) ∧
    (∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      LearnedEntailed leaf [r.clause] ∧ (e.literal ∈ r.clause) = True) ∧
    LearnedEntailed leaf bs.learned :=
  ⟨h.levels, h.norm, h.reason_ent, h.learned_ent⟩

/-- IMPLIED-ENTRY transfer. The reason's semantic justification by the CURRENT
trail is an explicit premise. -/
theorem lcgReachable_recordImplied {orig : List Domain}
    {bs : BranchState leaf} {l : Literal} {r : Reason}
    (h : LcgReachableState leaf orig bs)
    (hagrees : ∀ a, FrameCovers bs.frame a → l.norm.eval a = some true)
    (hent : LearnedEntailed leaf [r.clause])
    (hsem : SemReasonOK orig bs.trail l.norm r.clause)
    (hfresh : ∀ e' ∈ bs.trail, e'.literal ≠ l.norm) :
    LcgReachableState leaf orig (bs.recordImplied l r) := by
  refine ⟨h.length_ok, h.full_fits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a htrail hfit i hi
    exact h.prefix_forced a
      (fun e he => htrail e (List.mem_append.mpr (Or.inl he))) hfit i hi
  · intro e he a hcov
    rcases trail_append_entry_mem he with he | rfl
    · exact h.agrees e he a hcov
    · simpa [BranchState.recordImplied] using hagrees a hcov
  · intro i w hw hnot
    obtain ⟨e, he, hslot, hfalse⟩ := h.narrowing_complete i w hw hnot
    exact ⟨e, List.mem_append.mpr (Or.inl he), hslot, hfalse⟩
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact h.levels e he
    · simp [BranchState.recordImplied]
  · intro e he
    rcases trail_append_entry_mem he with he | rfl
    · exact h.norm e he
    · simp only [BranchState.recordImplied]
      rw [norm_norm]
  · intro e he r' hr'
    rcases trail_append_entry_mem he with he | rfl
    · exact h.reason_ent e he r' hr'
    · simp only [BranchState.recordImplied] at hr'
      injection hr' with hr'
      subst hr'
      exact ⟨hent, by simpa [BranchState.recordImplied, Literal.norm_idem] using hsem.1⟩
  · exact h.trail_sem.snoc_propagated hsem
  · exact h.learned_ent
  · rw [BranchState.recordImplied]
    refine levelSorted_append h.sorted ?_
    intro e' he'
    have hle := h.levels e' he'
    show e'.level ≤ bs.level
    omega
  · rw [BranchState.recordImplied]
    exact TrailLiteralsDistinct.enqueue h.distinct h.norm hfresh

/-- LEARNING transfer: adding a globally entailed clause. -/
theorem lcgReachable_learnGlobal {orig : List Domain} {bs : BranchState leaf} {c : Clause}
    (h : LcgReachableState leaf orig bs) (hent : LearnedEntailed leaf [c]) :
    LcgReachableState leaf orig (bs.learnGlobal c) :=
  ⟨h.length_ok, h.full_fits, h.prefix_forced, h.agrees, h.narrowing_complete,
    h.levels, h.norm, h.reason_ent, h.trail_sem,
    fun c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact fun a ha => hent c' (List.mem_singleton_self _) a ha
      · exact h.learned_ent c' hc',
    h.sorted, h.distinct⟩

/-- RESTORATION transfer when the whole trail is at or below the target. -/
theorem lcgReachable_restoreLevel {orig : List Domain} {bs : BranchState leaf} {target : Nat}
    (h : LcgReachableState leaf orig bs)
    (hlev : ∀ e ∈ bs.trail, e.level ≤ target) :
    LcgReachableState leaf orig (bs.restoreLevel target) := by
  have htrail : (bs.restoreLevel target).trail = bs.trail := by
    show bs.trail.filter (fun e => e.level ≤ target) = bs.trail
    exact List.filter_eq_self.mpr (fun a ha => by simpa using hlev a ha)
  refine ⟨h.length_ok, h.full_fits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.learned_ent, ?_, ?_⟩
  · intro a htrail' hfit i hi
    exact h.prefix_forced a
      (fun e he => htrail' e (by rw [htrail]; exact he)) hfit i hi
  · intro e he a hcov
    exact h.agrees e (by rw [← htrail]; exact he) a hcov
  · intro i w hw hnot
    obtain ⟨e, he, hslot, hfalse⟩ := h.narrowing_complete i w hw hnot
    exact ⟨e, by rw [htrail]; exact he, hslot, hfalse⟩
  · intro e he
    have he' : e ∈ bs.trail := by rw [htrail] at he; exact he
    exact hlev e he'
  · intro e he
    exact h.norm e (by rw [htrail] at he; exact he)
  · intro e he r hr
    exact h.reason_ent e (by rw [htrail] at he; exact he) r hr
  · rw [htrail]; exact h.trail_sem
  · rw [htrail]; exact h.sorted
  · rw [htrail]; exact h.distinct

/-- `explainedStep_narrow_reachable` over `LcgReachableState`: the exact-chronology
premise is replaced by the semantic justification of the pushed reason. -/
theorem lcgExplainedStep_narrow_reachable {orig : List Domain}
    {bs : BranchState leaf} {g : BranchFrame} {l : Literal} {c : Clause}
    {learned : List Clause}
    (hreach : LcgReachableState leaf orig bs)
    (hfilter : filterFrame l bs.frame = some g)
    (hfresh : ∀ e ∈ bs.trail, e.literal ≠ l.norm)
    (hin : l.atom.slot < (fullDomains bs.frame).length)
    (hent : LearnedEntailed leaf learned)
    (hentReason : LearnedEntailed leaf [c])
    (hsem : SemReasonOK orig bs.trail l.norm c) :
    LcgReachableState leaf orig (narrowState bs g l c learned) := by
  have hpre := filterFrame_prefix hfilter
  have hlen := filterFrame_rem_length hfilter
  have hframe : (narrowState bs g l c learned).frame = g := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- length
    have hgo : (fullDomains bs.frame).length = orig.length := hreach.length_ok
    rw [fullDomains_length] at hgo
    rw [hframe, fullDomains_length, hpre, hlen]
    exact hgo
  · -- no invented values
    intro i v hv
    exact hreach.full_fits i v (Frame.domains_subsets hfilter i v
      (by simpa only [narrowState] using hv))
  · -- the prefix is still forced (the trail only grew)
    intro a htrail hfit i hi
    have hi' : i < bs.frame.2.length := by
      rw [hframe, hpre] at hi
      exact hi
    have hgoal : a[i]? = (narrowState bs g l c learned).frame.2[i]? := by
      rw [hframe, hpre]
      exact hreach.prefix_forced a (fun e he =>
        htrail e (by
          simp only [narrowState]
          exact List.mem_append.mpr (Or.inl he))) hfit i hi'
    exact hgoal
  · -- every entry holds at every covered assignment
    intro e he a hcov
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact hreach.agrees e he a (filterFrame_refines hfilter hcov)
    · refine filterFrame_literal_holds hfilter hcov ?_
      have hlenfull : (fullDomains g).length = (fullDomains bs.frame).length := by
        rw [fullDomains_length, fullDomains_length, hpre, hlen]
      rw [hlenfull]
      exact hin
  · -- narrowing is complete
    intro i w horig hnot
    by_cases hwas : w ∈ bs.frame.1.getD i []
    · -- dropped by this filter: the fresh entry witnesses it
      obtain ⟨hslot, hfalse⟩ := filterFrame_removal_witness hfilter hwas hnot
      refine ⟨{ literal := l.norm, level := bs.level,
                reason := some { clause := c } }, ?_, ?_, ?_⟩
      · simp only [narrowState]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      · show l.norm.atom.slot = g.2.length + i
        rw [norm_atom_slot, hslot, hpre]
      · rwa [norm_valueHolds]
    · -- already excluded: the old witness, transported
      have horig' : w ∈ orig.getD (bs.frame.2.length + i) [] := by
        rw [hframe, hpre] at horig
        exact horig
      obtain ⟨e, he, hslot, hfalse⟩ := hreach.narrowing_complete i w horig' hwas
      refine ⟨e, ?_, ?_, hfalse⟩
      · simp only [narrowState]
        exact List.mem_append.mpr (Or.inl he)
      · show e.literal.atom.slot = g.2.length + i
        rw [hslot, hpre]
  · intro e he
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact hreach.levels e he
    · simp [narrowState]
  · intro e he
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact hreach.norm e he
    · simp [narrowState, norm_norm]
  · intro e he r hr
    simp only [narrowState] at he
    rcases trail_append_entry_mem he with he | rfl
    · exact hreach.reason_ent e he r hr
    · have hr1 : { clause := c } = r := by
        simpa only [Option.mem_some_iff] using hr
      rw [← hr1]
      exact ⟨hentReason, by simpa [narrowState, Literal.norm_idem] using hsem.1⟩
  · -- semantic chronology: the new entry is justified by the current trail
    simp only [narrowState]
    exact hreach.trail_sem.snoc_propagated hsem
  · intro cl hcl
    simp only [narrowState, List.mem_append] at hcl
    rcases hcl with hcl | hcl
    · exact hent cl hcl
    · exact hreach.learned_ent cl hcl
  · -- the trail stays LEVEL-SORTED (B2's uniqueness enabler): the fresh
    -- entry sits at the current level, which dominates every existing
    -- entry by well-formedness, and the reason clause never re-seeds the
    -- level order
    rw [narrowState]
    refine levelSorted_append hreach.sorted ?_
    intro e' he'
    have hle := hreach.levels e' he'
    show e'.level ≤ bs.level
    omega
  · -- the duplicate-safe discipline: the appended entry is the
    -- absence-checked enqueue of a fresh normalized literal (A1's
    -- `TrailLiteralsDistinct.enqueue`), so `distinct` is discharged from
    -- `hfresh`, not assumed
    rw [narrowState]
    exact TrailLiteralsDistinct.enqueue hreach.distinct hreach.norm hfresh

/-! ## Synchronisation -/

theorem syncOne_lcgReachable {orig : List Domain} {bs : BranchState leaf}
    (lit : Literal) (hreach : LcgReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (syncOne orig bs lit) := by
  unfold syncOne
  cases h : syncClause orig bs lit with
  | none => exact hreach
  | some c =>
    simp only
    have hin := syncClause_in h
    have hsem : SemReasonOK orig bs.trail lit.norm c := by
      obtain ⟨d, ex, -, -, -, -, -, hx, rfl⟩ := syncClause_spec h
      refine ⟨by simp [Literal.norm_idem], fun q hq hne => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd hne (by simp [litEqB])
      · obtain ⟨e, he, rfl⟩ := (syncExplain_spec hx).1 q hq
        exact semFalsified_of_negation he
    refine lcgExplainedStep_narrow_reachable hreach (syncClause_filter h)
      (syncClause_hfresh h) hin (fun _ h => absurd h (by simp))
      (syncClause_entailed h hfits ?_) hsem
    have := hreach.length_ok
    omega

theorem syncSlot_lcgReachable {orig : List Domain} {bs : BranchState leaf}
    (s : Nat) (hreach : LcgReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (syncSlot orig bs s) := by
  unfold syncSlot
  exact foldl_syncOne_inv (P := fun b => LcgReachableState leaf orig b)
    (fun b lit hb => syncOne_lcgReachable lit hb hfits) _ _ hreach

theorem syncAll_lcgReachable {orig : List Domain} {bs : BranchState leaf}
    (hreach : LcgReachableState leaf orig bs)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (syncAll orig bs) := by
  unfold syncAll
  exact foldl_range_inv (orig := orig) (P := fun b => LcgReachableState leaf orig b) _
    (fun b i hb => syncSlot_lcgReachable _ hb hfits) _ _ hreach

theorem stepNarrowSync_lcgReachable {orig : List Domain} {bs : BranchState leaf}
    (d : ProductiveDeduction leaf bs)
    (h : LcgReachableState leaf orig
      (narrowState bs d.frame d.literal d.reason d.learned))
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    LcgReachableState leaf orig (stepNarrowSync orig bs d) :=
  syncSlot_lcgReachable _ h hfits

/-! ## Closure and backjump -/

/-- Per-event premise (H2b discharges it): every selected deduction at an
Lcg-reachable state has an entailed reason, an in-range slot and a reason
semantically justified by the current trail. -/
def LcgEventPremise (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop :=
  ∀ bs : BranchState leaf, LcgReachableState leaf orig bs →
    ∀ d : ProductiveDeduction leaf bs, explainedDeduction original props bs = some d →
      LearnedEntailed leaf [d.reason] ∧
      d.literal.atom.slot < (fullDomains bs.frame).length ∧
      SemReasonOK orig bs.trail d.literal.norm d.reason

theorem lcgExplainedDeduction_narrow_reachable {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hev : LcgEventPremise leaf orig original props)
    {bs : BranchState leaf} (hreach : LcgReachableState leaf orig bs)
    {d : ProductiveDeduction leaf bs}
    (hd : explainedDeduction original props bs = some d) :
    LcgReachableState leaf orig (narrowState bs d.frame d.literal d.reason d.learned) := by
  obtain ⟨hent, hin, hsem⟩ := hev bs hreach d hd
  exact lcgExplainedStep_narrow_reachable hreach d.filtered
    (explainedDeduction_fresh hd) hin
    (explainedDeduction_learned_entailed hd hent) hent hsem

theorem lcgExplainedClosure_reachable {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hev : LcgEventPremise leaf orig original props)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (bs : BranchState leaf) (hreach : LcgReachableState leaf orig bs) :
    LcgReachableState leaf orig (explainedClosure orig original props bs) := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel →
      LcgReachableState leaf orig bs →
      LcgReachableState leaf orig (explainedClosure orig original props bs) from
    h (Frame.mass bs.frame) bs (Nat.le_refl _) hreach
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hreach
    rw [explainedClosure]
    split
    · exact hreach
    · rename_i d _
      exfalso
      have hdec := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hreach
    rw [explainedClosure]
    split
    · exact hreach
    · rename_i d hd
      refine ih (stepNarrowSync orig bs d) ?_ ?_
      · have hdec := d.decreases
        simp only [stepNarrowSync_frame]
        omega
      · exact stepNarrowSync_lcgReachable d
          (lcgExplainedDeduction_narrow_reachable hev hreach hd) hfits

theorem lcgPerform_reachable_of_narrowFrame {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hev : LcgEventPremise leaf orig original props)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    {p : BackjumpPlan leaf} {bs s : BranchState leaf} {g : BranchFrame}
    (hg : filterFrame p.asserting p.checkpoint.frame = some g)
    (hpre : LcgReachableState leaf orig
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g))
    (h : p.perform bs orig original props = some s) :
    LcgReachableState leaf orig s := by
  obtain ⟨g', hg', rfl⟩ := perform_eq_some_iff.mp h
  rw [hg] at hg'
  cases hg'
  exact lcgExplainedClosure_reachable hev hfits _ (syncAll_lcgReachable hpre hfits)

/-- Lcg version of `RestorationPreReachable`. -/
def LcgRestorationPreReachable (leaf : Assignment → Bool) (orig : List Domain)
    (p : BackjumpPlan leaf) (bs : BranchState leaf) : Prop :=
  ∃ g : BranchFrame, filterFrame p.asserting p.checkpoint.frame = some g ∧
    LcgReachableState leaf orig
      ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)

theorem lcgPerform_reachable_of_pre {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hev : LcgEventPremise leaf orig original props)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (hpre : LcgRestorationPreReachable leaf orig p bs)
    (h : p.perform bs orig original props = some s) :
    LcgReachableState leaf orig s := by
  obtain ⟨g, hg, hgpre⟩ := hpre
  exact lcgPerform_reachable_of_narrowFrame hev hfits hg hgpre h

end LeanFzn.Solver.UIP.LcgReachable
