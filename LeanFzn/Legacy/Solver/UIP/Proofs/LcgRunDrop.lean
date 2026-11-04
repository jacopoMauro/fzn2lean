/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunDrop.lean
H2f: the arm lemmas of the stack-soundness invariant `StackSound` / `DeadSound` / `CpSound`
(definitions in `LcgRunDropDef`), all over `LcgReachableState`/`LcgGood`, no `hbr`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunCert
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunDropDef
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgRunArms LeanFzn.Solver.UIP.LcgRunConflict

namespace LeanFzn.Solver.UIP.LcgRunDrop

variable {leaf : Assignment → Bool}

/-! ## Semantic pivot -/

theorem semFalsifiedBefore_not_true {orig : List Domain} {tr : List TrailEntry} {q : Literal}
    {a : Assignment} (h : SemFalsifiedBefore orig tr q) (hfit : a.Fits orig)
    (htr : ∀ e ∈ tr, e.literal.eval a = some true) : q.eval a ≠ some true := by
  intro hq
  rcases h with h | ⟨e, he, himp⟩
  · exact litFalseAtRoot_sound h hfit hq
  · have := impliesP_negate_sound himp hfit hq
    rw [htr e he] at this
    cases this

theorem pivot_true {orig : List Domain} {tr : List TrailEntry} {l : Literal} {c : Clause}
    {a : Assignment} (hs : SemReasonOK orig tr l c) (hfit : a.Fits orig)
    (htr : ∀ e ∈ tr, e.literal.eval a = some true)
    (hsat : ∃ q ∈ c, q.eval a = some true) : l.norm.eval a = some true := by
  obtain ⟨q, hq, hqe⟩ := hsat
  by_cases hpq : litEqB q.norm l.norm = true
  · have hqq := litEqB_iff.mp hpq
    rw [← hqq, Literal.norm_eval]
    exact hqe
  · exfalso
    have hpq' : litEqB q.norm l.norm = false := by simpa using hpq
    exact semFalsifiedBefore_not_true (hs.2 q hq hpq') hfit htr hqe

/-! ## Propagation -/

theorem propagate_covers {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs)
    {d : ProductiveDeduction leaf bs} (hd : explainedDeduction original props bs = some d) :
    ∀ a, leaf a = true → FrameCovers bs.frame a → FrameCovers d.frame a := by
  intro a ha hcv
  obtain ⟨hent, -, hsem⟩ := lcgEvent_of_kit_at (original := original) K.raw_eq K.props_eq
    K.fam K.int K.fits K.contract hg.reach hg.frameState d hd
  have hsat := hent d.reason (List.mem_singleton_self _) a ha
  have h1 := pivot_true hsem (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv) hsat
  rw [norm_norm, Literal.norm_eval] at h1
  obtain ⟨g, hgf, hcv'⟩ := filterFrame_preserves hcv h1
  have hg' : g = d.frame := Option.some.inj (hgf.symm.trans d.filtered)
  rw [← hg']
  exact hcv'

/-! ## Split / skip -/

theorem pinsAgree_pin_parent {B : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hB : B.doms[k]?.map Dom.enum = some (v :: vs.enum)) {a : Assignment}
    (h : Frame.PinsAgree (B.pin k v) a) : Frame.PinsAgree B a := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons hB
  intro j w hj
  by_cases hjk : j = k
  · subst j
    rw [hB] at hj
    have hEq : v :: vs.enum = [w] := Option.some.inj hj
    have hwv : w = v := ((List.cons.injEq v vs.enum w []).mp hEq).1.symm
    have hpin : (B.pin k v).doms[k]?.map Dom.enum = some [v] := by
      rw [BranchFrame.pin_doms, List.getElem?_set_self (List.getElem?_eq_some_iff.mp hd).1]
      simp
    have hread := h k v hpin
    rwa [hwv]
  · have hset : (B.pin k v).doms[j]?.map Dom.enum = some [w] := by
      rw [BranchFrame.pin_doms, getElem?_set_of_ne hjk]
      exact hj
    exact h j w hset

theorem pinsAgree_retire_parent {B : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hB : B.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hvs : vs.enum ≠ []) {a : Assignment}
    (h : Frame.PinsAgree (B.retire k vs) a) : Frame.PinsAgree B a := by
  intro j w hj
  by_cases hjk : j = k
  · subst j
    rw [hB] at hj
    have hEq : v :: vs.enum = [w] := Option.some.inj hj
    have hvs' : vs.enum = [] := ((List.cons.injEq v vs.enum w []).mp hEq).2
    exact absurd hvs' hvs
  · have hset : (B.retire k vs).doms[j]?.map Dom.enum = some [w] := by
      rw [BranchFrame.retire_doms, getElem?_set_of_ne hjk]
      exact hj
    exact h j w hset

theorem frameSnd_child {B : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hB : B.doms[k]?.map Dom.enum = some (v :: vs.enum)) (h : FrameSndOrder leaf B) :
    FrameSndOrder leaf (B.pin k v) := by
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons hB
  have hklt : k < B.doms.length := (List.getElem?_eq_some_iff.mp hd).1
  intro a ha hp
  have hpB : Frame.PinsOnOrder B a := by
    intro j hj w hjw
    by_cases hjk : j = k
    · subst j
      rw [hB] at hjw
      have hEq : v :: vs.enum = [w] := Option.some.inj hjw
      have hwv : w = v := ((List.cons.injEq v vs.enum w []).mp hEq).1.symm
      have hpin : (B.pin k v).doms[k]?.map Dom.enum = some [v] := by
        rw [BranchFrame.pin_doms, List.getElem?_set_self hklt]
        simp
      have hkpin : k ∈ (B.pin k v).order := by simp [BranchFrame.pin_order]
      have hread : a[k]? = some v := hp k hkpin v hpin
      rw [hread, ← hwv]
    · have hpin : (B.pin k v).doms[j]?.map Dom.enum = some [w] := by
        rw [BranchFrame.pin_doms, getElem?_set_of_ne hjk]
        exact hjw
      have hjpin : j ∈ (B.pin k v).order := by simp [BranchFrame.pin_order, hj]
      exact hp j hjpin w hpin
  have hc := h a ha hpB
  have hpin : (B.pin k v).doms[k]?.map Dom.enum = some [v] := by
    rw [BranchFrame.pin_doms, List.getElem?_set_self hklt]
    simp
  have hkpin : k ∈ (B.pin k v).order := by simp [BranchFrame.pin_order]
  have hread : a[k]? = some v := hp k hkpin v hpin
  have hmem := SparseFrame.mem_allAssigns_set_of_mem hc hread
    ((mem_ofList_iff v [v]).mpr (List.mem_singleton.mpr rfl))
  simpa [FrameCovers, BranchFrame.pin_doms] using hmem

theorem frameSnd_sibling_covers {B : BranchFrame} {k : Nat} {v : Value} {vs : Domain}
    (hB : B.doms[k]?.map Dom.enum = some (v :: vs.enum)) (hvs : vs.enum ≠ [])
    (h : FrameSndOrder leaf B) :
    ∀ a, leaf a = true → Frame.PinsOnOrder (B.retire k vs) a →
      ¬ FrameCovers (B.retire k vs) a → FrameCovers (B.pin k v) a := by
  intro a ha hp hn
  have hpB : Frame.PinsOnOrder B a := by
    intro j hj w hjw
    by_cases hjk : j = k
    · subst j
      rw [hB] at hjw
      have hEq : v :: vs.enum = [w] := Option.some.inj hjw
      exact absurd ((List.cons.injEq v vs.enum w []).mp hEq).2 hvs
    · have hret : (B.retire k vs).doms[j]?.map Dom.enum = some [w] := by
        rw [BranchFrame.retire_doms, getElem?_set_of_ne hjk]
        exact hjw
      exact hp j hj w hret
  have hc := h a ha hpB
  rcases (covers_split_at hB a).mp hc with h1 | h1
  · exact h1
  · exact absurd h1 hn

theorem skip_covers {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hs : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (cfg.branch.frame.pin k v) a := by
  obtain ⟨i, hv, hl, hpin⟩ := lcgPinFits_int hs hreach hint
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  obtain ⟨d, hd, hde⟩ := exists_dom_of_enum_cons ((splitData_eq_some_iff.mp hs).2.1)
  intro a ha hcov
  have h1 : (l.norm).eval a = some true := by
    have h3 := hreach.agrees e he a hcov
    rwa [hil] at h3
  have hread := (hpin a (hfits a ha)).mp h1
  exact (SparseFrame.Frame.covers_pin_iff hd
    ((DomainLike.mem_iff d v).mpr (by
      rw [domElems_eq_enum, hde]
      exact List.mem_cons_self)) a).mpr ⟨hcov, hread⟩


/-! ## The propagation closure -/

theorem closure_frameSnd {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs) (hs : FrameSndOrder leaf bs.frame) :
    FrameSndOrder leaf (explainedClosure orig original props bs).frame := by
  have := explainedClosure_induction orig original props
    (fun b => LcgGood leaf orig b ∧ FrameSndOrder leaf b.frame)
    (fun b d hd h => by
      refine ⟨h.1.stepNarrowSync K hd, ?_⟩
      rw [stepNarrowSync_frame]
      intro a ha hp
      have hp' : Frame.PinsOnOrder b.frame a := by
        intro j hj w hjw
        have hjd : j ∈ (d.frame).order := by
          rw [Frame.filterFrame_order d.filtered]
          exact hj
        exact hp j hjd w (filterFrame_singleton d.filtered hjw)
      exact propagate_covers K h.1 hd a ha (h.2 a ha hp')) bs ⟨hg, hs⟩
  exact this.2

/-! ## Dead sites -/

theorem terminal_conflict_dead {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs s : BranchState leaf} (hg : LcgGood leaf orig bs) {cs learned : List Clause}
    (ht : terminalResult orig original props bs = .conflict s cs learned) :
    ∀ a, leaf a = true → ¬ FrameCovers bs.frame a := by
  intro a ha hcv
  obtain ⟨-, h⟩ := terminalResult_conflict_cases ht
  rcases h with ⟨hev, -⟩ | ⟨l, c, lr, fl, hev, hnone, hcs, -⟩ | ⟨w, hev, hw, hcs, -⟩
  · rcases nextPruningEvent_conflict_cases hev with hdb | ⟨-, hview, hprop⟩
    · obtain ⟨c, hmem, hunit, -⟩ := scanDatabase_conflict_facts hdb
      exact clauseRemaining_empty_excludes hcv hunit (hg.reach.learned_ent c hmem a ha)
    · obtain ⟨p, hpm, c, hrun, -⟩ := scanPropagators_conflict_facts hprop
      rw [K.props_eq] at hpm
      obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
      obtain ⟨c0, hrun0, -⟩ := clamp_run_conflict hrun
      exact K.contract.conflict bs.frame hview p0 hp0 c0 hrun0 a ha hcv
  · have hP : ∀ p ∈ props, PropSemContract orig p bs :=
      propSem_of_state K.raw_eq K.props_eq K.fam
        (frameExplainedFull_of_explDoms K.int hg.fj.expl) hg.frameState.snap
    have hsem := nextPruningEvent_implied_sem K.int hg.fj hg.fs hP hev
    have hent := implied_reason_entailed K hg.reach hev
    have h1 := pivot_true hsem (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv)
      (hent c (List.mem_singleton_self _) a ha)
    rw [Literal.norm_eval] at h1
    obtain ⟨g, hgf, -⟩ := filterFrame_preserves hcv h1
    rw [hnone] at hgf
    cases hgf
  · exact wipeoutClause_excludes hw (K.fits a ha) (fun e he => hg.reach.agrees e he a hcv)

theorem stableNone_dead_lcg {orig : List Domain} {cfg : SchedulerConfig leaf}
    (hint : AllIntBox orig) (hr : LcgReachableState leaf orig cfg.branch)
    (hwit : leafWitness leaf cfg = none) (hsp : splitData cfg.branch.frame cfg.prio = none) :
    ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a := by
  intro a ha hcv
  refine stableNone_dead hwit hsp ?_ a ha hcv
  rintro ⟨k, v, vs, hslots, hnone⟩
  have hmem : v ∈ (fullDomains cfg.branch.frame).getD k Dom.empty := by
    show v ∈ (cfg.branch.frame.doms.getD k Dom.empty)
    exact (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum, enum_getD_of_enum_cons hslots]
      exact List.mem_cons_self)
  have hfit := hr.full_fits _ _ hmem
  obtain ⟨i, rfl⟩ := allInt_getD hint _ v ((DomainLike.mem_iff _ v).mp hfit)
  simp [valueLiteral] at hnone


/-! ## Arm bundles -/

/-- The three H2f fields of `LcgRunState`, as one predicate. -/
def DropInv (cfg : SchedulerConfig leaf) : Prop := StackSound cfg ∧ DeadSound cfg ∧ CpSound cfg

theorem deadSound_active {cfg : SchedulerConfig leaf} (hs : cfg.status = .active)
    (hc : cfg.conflict = none) : DeadSound cfg := by
  rintro (h | h)
  · rw [hs] at h; cases h
  · exact absurd hc h

theorem dropInv_stay {cfg cfg' : SchedulerConfig leaf} (h : DropInv cfg)
    (hf : cfg'.branch.frame = cfg.branch.frame) (hp : cfg'.pending = cfg.pending)
    (hc : cfg'.checkpoints = cfg.checkpoints)
    (hd : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a) : DropInv cfg' := by
  refine ⟨?_, fun _ => by rw [hf]; exact hd, ?_⟩
  · unfold StackSound; rw [hf, hp]; exact h.1
  · unfold CpSound; rw [hc]; exact h.2.2

/-- An active step that replaces the head frame (propagate, skip, jump). -/
theorem dropInv_replace {cfg cfg' : SchedulerConfig leaf} (h : DropInv cfg)
    (hp : cfg'.pending = cfg.pending)
    (hc : ∀ cp ∈ cfg'.checkpoints, cp ∈ cfg.checkpoints)
    (hB' : FrameSndOrder leaf cfg'.branch.frame)
    (hcov : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers cfg'.branch.frame a)
    (hs : cfg'.status = .active) (hcn : cfg'.conflict = none) : DropInv cfg' := by
  refine ⟨?_, deadSound_active hs hcn, fun cp hcp => h.2.2 cp (hc cp hcp)⟩
  unfold StackSound; rw [hp]
  exact stackSound_replace_head h.1 hB' hcov

theorem dropInv_decide {cfg : SchedulerConfig leaf} (h : DropInv cfg)
    {k : Nat} {v : Value} {vs : Domain} {l : Literal}
    (hB : cfg.branch.frame.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hvs : vs.enum ≠ [])
    (hconf : cfg.conflict = none) :
    DropInv (stepDecide cfg k v vs l) := by
  have hsnd := frameSnd_of_head h.1
  refine ⟨?_, deadSound_active rfl (by rw [stepDecide_conflict, hconf]), ?_⟩
  · exact stackSound_split (C := cfg.branch.frame.pin k v)
      (S := cfg.branch.frame.retire k vs) h.1 (frameSnd_child hB hsnd)
      (frameSnd_sibling_covers hB hvs hsnd)
      (fun a => (covers_split_at hB a).mp)
  · intro cp hcp
    change cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · exact hsnd
    · exact h.2.2 cp hcp

theorem dropInv_skip {cfg : SchedulerConfig leaf} (h : DropInv cfg)
    {k : Nat} {v : Value} {vs : Domain}
    (hB : cfg.branch.frame.doms[k]?.map Dom.enum = some (v :: vs.enum))
    (hcov : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (cfg.branch.frame.pin k v) a)
    (hconf : cfg.conflict = none) : DropInv (stepDecideSkip cfg k v) :=
  dropInv_replace h rfl (fun cp hcp => hcp) (frameSnd_child hB (frameSnd_of_head h.1))
    hcov rfl (by rw [stepDecideSkip_conflict, hconf])

/-- Consume: the canonical level-0 falsifiers of the resumed pending frame hold at every leaf
solution (the dead head covers none, so the resumed frame holds every solution of its prefix). -/
theorem consume_falsifiers {orig : List Domain} {B f : BranchFrame} {rest : List BranchFrame}
    (hst : StackSoundFrom leaf (fun _ => False) (B :: f :: rest))
    (hdead : ∀ a, leaf a = true → ¬ FrameCovers B a) (hpb : PendingBacked orig f) :
    ∀ e ∈ canonicalFalsifiers orig f, e.level = 0 →
      ∀ a, leaf a = true → e.literal.eval a = some true := by
  have hsnd : FrameSndOrder leaf f := by
    intro a ha hp
    refine Classical.byContradiction fun hn => ?_
    rcases hst.2.1 a ha hp hn with hu | hu
    · exact hu
    · exact hdead a ha hu
  intro e he hl a ha
  have hlev : f.level = 0 := by
    rw [← canonicalFalsifiers_level he]
    exact hl
  have hnil : f.order = [] := List.length_eq_zero_iff.mp (by
    simpa [BranchFrame.level] using hlev)
  have hpins : Frame.PinsOnOrder f a := by
    intro k hk
    rw [hnil] at hk
    cases hk
  exact agrees_canonicalFalsifiers hpb.shape hpb.fit hpb.full_len e he a
    (hsnd a ha hpins)

theorem dropInv_consume {cfg next : SchedulerConfig leaf} (h : DropInv cfg)
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest)
    (hdead : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a)
    (hb : next.branch.frame = f) (hpn : next.pending = rest)
    (hck : next.checkpoints = []) (hs : next.status = .active) (hcn : next.conflict = none) :
    DropInv next := by
  refine ⟨?_, deadSound_active hs hcn, ?_⟩
  · unfold StackSound; rw [hb, hpn]
    have h1 : StackSoundFrom leaf (fun _ => False) (cfg.branch.frame :: cfg.pending) := h.1
    rw [hp] at h1
    exact stackSound_consume h1 hdead
  · intro cp hcp; rw [hck] at hcp; cases hcp

end LeanFzn.Solver.UIP.LcgRunDrop
