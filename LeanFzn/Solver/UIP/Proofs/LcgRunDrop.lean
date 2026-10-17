/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunDrop.lean
H2f: the arm lemmas of the stack-soundness invariant `StackSound` / `DeadSound` / `CpSound`
(definitions in `LcgRunDropDef`), all over `LcgReachableState`/`LcgGood`, no `hbr`.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunCert
import LeanFzn.Solver.UIP.Proofs.LcgRunDropDef
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

theorem cover_sibling_prefix {p : List Value} {v : Value} {vs : Domain} {doms : List Domain}
    {a : Assignment} (hc : FrameCovers (vs :: doms, p) a) (hp : (p ++ [v]) <+: a) :
    FrameCovers (doms, p ++ [v]) a := by
  obtain ⟨tail, ht, rfl⟩ := hc
  cases vs with
  | nil => simp [allAssigns] at ht
  | cons u us =>
      obtain ⟨w, hw, suffix, hs, rfl⟩ := (mem_allAssigns_singleton u us doms tail).mp ht
      have h1 : [v] <+: w :: suffix := (List.prefix_append_right_inj p).mp
        (by simpa using hp)
      have hwv : w = v := by
        obtain ⟨t, ht⟩ := h1
        simp at ht
        exact ht.1.symm
      subst hwv
      exact ⟨suffix, hs, by simp⟩

theorem frameSnd_child {B : BranchFrame} {v : Value} {vs : Domain} {doms : List Domain}
    (hB : B.1 = (v :: vs) :: doms) (h : FrameSnd leaf B) :
    FrameSnd leaf (doms, B.2 ++ [v]) := by
  intro a ha hp
  have hp' : B.2 <+: a := (List.prefix_append _ _).trans hp
  have hc := h a ha hp'
  have hBe : B = ((v :: vs) :: doms, B.2) := Prod.ext hB rfl
  rw [hBe] at hc
  rcases (covers_split v vs doms B.2 a).mp hc with h1 | h1
  · exact h1
  · exact cover_sibling_prefix h1 hp

theorem frameSnd_sibling_covers {B : BranchFrame} {v : Value} {vs : Domain} {doms : List Domain}
    (hB : B.1 = (v :: vs) :: doms) (h : FrameSnd leaf B) :
    ∀ a, leaf a = true → (vs :: doms, B.2).2 <+: a → ¬ FrameCovers (vs :: doms, B.2) a →
      FrameCovers (doms, B.2 ++ [v]) a := by
  intro a ha hp hn
  have hc := h a ha hp
  have hBe : B = ((v :: vs) :: doms, B.2) := Prod.ext hB rfl
  rw [hBe] at hc
  rcases (covers_split v vs doms B.2 a).mp hc with h1 | h1
  · exact h1
  · exact absurd h1 hn

theorem skip_covers {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}
    (hreach : LcgReachableState leaf orig cfg.branch) (hint : AllIntBox orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a := by
  obtain ⟨i, hv, hl, hpin⟩ := lcgPinFits_int hs hreach hint
  obtain ⟨e, he, hil⟩ := trailRedundant_iff.mp hred
  have hslots := (splitData_eq_some_iff.mp hs).1
  intro a ha hcov
  have h1 : (l.norm).eval a = some true := by
    have h3 := hreach.agrees e he a hcov
    rwa [hil] at h3
  have hslot := (hpin a (hfits a ha)).mp h1
  obtain ⟨tail, htail, heq⟩ := hcov
  have htail' : tail ∈ allAssigns ((v :: vs) :: doms) := by
    rwa [← hslots]
  obtain ⟨w, hw, suffix, hsuffix, rfl⟩ := (mem_allAssigns_singleton v vs doms tail).mp htail'
  have hwv : w = v := by
    have hget : (cfg.branch.frame.2 ++ (w :: suffix))[cfg.branch.frame.2.length]? = some w := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [heq, hget] at hslot
    exact Option.some.inj hslot
  subst hwv
  refine ⟨suffix, hsuffix, ?_⟩
  rw [heq]
  simp only [List.append_assoc, List.singleton_append]


/-! ## The propagation closure -/

theorem closure_frameSnd {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {bs : BranchState leaf} (hg : LcgGood leaf orig bs) (hs : FrameSnd leaf bs.frame) :
    FrameSnd leaf (explainedClosure orig original props bs).frame := by
  have := explainedClosure_induction orig original props
    (fun b => LcgGood leaf orig b ∧ FrameSnd leaf b.frame)
    (fun b d hd h => by
      refine ⟨h.1.stepNarrowSync K hd, ?_⟩
      rw [stepNarrowSync_frame]
      intro a ha hp
      have hpre : d.frame.2 = b.frame.2 := filterFrame_prefix d.filtered
      rw [hpre] at hp
      exact propagate_covers K h.1 hd a ha (h.2 a ha hp)) bs ⟨hg, hs⟩
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
    (hwit : leafWitness leaf cfg = none) (hsp : splitData cfg.branch.frame = none) :
    ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a := by
  intro a ha hcv
  refine stableNone_dead hwit hsp ?_ a ha hcv
  rintro ⟨v, vs, doms, hslots, hnone⟩
  have hmem : v ∈ (fullDomains cfg.branch.frame).getD cfg.branch.frame.2.length [] := by
    rw [List.getD_eq_getElem?_getD]
    have hfr := fullDomains_remaining (f := cfg.branch.frame) (i := 0)
    rw [Nat.add_zero, hslots] at hfr
    rw [hfr]
    simp
  have hfit := hr.full_fits _ _ hmem
  obtain ⟨k, rfl⟩ := allInt_getD hint _ v hfit
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
    (hB' : FrameSnd leaf cfg'.branch.frame)
    (hcov : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers cfg'.branch.frame a)
    (hs : cfg'.status = .active) (hcn : cfg'.conflict = none) : DropInv cfg' := by
  refine ⟨?_, deadSound_active hs hcn, fun cp hcp => h.2.2 cp (hc cp hcp)⟩
  unfold StackSound; rw [hp]
  exact stackSound_replace_head h.1 hB' hcov

theorem dropInv_decide {cfg : SchedulerConfig leaf} (h : DropInv cfg)
    {v : Value} {vs : Domain} {doms : List Domain} {l : Literal}
    (hB : cfg.branch.frame.1 = (v :: vs) :: doms) (hconf : cfg.conflict = none) :
    DropInv (stepDecide cfg v vs doms l) := by
  have hsnd := frameSnd_of_head h.1
  have hBe : cfg.branch.frame = ((v :: vs) :: doms, cfg.branch.frame.2) := Prod.ext hB rfl
  refine ⟨?_, deadSound_active rfl (by rw [stepDecide_conflict, hconf]), ?_⟩
  · have := stackSound_split (C := (doms, cfg.branch.frame.2 ++ [v]))
      (S := (vs :: doms, cfg.branch.frame.2)) h.1 (frameSnd_child hB hsnd)
      (frameSnd_sibling_covers hB hsnd)
      (fun a ha => by
        rw [hBe] at ha
        exact (covers_split v vs doms _ a).mp ha)
    exact this
  · intro cp hcp
    change cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · exact hsnd
    · exact h.2.2 cp hcp

theorem dropInv_skip {cfg : SchedulerConfig leaf} (h : DropInv cfg)
    {v : Value} {vs : Domain} {doms : List Domain}
    (hB : cfg.branch.frame.1 = (v :: vs) :: doms)
    (hcov : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      FrameCovers (doms, cfg.branch.frame.2 ++ [v]) a)
    (hconf : cfg.conflict = none) : DropInv (stepDecideSkip cfg v doms) :=
  dropInv_replace h rfl (fun cp hcp => hcp) (frameSnd_child hB (frameSnd_of_head h.1))
    hcov rfl (by rw [stepDecideSkip_conflict, hconf])

/-- Consume: the canonical level-0 falsifiers of the resumed pending frame hold at every leaf
solution (the dead head covers none, so the resumed frame holds every solution of its prefix). -/
theorem consume_falsifiers {orig : List Domain} {B f : BranchFrame} {rest : List BranchFrame}
    (hst : StackSoundFrom leaf (fun _ => False) (B :: f :: rest))
    (hdead : ∀ a, leaf a = true → ¬ FrameCovers B a) (hpb : PendingBacked orig f) :
    ∀ e ∈ canonicalFalsifiers orig f, e.level = 0 →
      ∀ a, leaf a = true → e.literal.eval a = some true := by
  intro e he hl a ha
  have hlen : f.2.length = 0 := by rw [← canonicalFalsifiers_level he]; exact hl
  have hnil : f.2 = [] := List.length_eq_zero_iff.mp hlen
  have hcov : FrameCovers f a := by
    refine Classical.byContradiction fun hn => ?_
    rcases hst.2.1 a ha (by rw [hnil]; exact List.nil_prefix) hn with hu | hu
    · exact hu
    · exact hdead a ha hu
  exact agrees_canonicalFalsifiers hpb.shape hpb.fit hpb.full_len e he a hcov

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
