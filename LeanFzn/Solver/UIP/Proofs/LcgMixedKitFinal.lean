/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedKitFinal.lean
A4b: the mixed `LcgKitFinal`.
Part 1 delivers the mechanical twins of the kit-level theorems of `LcgKitFinal`
(`frameRun_of_kit`, `frameExplainedFull_of_kit`, `trailSnapFixed_of_kit`,
`trailRun_of_kit`, `runSemContract_of_kit`, `lcgKit_gate_of_kit`,
`lcgRunInvCond_of_kit`) under `MixedLcgKit`/`LcgMixedRunState`.
Part 2 generalizes the closure chain (`literalImpossible_of_sem`,
`dbSemUnfalsified_of_stableScan`, `closure_at_decide`) from `AllIntBox orig` to
`ShapeTypedDomains orig` and feeds it into `lcgRunInvCond_of_kit_mixed`.
The integer declarations are untouched.
DAG: LcgMixedRunStep + LcgRunInvariantFinal + LcgKitFinal -> LcgMixedKitFinal.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal
import LeanFzn.Solver.UIP.Proofs.LcgKitFinal
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedRunStep LeanFzn.Solver.UIP.LcgEvidence

namespace LeanFzn.Solver.UIP.LcgMixedKitFinal

variable {leaf : Assignment → Bool}

section
variable {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}

/-- `MixedFrameRun` along a supported run of the mixed kit (twin of
`frameRun_of_kit`; the Boolean prefix pins are part of the mixed run bundle). -/
theorem frameRun_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    MixedFrameRun cfg :=
  (lcgMixedRunState_of_supportedRun K hreach).frameRun

/-- `FrameExplainedFull` along a supported run of the mixed kit (twin of
`frameExplainedFull_of_kit`; via `MixedFrameRun.frameExplained`). -/
theorem frameExplainedFull_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    FrameExplainedFull orig cfg.branch := by
  have h := (frameRun_of_kit_mixed K hreach).frameExplained
    (by rw [SupportedReach.orig_eq hreach]; exact K.shape)
  rw [SupportedReach.orig_eq hreach] at h
  exact h

/-- `TrailSnapFixed` along a supported run of the mixed kit (twin of
`trailSnapFixed_of_kit`). -/
theorem trailSnapFixed_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    TrailSnapFixed orig cfg.branch.trail := fun e he =>
  snapLit_fixed_of_norm_pool ((lcgMixedRunState_of_supportedRun K hreach).core.voc e he)

/-- `TrailRun` along a supported run of the mixed kit (twin of `trailRun_of_kit`). -/
theorem trailRun_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    TrailRun cfg where
  branch := by
    rw [(lcgMixedRunState_of_supportedRun K hreach).core.orig_eq]
    exact (lcgMixedRunState_of_supportedRun K hreach).core.reach.trail_sem
  cps := fun cp hcp => by
    have h := (lcgMixedRunState_of_supportedRun K hreach).core.snaps cp hcp
    rw [(lcgMixedRunState_of_supportedRun K hreach).core.orig_eq]
    obtain ⟨bs, hbs, -, htr, -⟩ := h
    rw [← htr]
    exact hbs.trail_sem

/-- `RunSemContract` from the mixed kit (twin of `runSemContract_of_kit`). -/
theorem runSemContract_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props) :
    RunSemContract orig original props leaf :=
  runSemContract_of_families (dcs := dcs) (by rw [K.props_eq, K.raw_eq]) K.fam
    (fun hr => frameExplainedFull_of_kit_mixed K hr)
    (fun hr => trailSnapFixed_of_kit_mixed K hr)

/-- The `lcgKit` gate from the mixed kit (twin of `lcgKit_gate_of_kit`). -/
theorem lcgKit_gate_of_kit_mixed (K : MixedLcgKit leaf orig original dcs raw props) :
    (lcgKit lcgFamB).Gate leaf orig original props :=
  lcgKit_gate_of_families (dcs := dcs) (by rw [K.props_eq, K.raw_eq]) K.fam
    (fun hr => frameExplainedFull_of_kit_mixed K hr)
    (fun hr => trailSnapFixed_of_kit_mixed K hr)

end

/-! ## Part 2: the shape closure chain (`AllIntBox` -> `ShapeTypedDomains`) -/

section ShapeClosure
variable {orig : List Domain} {original : List Clause}

/-- The completed implication relation never changes the slot. -/
theorem impliesP_slot {orig : List Domain} {t g : Literal}
    (h : impliesP orig t g = true) : t.atom.slot = g.atom.slot := by
  rcases impliesP_cases h with h | h
  · unfold impliesBase at h
    rcases Bool.or_eq_true_iff.mp h with heq | h2
    · rw [litEqB_iff.mp heq]
    · obtain ⟨-, hil⟩ := Bool.and_eq_true_iff.mp h2
      rw [← intForm_slot t, ← intForm_slot g]
      exact impliesLit_slot hil
  · exact (boolSlotImp_elim h).1

/-- The order form of a literal agrees with it on Boolean values. -/
theorem intForm_valueHolds_bool (l : Literal) (c : Bool) :
    l.intForm.valueHolds (.bool c) = l.valueHolds (.bool c) := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b =>
      cases b <;> cases pos <;> cases c <;>
        simp [Literal.valueHolds, Literal.intForm, Literal.negate, posLe, negLe, Value.intView]
  | intLe s u =>
      cases pos <;> cases c <;> simp [Literal.valueHolds, Literal.intForm, Value.intView]
  | intNe s u =>
      cases pos <;> cases c <;> simp [Literal.valueHolds, Literal.intForm, Value.intView]

/-- A Boolean truth-table step of the completed implication, read on values. -/
theorem valueHolds_of_impliesP_bool {orig : List Domain} {t g : Literal} {b : Bool}
    (h : impliesP orig t g = true)
    (hmem : Value.bool b ∈ orig.getD t.atom.slot [])
    (ht : t.valueHolds (.bool b) = true) : g.valueHolds (.bool b) = true := by
  have hslot : t.atom.slot = g.atom.slot := impliesP_slot h
  rcases impliesP_cases h with h | h
  · unfold impliesBase at h
    rcases Bool.or_eq_true_iff.mp h with heq | h2
    · rwa [litEqB_iff.mp heq] at ht
    · obtain ⟨-, hil⟩ := Bool.and_eq_true_iff.mp h2
      have hs : t.atom.slot < orig.length := lt_of_mem_getD hmem
      have ha : ((orig.map fun _ => Value.bool b).set t.atom.slot (.bool b))[t.atom.slot]?
          = some (.bool b) := List.getElem?_set_self (by rw [List.length_map]; exact hs)
      have hti : t.intForm.eval ((orig.map fun _ => Value.bool b).set t.atom.slot (.bool b))
          = some true :=
        Literal.intForm_eval ((valueHolds_read ha).mp ht)
      have hgi : g.intForm.eval ((orig.map fun _ => Value.bool b).set t.atom.slot (.bool b))
          = some true := impliesLit_sound hil hti
      have hai : ((orig.map fun _ => Value.bool b).set t.atom.slot (.bool b))[g.intForm.atom.slot]?
          = some (.bool b) := by rw [intForm_slot, ← hslot]; exact ha
      have hgv : g.intForm.valueHolds (.bool b) = true := (valueHolds_read hai).mpr hgi
      rwa [intForm_valueHolds_bool] at hgv
  · obtain ⟨-, -, htab⟩ := boolSlotImp_elim h
    have hs : slotHasBool orig t.atom.slot b = true := slotHasBool_of_mem hmem
    have htb : t.truthAtBool b = true := by rwa [valueHolds_bool] at ht
    have hgb : g.truthAtBool b = true := htab b hs htb
    rwa [valueHolds_bool]

/-- A literal semantically refuted by a single trail entry is impossible on a shape-typed
frame (integer twin: `literalImpossible_of_sem`; integer slots replay it verbatim, Boolean
slots use the complete truth table of `impliesP`). -/
theorem literalImpossible_of_sem_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig tr F) {q : Literal} {e : TrailEntry}
    (he : e ∈ tr) (himp : impliesP orig e.literal q.negate.norm = true) :
    literalImpossible F q = true := by
  unfold literalImpossible
  rw [List.all_eq_true]
  intro v hv
  have hmemO := hJ.fits _ v hv
  rcases slot_cases hshape q.atom.slot with hi | hb
  · obtain ⟨k, rfl⟩ := hi v hmemO
    obtain ⟨atom, pos⟩ := q
    cases atom with
    | boolEq s b => simp [Literal.valueHolds]
    | intLe s u =>
        have hg : ∀ s' b, (Literal.norm (Literal.negate ⟨Atom.intLe s u, pos⟩)).atom ≠ Atom.boolEq s' b := by
          intro s' b hb; cases pos <;> simp [Literal.norm, Literal.negate] at hb
        have hnb := intSlot_slotBoolB_false hmemO hi
        have ht := not_boolEq_of_impliesP hg (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
        have hs := impliesP_slot_int ht hg himp
        have hag := hJ.agree _ e he (by simpa [Literal.norm, Literal.negate, Atom.slot] using hs)
          (Value.int k) hv
        have hbase := impliesP_base_of_target_nonBoolean
          (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
        have hsound := impliesBase_sound_value hg hbase hag
        rw [norm_valueHolds, valueHolds_negate_int (fun s b => by simp)] at hsound
        simpa using hsound
    | intNe s u =>
        have hg : ∀ s' b, (Literal.norm (Literal.negate ⟨Atom.intNe s u, pos⟩)).atom ≠ Atom.boolEq s' b := by
          intro s' b hb; cases pos <;> simp [Literal.norm, Literal.negate] at hb
        have hnb := intSlot_slotBoolB_false hmemO hi
        have ht := not_boolEq_of_impliesP hg (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
        have hs := impliesP_slot_int ht hg himp
        have hag := hJ.agree _ e he (by simpa [Literal.norm, Literal.negate, Atom.slot] using hs)
          (Value.int k) hv
        have hbase := impliesP_base_of_target_nonBoolean
          (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
        have hsound := impliesBase_sound_value hg hbase hag
        rw [norm_valueHolds, valueHolds_negate_int (fun s b => by simp)] at hsound
        simpa using hsound
  · obtain ⟨b0, rfl⟩ := hb v hmemO
    have hslot : e.literal.atom.slot = (q.negate.norm).atom.slot := impliesP_slot himp
    have hslotq : (q.negate.norm).atom.slot = q.atom.slot := by
      obtain ⟨atom, pos⟩ := q
      cases atom <;> cases pos <;> rfl
    have hag := hJ.agree q.atom.slot e he (by rw [hslot, hslotq]) (Value.bool b0) hv
    have hmem' : Value.bool b0 ∈ orig.getD e.literal.atom.slot [] := by
      rw [hslot, hslotq]; exact hmemO
    have hgtrue : (q.negate.norm).valueHolds (Value.bool b0) = true :=
      valueHolds_of_impliesP_bool himp hmem' hag
    rw [valueHolds_bool]
    rw [valueHolds_bool, truthAtBool_negate_norm] at hgtrue
    cases hh : q.truthAtBool b0 <;> simp_all

/-- **Closure from a stable database scan, shape-typed**: twin of
`dbSemUnfalsified_of_stableScan` with `literalImpossible_of_sem_shape`. -/
theorem dbSemUnfalsified_of_stableScan_shape {orig : List Domain} {original : List Clause}
    {bs : BranchState leaf} (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig bs.trail bs.frame)
    (hstable : scanDatabase original bs.frame bs.learned = .stable) : DbSemUnfalsified orig bs := by
  intro c hc hfals
  refine scanDatabase_stable_clauseRemaining hstable c hc ?_
  unfold clauseRemaining
  rw [List.filter_eq_nil_iff]
  intro q hq hfilt
  obtain ⟨e, he, himp⟩ := hfals q hq
  have := literalImpossible_of_sem_shape hshape hJ he himp
  rw [this] at hfilt
  simp at hfilt

/-- **`ClosureRun` from decide-site liveness, shape-typed**: twin of `closure_at_decide`;
its only integer use is the stable-scan closure, everything else is sort-agnostic. -/
theorem closure_at_decide_shape {cfg : SchedulerConfig leaf} (hshape : ShapeTypedDomains cfg.orig)
    (hJ : FrameJ cfg.orig cfg.branch.trail cfg.branch.frame)
    (hlive : ∀ d ∈ cfg.branch.frame.1, d ≠ [])
    (hdec : ∃ n m, schedulerNext cfg = .decide n m) : DbSemUnfalsified cfg.orig cfg.branch := by
  obtain ⟨n, m, hdec⟩ := hdec
  cases hc : cfg.conflict with
  | some ev =>
      rw [C2d.schedulerNext_eq_backjump hc] at hdec
      exact absurd hdec (backjumpStep_ne_decide _ _ _ _)
  | none =>
    cases hs : cfg.status with
    | dead =>
        rw [C2d.schedulerNext_eq_consume hc hs] at hdec
        exact absurd hdec (consumeStep_ne_decide _ _ _)
    | active =>
      cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
      | some d =>
          rw [C2d.schedulerNext_eq_deduction hc hs hd] at hdec
          cases hdec
      | none =>
        cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
        | conflict bs cs learned =>
            simp only [schedulerNext, hc, hs, hd, ht] at hdec
            unfold conflictStep at hdec
            split at hdec
            · cases hdec
            · split at hdec <;> cases hdec
        | localExcluded bs lit reason learned =>
            simp only [schedulerNext, hc, hs, hd, ht] at hdec
            cases hdec
        | stable bs =>
            unfold terminalResult at ht
            cases hev : nextPruningEvent cfg.original cfg.props cfg.branch.frame
                cfg.branch.learned with
            | conflict cs => rw [hev] at ht; cases ht
            | stable =>
                unfold nextPruningEvent at hev
                cases hdb : scanDatabase cfg.original cfg.branch.frame cfg.branch.learned with
                | stable => exact dbSemUnfalsified_of_stableScan_shape hshape hJ hdb
                | conflict cs => rw [hdb] at hev; cases hev
                | implied l c lr fl =>
                    rw [hdb] at hev
                    simp only at hev
                    rw [if_pos (frameLiveB_of_live hlive)] at hev
                    cases hev
            | implied l c lr fl =>
                exfalso
                have hprod := nextPruningEvent_implied_productive hev
                rw [hev] at ht
                simp only at ht
                cases hf : filterFrame l cfg.branch.frame with
                | none => rw [hf] at ht; cases ht
                | some g =>
                    unfold explainedDeduction at hd
                    rw [hev] at hd
                    simp only at hd
                    cases hr : TrailRedundant cfg.branch.trail l with
                    | true =>
                        rw [productive_false_of_redundant hJ hr] at hprod
                        cases hprod
                    | false =>
                        rw [hr] at hd
                        simp only at hd
                        split at hd
                        · rename_i heq; rw [hf] at heq; cases heq
                        · rename_i g' hg'
                          rw [hf] at hg'
                          cases hg'
                          split at hd
                          · cases hd
                          · rename_i hnm
                            unfold productive at hprod
                            rw [hf] at hprod
                            simp only [decide_eq_true_eq] at hprod
                            exact hnm hprod

/-- **THE CONDITIONAL RUN INVARIANT, MIXED KIT LEVEL**: twin of `lcgRunInvCond_of_kit`
with the shape-typed closure (`closure_at_decide_shape`); the `LcgMixedRunState` bundle
supplies `reasons`/`wipe` and the Boolean pins. -/
theorem lcgRunInvCond_of_kit_mixed {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LcgRunInv' cfg := by
  intro cfg hreach
  have hS := lcgMixedRunState_of_supportedRun K hreach
  have hor : cfg.orig = orig := SupportedReach.orig_eq hreach
  exact
    { entailed := hS.core.reach.learned_ent
      reasons := (trailRun_of_kit_mixed K hreach).branch
      evidence := fun ev an h1 h2 => evidenceRunCond_holds orig original props leaf hreach ev h1 an h2
      wipe := wipeoutOk_of_fits K.fits cfg hor
      closure := fun hdec =>
        closure_at_decide_shape (by rw [hor]; exact K.shape) hS.frameRun.branch (hlive hreach hdec) hdec }

end ShapeClosure
end LeanFzn.Solver.UIP.LcgMixedKitFinal
