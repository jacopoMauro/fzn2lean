/-
File: LeanFzn/Solver/UIP/Proofs/LcgDecideLive.lean

DL: `DecideLive` discharged from the kit. At a decide site the dispatcher found no conflict, in
particular no buildable wipe-out clause. On an integer box whose trail has no Boolean-atom
literal (`nbCfg_of_kit`) every emptied slot has a buildable wipe-out clause (each removed value has
a remover on the trail), so the frame has no empty domain.

`DecideLive` is FALSE without a nonempty box: for `orig = [[0], []]` the root frame has an empty
second domain, no wipe-out clause can be built (empty original domain) and the dispatcher decides
on slot 0. Hence the extra premise `hne : ∀ d ∈ orig, d ≠ []`.
-/
import LeanFzn.Solver.UIP.Proofs.LcgNoBoolRun
import LeanFzn.Solver.UIP.Proofs.LcgKitFinal
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgEvidence LeanFzn.Solver.UIP.LcgNoBool
open LeanFzn.Solver.UIP.LcgNoBoolTrail LeanFzn.Solver.UIP.LcgNoBoolRun LeanFzn.Solver.UIP.LcgKitFinal

namespace LeanFzn.Solver.UIP.LcgDecideLive

variable {leaf : Assignment → Bool}

/-! ## The wipe-out scan -/

theorem wipeoutScan_none_empty (orig : List Domain) (tr : List TrailEntry) :
    ∀ (ds : List Domain) (s0 : Nat), wipeoutScan orig tr ds s0 = none →
      ∀ i (hi : i < ds.length), ds[i] = [] → wipeoutClauseAt orig tr (s0 + i) = none := by
  intro ds
  induction ds with
  | nil => intro s0 _ i hi; simp at hi
  | cons d rest ih =>
      intro s0 h i hi hdi
      unfold wipeoutScan at h
      cases hh : (if d.isEmpty then wipeoutClauseAt orig tr s0 else none) with
      | some c => rw [hh] at h; cases h
      | none =>
          rw [hh] at h
          cases i with
          | zero =>
              have hd : d = [] := by simpa using hdi
              subst hd
              simpa [hh] using hh
          | succ i =>
              have := ih (s0 + 1) h i (by simpa using hi) (by simpa using hdi)
              have e : s0 + 1 + i = s0 + (i + 1) := by omega
              rw [e] at this
              exact this

theorem wipeoutClauseAt_ne_none {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    (hne : orig.getD s [] ≠ [])
    (hall : ∀ w ∈ orig.getD s [], (wipeRemover tr s w).isSome = true) :
    wipeoutClauseAt orig tr s ≠ none := by
  intro hnone
  unfold wipeoutClauseAt at hnone
  have hany : ((orig.getD s []).map (wipeRemover tr s)).any Option.isNone = false := by
    rw [Bool.eq_false_iff]
    intro hh
    obtain ⟨x, hx, hxn⟩ := List.any_eq_true.mp hh
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have := hall w hw
    cases hr : wipeRemover tr s w with
    | none => rw [hr] at this; simp at this
    | some q => rw [hr] at hxn; simp at hxn
  rw [if_neg (by rw [hany]; simp)] at hnone
  obtain ⟨w0, hw0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hall w0 hw0)
  have hqm : q ∈ (((orig.getD s []).map (wipeRemover tr s)).filterMap id).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨some q, List.mem_map.mpr ⟨w0, hw0, hq⟩, rfl⟩)
  generalize (((orig.getD s []).map (wipeRemover tr s)).filterMap id).eraseDups = ed at hnone hqm
  cases ed with
  | nil => cases hqm
  | cons a rest => cases hnone

theorem wipeRemover_isSome_of_int {tr : List TrailEntry} (hnb : NBTrail tr) {s : Nat} {k : Int}
    {e : TrailEntry} (he : e ∈ tr) (hs : e.literal.atom.slot = s)
    (hv : e.literal.valueHolds (Value.int k) = false) :
    (wipeRemover tr s (Value.int k)).isSome = true := by
  unfold wipeRemover
  rw [List.find?_isSome]
  refine ⟨e.literal.negate.norm, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
  have hnbl := hnb e he
  have h1 : e.literal.negate.norm.atom.slot = s := by
    rw [norm_atom_slot]; simpa [Literal.negate] using hs
  have h2 : e.literal.negate.norm.valueHolds (Value.int k) = true := by
    rw [norm_valueHolds, valueHolds_negate_int hnbl k, hv]; rfl
  simp [h1, h2]

/-- No empty remaining domain once the wipe-out scan found nothing. -/
theorem live_of_wipeNone {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hne : ∀ d ∈ orig, d ≠ []) (hJ : FrameJ orig tr F)
    (hS : FrameShape orig F) (hnb : NBTrail tr) (hw : wipeoutClause orig tr F = none) :
    ∀ d ∈ F.1, d ≠ [] := by
  intro d hd hdnil
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hscan := wipeoutScan_none_empty orig tr F.1 F.2.length hw i hi hdnil
  have hlen : (Frame.domains F).length = F.2.length + F.1.length := by
    simp [Frame.domains]
  have hslt : F.2.length + i < orig.length := by
    have := hS.1; omega
  have hgetD : orig.getD (F.2.length + i) [] = orig[F.2.length + i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hslt]; rfl
  have hne' : orig.getD (F.2.length + i) [] ≠ [] := by
    rw [hgetD]; exact hne _ (List.getElem_mem hslt)
  refine wipeoutClauseAt_ne_none hne' ?_ hscan
  intro w hwm
  obtain ⟨k, rfl⟩ := allInt_getD hint _ w hwm
  have hnot : Value.int k ∉ F.1.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [hdnil]
  obtain ⟨e, he, hes, hev⟩ := hJ.nc i _ hwm hnot
  exact wipeRemover_isSome_of_int hnb he hes hev

/-! ## The decide site -/

/-- At a decide site no wipe-out clause is buildable on the branch. -/
theorem decide_wipe_none {cfg : SchedulerConfig leaf}
    (hJ : FrameJ cfg.orig cfg.branch.trail cfg.branch.frame)
    (hdec : ∃ n m, schedulerNext cfg = .decide n m) :
    wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame = none := by
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
                rw [hev] at ht
                simp only at ht
                cases hw : wipeoutClause cfg.orig cfg.branch.trail cfg.branch.frame with
                | none => rfl
                | some w => rw [hw] at ht; cases ht
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

/-- **`DecideLive`, DERIVED** from the kit for a nonempty integer box: at every decide site of
a supported run the frame is live. (`hne` is necessary: see the file header.) -/
theorem decideLive_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) (hne : ∀ d ∈ orig, d ≠ []) :
    DecideLive orig original props leaf := by
  intro cfg hreach hdec
  have hS := lcgRunState_of_supportedRun K hreach
  have hor : cfg.orig = orig := SupportedReach.orig_eq hreach
  have hw := decide_wipe_none hS.frameRun.branch hdec
  have hnb := (nbCfg_of_kit K hreach).1
  have hsh := hS.frameRun.shape
  rw [hor] at hw hsh
  have hj := hS.frameRun.branch
  rw [hor] at hj
  exact live_of_wipeNone K.int hne hj hsh hnb hw

/-- **THE CONDITIONAL RUN INVARIANT, kit level, WITHOUT `hlive`** (nonempty integer box). -/
theorem lcgRunInvCond_of_kit_live {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) (hne : ∀ d ∈ orig, d ≠ []) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LcgRunInv' cfg :=
  lcgRunInvCond_of_kit K (decideLive_of_kit K hne)

/-! ## The nonempty-box premise is necessary -/

/-- Local helper: the transition is a decision. -/
def isDecideB {leaf : Assignment → Bool} : SchedulerTransition leaf → Bool
  | .decide _ _ => true
  | _ => false

/-- **COUNTEREXAMPLE to `DecideLive` without `hne`**: on the box `[[0], []]` (second slot empty,
no propagators, no clauses) the root dispatcher decides on slot 0 although the frame has an empty
domain. -/
theorem not_decideLive_empty_domain :
    ¬ DecideLive (leaf := fun _ => false) [[Value.int 0], []] [] [] := by
  intro h
  have hreach : SupportedReach (leaf := fun _ => false) [[Value.int 0], []] [] []
      (SchedulerConfig.init [[Value.int 0], []] [] []) :=
    SupportedReach.init (fun c hc => by cases hc)
  have hb : isDecideB (schedulerNext (SchedulerConfig.init (leaf := fun _ => false)
      [[Value.int 0], []] [] [])) = true := by decide +kernel
  have hdec : ∃ n m, schedulerNext (SchedulerConfig.init (leaf := fun _ => false)
      [[Value.int 0], []] [] []) = .decide n m := by
    cases hn : schedulerNext (SchedulerConfig.init (leaf := fun _ => false)
        [[Value.int 0], []] [] []) with
    | decide n m => exact ⟨n, m, rfl⟩
    | sat _ => rw [hn] at hb; cases hb
    | unsat => rw [hn] at hb; cases hb
    | propagate _ => rw [hn] at hb; cases hb
    | analyzeConflict _ _ => rw [hn] at hb; cases hb
    | localExclude _ => rw [hn] at hb; cases hb
    | chronologicalFallback _ => rw [hn] at hb; cases hb
    | learnBackjumpAssert _ => rw [hn] at hb; cases hb
  exact (h hreach hdec [] (by simp [SchedulerConfig.init, BranchState.init])) rfl

end LeanFzn.Solver.UIP.LcgDecideLive
