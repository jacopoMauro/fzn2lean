/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantFinal.lean
U1c: the wipe-out field, and the assembled run invariant with the exact residual premises.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantTrailStep
import LeanFzn.Solver.UIP.Proofs.DatabaseUnfalsified
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

theorem wipeoutScan_some (orig : List Domain) (tr : List TrailEntry) :
    ∀ (ds : List Domain) (s0 : Nat) {w : Clause},
      wipeoutScan orig tr ds s0 = some w → ∃ s, wipeoutClauseAt orig tr s = some w := by
  intro ds
  induction ds with
  | nil => intro s0 w h; simp [wipeoutScan] at h
  | cons d rest ih =>
      intro s0 w h
      unfold wipeoutScan at h
      cases hh : (if d.isEmpty then wipeoutClauseAt orig tr s0 else none) with
      | some c =>
          rw [hh] at h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨s0, ?_⟩
          by_cases hd : d.isEmpty = true
          · rw [if_pos hd] at hh; exact hh
          · rw [if_neg hd] at hh; cases hh
      | none => rw [hh] at h; exact ih (s0 + 1) h

/-- **The wipe-out field of the run invariant** (no run premise beyond leaf-fits). -/
theorem wipeoutOk_of_fits (hfit : ∀ a, leaf a = true → a.Fits orig) (cfg : SchedulerConfig leaf)
    (hor : cfg.orig = orig) : WipeoutOk cfg := by
  intro w hw
  unfold wipeoutClause at hw
  obtain ⟨s, hs⟩ := wipeoutScan_some cfg.orig cfg.branch.trail cfg.branch.frame.1
    cfg.branch.frame.2.length hw
  obtain ⟨hne, hc, hany⟩ := wipeoutClauseAt_eq hs
  have hmemw : ∀ q ∈ w, ∃ v ∈ cfg.orig.getD s [], wipeRemover cfg.branch.trail s v = some q := by
    intro q hq
    rw [hc] at hq
    obtain ⟨r, hr, hrq⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp hq)
    obtain ⟨v, hv, hvr⟩ := List.mem_map.mp hr
    exact ⟨v, hv, by rw [hvr]; simpa using hrq⟩
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨v, -, hv⟩ := hmemw q hq
    obtain ⟨⟨e, he, rfl⟩, -, -⟩ := wipeRemover_spec hv
    refine Or.inr ⟨e, he, ?_⟩
    rw [negate_norm_negate_norm]
    exact impliesP_self_norm _ _
  · intro c hc' a hleaf
    rw [List.mem_singleton] at hc'
    rw [hc']
    have hfa := hfit a hleaf
    rw [← hor] at hfa
    -- the slot is inside the box
    obtain ⟨q0, hq0⟩ : ∃ q0, q0 ∈ w := by
      cases w with
      | nil => exact absurd rfl hne
      | cons q rest => exact ⟨q, List.mem_cons_self⟩
    obtain ⟨v0, hv0, -⟩ := hmemw q0 hq0
    have hslt : s < cfg.orig.length := lt_of_mem_getD hv0
    have hlen : a.length = cfg.orig.length := hfa.1
    have hsa : s < a.length := by omega
    have hget : a[s]? = some a[s] := List.getElem?_eq_getElem hsa
    have hmem : a[s] ∈ cfg.orig.getD s [] := hfa.2 s _ hget
    -- the remover of the value `a[s]`
    have hnn : wipeRemover cfg.branch.trail s a[s] ≠ none := by
      intro hn
      have : ((cfg.orig.getD s []).map (wipeRemover cfg.branch.trail s)).any Option.isNone = true :=
        List.any_eq_true.mpr ⟨none, List.mem_map.mpr ⟨a[s], hmem, hn⟩, rfl⟩
      rw [hany] at this; cases this
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hnn
    obtain ⟨-, hqs, hqv⟩ := wipeRemover_spec hq
    refine ⟨q, ?_, ?_⟩
    · rw [hc]
      exact List.mem_eraseDups.mpr (List.mem_filterMap.mpr
        ⟨some q, List.mem_map.mpr ⟨a[s], hmem, hq⟩, rfl⟩)
    · exact (valueHolds_read (by rw [hqs]; exact hget)).mp hqv

/-! ## The assembled run invariant with its exact residual premises -/

/-- Residual premise 1 (U1d + propagator reason validity): the learned database is globally
entailed along the run. -/
def EntailedRun (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    LearnedEntailed leaf cfg.branch.learned

/-- Residual premise 2: recorded conflict clauses are semantically falsified.  **REFUTED**
(`evidence_refuted`); kept only so that the failure is a named, checkable statement.  The
analyser-level contract that remains true is "analysis success implies falsified". -/
def EvidenceRun (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ∀ ev, cfg.conflict = some ev → ClauseSemFalsifiedR cfg.orig cfg.branch.trail ev.clause

/-- A slot with an integer value in `orig` is not Boolean-only (R3 guard is off). -/
theorem slotBoolB_false_of_int {orig : List Domain} {s : Nat} {k : Int}
    (h : Value.int k ∈ orig.getD s []) : slotBoolB orig s = false := by
  unfold slotBoolB
  rw [List.all_eq_false]
  exact ⟨_, h, by simp⟩

/-- Integer arithmetic soundness of the syntactic base relation. -/
theorem impliesBase_sound_value {orig : List Domain} {t g : Literal} {k : Int}
    (hg : ∀ s b, g.atom ≠ Atom.boolEq s b)
    (h : impliesBase orig t g = true) (hv : t.valueHolds (.int k) = true) :
    g.valueHolds (.int k) = true := by
  have ht := not_boolEq_of_holds hv
  obtain ⟨ta, tp⟩ := t
  obtain ⟨ga, gp⟩ := g
  cases ta with
  | boolEq s b => exact absurd rfl (ht s b)
  | intLe s1 u1 =>
    cases ga with
    | boolEq s b => exact absurd rfl (hg s b)
    | intLe s2 u2 =>
      cases tp <;> cases gp <;>
        simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Literal.valueHolds, Value.intView] <;> omega
    | intNe s2 u2 =>
      cases tp <;> cases gp <;>
        simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Literal.valueHolds, Value.intView] <;> omega
  | intNe s1 u1 =>
    cases ga with
    | boolEq s b => exact absurd rfl (hg s b)
    | intLe s2 u2 =>
      cases tp <;> cases gp <;>
        simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Literal.valueHolds, Value.intView] <;> omega
    | intNe s2 u2 =>
      cases tp <;> cases gp <;>
        simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Literal.valueHolds, Value.intView] <;> omega

theorem impliesP_slot_int {orig : List Domain} {t g : Literal} (ht : ∀ s b, t.atom ≠ Atom.boolEq s b)
    (hg : ∀ s b, g.atom ≠ Atom.boolEq s b) (h : impliesP orig t g = true) :
    t.atom.slot = g.atom.slot := by
  rcases impliesP_cases h with h | h
  ·
    obtain ⟨ta, tp⟩ := t
    obtain ⟨ga, gp⟩ := g
    cases ta with
    | boolEq s b => exact absurd rfl (ht s b)
    | intLe s1 u1 =>
      cases ga with
      | boolEq s b => exact absurd rfl (hg s b)
      | intLe s2 u2 =>
        cases tp <;> cases gp <;>
          simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Atom.slot] <;>
            (try (rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1))
      | intNe s2 u2 =>
        cases tp <;> cases gp <;>
          simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Atom.slot] <;>
            (try (rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1))
    | intNe s1 u1 =>
      cases ga with
      | boolEq s b => exact absurd rfl (hg s b)
      | intLe s2 u2 =>
        cases tp <;> cases gp <;>
          simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Atom.slot] <;>
            (try (rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1))
      | intNe s2 u2 =>
        cases tp <;> cases gp <;>
          simp_all [impliesBase, impliesLit, litEqB, Literal.intForm, Literal.boolKind, Atom.slot] <;>
            (try (rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1))
  · exact (boolSlotImp_elim h).1

theorem intForm_slot (t : Literal) : t.intForm.atom.slot = t.atom.slot := by
  obtain ⟨a, p⟩ := t
  cases a <;> cases p <;> (try cases ‹Bool›) <;> simp [Literal.intForm, Atom.slot, Literal.negate, posLe, negLe]

theorem impliesLit_slot {t g : Literal} (h : impliesLit t g = true) :
    t.atom.slot = g.atom.slot := by
  unfold impliesLit at h
  split at h
  · rename_i hl
    have := litEqB_iff.mp hl
    subst this; rfl
  · split at h
    · simp at h
    · rename_i hne
      simpa [bne_iff_ne] using hne

/-- A Boolean-only trail literal (on slot `s`) cannot imply an integer literal on a slot that
is not Boolean-only in `orig` (the R3 guard in `impliesP`). -/
theorem not_boolEq_of_impliesP {orig : List Domain} {t g : Literal}
    (hg : ∀ s b, g.atom ≠ Atom.boolEq s b) (hnb : slotBoolB orig g.atom.slot = false)
    (h : impliesP orig t g = true) : ∀ s b, t.atom ≠ Atom.boolEq s b := by
  have h := impliesP_base_of_target_nonBoolean hnb h
  intro s b hb
  obtain ⟨ta, tp⟩ := t
  simp only at hb
  subst hb
  have hgk : g.boolKind = false := by
    obtain ⟨ga, gp⟩ := g
    cases ga with
    | boolEq s' b' => exact absurd rfl (hg s' b')
    | _ => rfl
  unfold impliesBase at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨hg', h⟩
  · obtain ⟨ga, gp⟩ := g
    cases ga with
    | boolEq s' b' => exact absurd rfl (hg s' b')
    | _ => simp [litEqB] at h
  · have hsl := impliesLit_slot h
    rw [intForm_slot, intForm_slot] at hsl
    have hs : s = g.atom.slot := by simpa [Atom.slot] using hsl
    rw [← hs] at hnb
    have hg'' : slotBoolB orig s = true := by
      rcases hg' with (h1 | h1) | h1
      · simp [Literal.boolKind] at h1
      · rw [hgk] at h1; cases h1
      · exact h1
    rw [hg''] at hnb
    cases hnb

/-- A literal semantically refuted by a single trail entry is impossible on the frame. -/
theorem literalImpossible_of_sem {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hJ : FrameJ orig tr F) {q : Literal} {e : TrailEntry}
    (he : e ∈ tr) (himp : impliesP orig e.literal q.negate.norm = true) :
    literalImpossible F q = true := by
  unfold literalImpossible
  rw [List.all_eq_true]
  intro v hv
  have hmemO := hJ.fits _ v hv
  obtain ⟨k, rfl⟩ := allInt_getD hint _ v hmemO
  obtain ⟨atom, pos⟩ := q
  cases atom with
  | boolEq s b => simp [Literal.valueHolds]
  | intLe s u =>
      have hg : ∀ s' b, (Literal.norm (Literal.negate ⟨Atom.intLe s u, pos⟩)).atom ≠ Atom.boolEq s' b := by
        intro s' b hb; cases pos <;> simp [Literal.norm, Literal.negate] at hb
      have hnb := slotBoolB_false_of_int hmemO
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
      have hnb := slotBoolB_false_of_int hmemO
      have ht := not_boolEq_of_impliesP hg (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
      have hs := impliesP_slot_int ht hg himp
      have hag := hJ.agree _ e he (by simpa [Literal.norm, Literal.negate, Atom.slot] using hs)
        (Value.int k) hv
      have hbase := impliesP_base_of_target_nonBoolean
        (by simpa [Literal.norm, Literal.negate, Atom.slot] using hnb) himp
      have hsound := impliesBase_sound_value hg hbase hag
      rw [norm_valueHolds, valueHolds_negate_int (fun s b => by simp)] at hsound
      simpa using hsound

/-- **Closure from a stable database scan**: if the scan of the stored clauses is stable, no
stored clause is semantically falsified by the trail. -/
theorem dbSemUnfalsified_of_stableScan {orig : List Domain} {original : List Clause}
    {bs : BranchState leaf} (hint : AllIntBox orig) (hJ : FrameJ orig bs.trail bs.frame)
    (hstable : scanDatabase original bs.frame bs.learned = .stable) : DbSemUnfalsified orig bs := by
  intro c hc hfals
  refine scanDatabase_stable_clauseRemaining hstable c hc ?_
  unfold clauseRemaining
  rw [List.filter_eq_nil_iff]
  intro q hq hfilt
  obtain ⟨e, he, himp⟩ := hfals q hq
  have := literalImpossible_of_sem hint hJ he himp
  rw [this] at hfilt
  simp at hfilt

/-! ## Closure at a decide step -/

theorem backjumpStep_ne_decide (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (n : SchedulerConfig leaf) (m : Literal) : backjumpStep cfg ev ≠ .decide n m := by
  intro h
  unfold backjumpStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h <;> cases h

theorem consumeStep_ne_decide (cfg : SchedulerConfig leaf)
    (n : SchedulerConfig leaf) (m : Literal) : consumeStep cfg ≠ .decide n m := by
  intro h
  unfold consumeStep at h
  split at h <;> cases h

theorem nextPruningEvent_implied_productive {original : List Clause} {props : List Propagator}
    {f : BranchFrame} {db : List Clause} {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props f db = .implied l c lr fl) : productive l f = true := by
  unfold nextPruningEvent at h
  have hdb : ∀ {db' : List Clause} {l' : Literal} {c' : Clause} {lr' fl' : Bool},
      scanDatabase original f db' = .implied l' c' lr' fl' → productive l' f = true := by
    intro db'
    induction db' with
    | nil => intro l' c' lr' fl' h'; simp [scanDatabase] at h'
    | cons c0 rest ih =>
        intro l' c' lr' fl' h'
        unfold scanDatabase at h'
        cases hr : clauseRemaining f c0 with
        | nil => rw [hr] at h'; simp at h'
        | cons a tl =>
            rw [hr] at h'
            cases tl with
            | nil =>
                simp only at h'
                by_cases hp : productive a f = true
                · rw [if_pos hp] at h'
                  simp only [PruningEvent.implied.injEq] at h'
                  obtain ⟨rfl, -, -, -⟩ := h'
                  exact hp
                · rw [if_neg hp] at h'; exact ih h'
            | cons b tl' => simp only at h'; exact ih h'
  have hpr : ∀ {ps : List Propagator} {l' : Literal} {c' : Clause} {lr' fl' : Bool},
      scanPropagators f ps = .implied l' c' lr' fl' → productive l' f = true := by
    intro ps
    induction ps with
    | nil => intro l' c' lr' fl' h'; simp [scanPropagators] at h'
    | cons p rest ih =>
        intro l' c' lr' fl' h'
        unfold scanPropagators at h'
        cases hrun : p.run (frameState f) with
        | stable => rw [hrun] at h'; exact ih h'
        | conflict cc => rw [hrun] at h'; simp at h'
        | implied l'' r =>
            rw [hrun] at h'
            simp only at h'
            by_cases hp : productive l'' f = true
            · rw [if_pos hp] at h'
              simp only [PruningEvent.implied.injEq] at h'
              obtain ⟨rfl, -, -, -⟩ := h'
              exact hp
            · rw [if_neg hp] at h'; exact ih h'
  cases hd : scanDatabase original f db with
  | stable =>
      rw [hd] at h
      by_cases hv : frameViewedB f = true
      · rw [if_pos hv] at h; exact hpr h
      · rw [if_neg hv] at h; cases h
  | conflict cs => rw [hd] at h; cases h
  | implied l' c' lr' fl' =>
      rw [hd] at h
      simp only at h
      by_cases hl : frameLiveB f = true
      · rw [if_pos hl] at h
        simp only [PruningEvent.implied.injEq] at h
        obtain ⟨rfl, -, -, -⟩ := h
        exact hdb hd
      · rw [if_neg hl] at h; cases h

theorem filterFrame_self_of_holds {l : Literal} {F : BranchFrame}
    (h : ∀ v ∈ (Frame.domains F).getD l.atom.slot [], l.valueHolds v = true) :
    filterFrame l F = some F := by
  unfold filterFrame
  by_cases hlt : l.atom.slot < F.2.length
  · rw [if_pos hlt]
    have hv := h F.2[l.atom.slot] (by rw [domains_getD_pre F hlt]; exact List.mem_cons_self)
    have : l.eval F.2 = some true :=
      (valueHolds_read (l := l) (a := F.2) (v := F.2[l.atom.slot])
        (List.getElem?_eq_getElem hlt)).mp hv
    simp [this]
  · rw [if_neg hlt]
    have hid : filterSlots l F.2.length F.1 = F.1 := by
      apply filterSlots_id
      intro i d hi hoff
      have hle : F.2.length ≤ l.atom.slot := by omega
      have hidx : l.atom.slot - F.2.length = i := by omega
      have hdg : (Frame.domains F).getD l.atom.slot [] = d :=
        domains_getD_remaining F hle (by rw [hidx]; exact hi)
      rw [List.all_eq_true]
      intro v hv
      exact h v (by rw [hdg]; exact hv)
    rw [hid]

theorem productive_false_of_redundant {orig : List Domain} {tr : List TrailEntry}
    {F : BranchFrame} (hJ : FrameJ orig tr F) {l : Literal}
    (hred : TrailRedundant tr l = true) : productive l F = false := by
  obtain ⟨e, he, hel⟩ := trailRedundant_iff.mp hred
  have hag : ∀ v ∈ (Frame.domains F).getD l.atom.slot [], l.valueHolds v = true := by
    intro v hv
    have := hJ.agree l.atom.slot e he (by rw [hel, norm_atom_slot]) v hv
    rwa [hel, norm_valueHolds] at this
  unfold productive
  rw [filterFrame_self_of_holds hag]
  simp

theorem frameLiveB_of_live {F : BranchFrame} (h : ∀ d ∈ F.1, d ≠ []) : frameLiveB F = true := by
  unfold frameLiveB
  rw [List.all_eq_true]
  intro d hd
  cases d with
  | nil => exact absurd rfl (h _ hd)
  | cons a rest => rfl

/-- **`ClosureRun` from decide-site liveness**: at a decide step of a live integer frame no
stored clause is semantically falsified by the trail. -/
theorem closure_at_decide {cfg : SchedulerConfig leaf} (hint : AllIntBox cfg.orig)
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
                | stable => exact dbSemUnfalsified_of_stableScan hint hJ hdb
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

/-- Residual premise 3 (replaces the old closure premise): decide sites of the run are on live
frames (every remaining domain nonempty).  Needed because the wipe-out route can only be shown
to fire for an emptied slot when the removing trail literals are integer atoms. -/
def DecideLive (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    (∃ n m, schedulerNext cfg = .decide n m) → ∀ d ∈ cfg.branch.frame.1, d ≠ []

/-- **(3) THE RUN INVARIANT**: `reasons`, `wipe` and `closure` are proved (integer box, clamped
family kit; `closure` from decide-site liveness); `entailed`, `evidence` and the jump premise
`AssertingSem` are the named residuals (`evidence` is refuted: `evidenceRun_refuted`). 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem lcgRunInv_of_residual {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hfit : ∀ a, leaf a = true → a.Fits orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hA : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → AssertingSem cfg)
    (hent : EntailedRun orig original props leaf)
    (hev : EvidenceRun orig original props leaf)
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LcgRunInv cfg := by
  intro cfg hreach
  have hT := trailRun_of_supportedRun hraw hprops hfam hint hnd htyped horig hbr hA hreach
  have hF := frameRun_of_supportedRun hint hnd (shape_of_allInt hint) hbr hreach
  have hor : cfg.orig = orig := SupportedReach.orig_eq hreach
  exact
    { entailed := hent hreach
      reasons := hT.branch
      evidence := hev hreach
      wipe := wipeoutOk_of_fits hfit cfg hor
      closure := fun hdec =>
        closure_at_decide (by rw [hor]; exact hint) hF.branch (hlive hreach hdec) hdec }

end LeanFzn.Solver.UIP.LcgRunInv
