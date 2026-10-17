/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantReasons.lean
U1c (3): `TrailSem` (the semantic reason contract of every trail entry) along supported runs.

Sections: R0 literal algebra; R1 synchronisation entries are semantically justified by
construction (their reasons are negations of earlier trail literals); R2 frame-falsity to
semantic falsification (integer boxes); R3 event contract; R4 closure; R5 arms.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantGate
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-! ## R0 literal algebra -/

theorem impliesP_self_norm (orig : List Domain) (t : Literal) : impliesP orig t t.norm = true := by
  obtain ⟨atom, pos⟩ := t
  cases atom with
  | boolEq s b =>
      cases pos <;> cases b <;>
        simp [impliesP, impliesBase, impliesLit, litEqB, Literal.norm, Literal.intForm, Literal.boolKind,
          posLe, negLe, Literal.negate]
  | intLe s k => cases pos <;> simp [impliesP, impliesBase, litEqB, Literal.norm]
  | intNe s k => cases pos <;> simp [impliesP, impliesBase, litEqB, Literal.norm]

theorem negate_norm_negate_norm (l : Literal) : l.negate.norm.negate.norm = l.norm := by
  obtain ⟨atom, pos⟩ := l
  cases atom <;> cases pos <;> simp [Literal.norm, Literal.negate]

theorem semFalsified_of_negation {orig : List Domain} {tr : List TrailEntry} {e : TrailEntry}
    (he : e ∈ tr) : SemFalsifiedBefore orig tr e.literal.negate :=
  Or.inr ⟨e, he, by rw [Literal.negate_negate]; exact impliesP_self_norm _ _⟩

theorem semReasonOK_norm {orig : List Domain} {tr : List TrailEntry} {l : Literal} {c : Clause}
    (h : SemReasonOK orig tr l c) : SemReasonOK orig tr l.norm c := by
  refine ⟨by rw [Literal.norm_idem]; exact h.1, fun q hq hne => h.2 q hq ?_⟩
  rw [Literal.norm_idem] at hne; exact hne

/-! ## R1 synchronisation entries -/

theorem syncOne_trailSem {orig : List Domain} (bs : BranchState leaf) (lit : Literal)
    (h : TrailSem orig bs.trail) : TrailSem orig (syncOne orig bs lit).trail := by
  unfold syncOne
  cases hc : syncClause orig bs lit with
  | none => exact h
  | some c =>
      obtain ⟨d, ex, -, -, -, -, -, hx, rfl⟩ := syncClause_spec hc
      simp only [narrowState]
      refine h.snoc (fun r hr => ?_)
      have : r = { clause := lit.norm :: ex } := (Option.some.inj hr).symm
      subst this
      refine ⟨by simp [Literal.norm_idem], fun q hq hne => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd hne (by simp [litEqB])
      · obtain ⟨e, he, rfl⟩ := (syncExplain_spec hx).1 q hq
        exact semFalsified_of_negation he

theorem syncSlot_trailSem {orig : List Domain} (bs : BranchState leaf) (s : Nat)
    (h : TrailSem orig bs.trail) : TrailSem orig (syncSlot orig bs s).trail := by
  unfold syncSlot
  exact foldl_syncOne_inv (orig := orig) (P := fun b => TrailSem orig b.trail)
    (fun b lit hb => syncOne_trailSem b lit hb) _ _ h

theorem syncAll_trailSem {orig : List Domain} (bs : BranchState leaf)
    (h : TrailSem orig bs.trail) : TrailSem orig (syncAll orig bs).trail := by
  unfold syncAll
  exact foldl_range_inv (orig := orig) (P := fun b => TrailSem orig b.trail) _
    (fun b i hb => syncSlot_trailSem b _ hb) _ _ h

/-! ## R2 frame falsity is semantic falsity (integer boxes) -/

theorem impliesP_negLe_posNe {orig : List Domain} {t : Literal} {s : Nat} {m k : Int}
    (h : impliesP orig t (negLe s m) = true) (hk : k ≤ m) : impliesP orig t (posNe s k) = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
      simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB,
      posNe, negLe, posLe, Literal.negate] at h ⊢ <;> simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, posNe, negLe] at this ⊢ <;> omega

theorem impliesP_posLe_posNe {orig : List Domain} {t : Literal} {s : Nat} {m k : Int}
    (h : impliesP orig t (posLe s m) = true) (hk : m < k) : impliesP orig t (posNe s k) = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
      simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB,
      posNe, negLe, posLe, Literal.negate] at h ⊢ <;> simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, posNe, posLe] at this ⊢ <;> omega

theorem sf_posLe_to_negNe {orig : List Domain} {tr : List TrailEntry} {s : Nat} {m k : Int}
    (h : SemFalsifiedBefore orig tr (posLe s m)) (hk : k ≤ m) :
    SemFalsifiedBefore orig tr (negNe s k) := by
  rcases h with h | ⟨e, he, hi⟩
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr fun v hv => ?_)
    have h' := (litFalseAtRoot_iff orig _).mp h v hv
    cases hiv : v.intView with
    | none => simp [Literal.valueHolds, negNe, hiv]
    | some a =>
        simp [Literal.valueHolds, posLe, negNe, hiv] at h' ⊢
        omega
  · exact Or.inr ⟨e, he, impliesP_negLe_posNe (m := m) (by simpa [posLe, negLe, Literal.negate, Literal.norm] using hi) hk⟩

theorem sf_negLe_to_negNe {orig : List Domain} {tr : List TrailEntry} {s : Nat} {m k : Int}
    (h : SemFalsifiedBefore orig tr (negLe s m)) (hk : m < k) :
    SemFalsifiedBefore orig tr (negNe s k) := by
  rcases h with h | ⟨e, he, hi⟩
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr fun v hv => ?_)
    have h' := (litFalseAtRoot_iff orig _).mp h v hv
    cases hiv : v.intView with
    | none => simp [Literal.valueHolds, negNe, hiv]
    | some a =>
        simp [Literal.valueHolds, negLe, negNe, hiv] at h' ⊢
        omega
  · exact Or.inr ⟨e, he, impliesP_posLe_posNe (m := m) (by simpa [posLe, negLe, Literal.negate, Literal.norm] using hi) hk⟩

theorem list_eq_singleton_of_nodup {α : Type} {D : List α} {x : α} (hx : x ∈ D)
    (hnd : D.Nodup) (hall : ∀ y ∈ D, y = x) : D = [x] := by
  cases D with
  | nil => cases hx
  | cons a rest =>
      have ha : a = x := hall a List.mem_cons_self
      subst ha
      have : rest = [] := by
        cases rest with
        | nil => rfl
        | cons b rest' =>
            exfalso
            have hb : b = a := hall b (List.mem_cons_of_mem _ List.mem_cons_self)
            subst hb
            exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
      rw [this]

theorem domains_getD_ne_nil {F : BranchFrame} (hlive : ∀ d ∈ F.1, d ≠ []) {s : Nat}
    (hs : s < (Frame.domains F).length) : (Frame.domains F).getD s [] ≠ [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
  simp only [Option.getD_some]
  have hmem := List.getElem_mem hs
  simp only [Frame.domains, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨x, -, hx⟩ | hmem
  · intro hnil
    have : (Frame.domains F)[s] = [x] := hx.symm
    rw [this] at hnil
    cases hnil
  · exact hlive _ hmem

theorem domains_getD_nodup {F : BranchFrame} (hnd : ∀ d ∈ F.1, d.Nodup) (s : Nat) :
    ((Frame.domains F).getD s []).Nodup := by
  by_cases hs : s < F.2.length
  · rw [domains_getD_pre F hs]; simp
  · rw [domains_getD_rem F (by omega), List.getD_eq_getElem?_getD]
    cases hh : F.1[s - F.2.length]? with
    | none => simp
    | some d => exact hnd d (List.mem_of_getElem? hh)

/-- **Frame falsity is semantic falsity**: a literal impossible on every value of its slot's
frame domain is semantically falsified by the trail (live integer frames). -/
theorem frameFalse_sem {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hJ : FrameJ orig tr F) (hS : FrameShape orig F)
    (hlive : ∀ d ∈ F.1, d ≠ []) {q : Literal}
    (himp : ((Frame.domains F).getD q.atom.slot []).all (fun v => !q.valueHolds v) = true) :
    SemFalsifiedBefore orig tr q := by
  have hfalse : ∀ v ∈ (Frame.domains F).getD q.atom.slot [], q.valueHolds v = false := by
    intro v hv
    have := List.all_eq_true.mp himp v hv
    simpa using this
  by_cases hD : (Frame.domains F).getD q.atom.slot [] = []
  · -- the slot is outside the box: root-false vacuously
    have hs : ¬ q.atom.slot < (Frame.domains F).length := fun hlt =>
      domains_getD_ne_nil hlive hlt hD
    refine Or.inl ((litFalseAtRoot_iff orig q).mpr fun v hv => ?_)
    exfalso
    have : orig.length ≤ q.atom.slot := by rw [← hS.1]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none this] at hv
    simp at hv
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ (Frame.domains F).getD q.atom.slot [] := by
      cases hh : (Frame.domains F).getD q.atom.slot [] with
      | nil => exact absurd hh hD
      | cons a rest => exact ⟨a, by simp⟩
    have hints : ∀ v ∈ (Frame.domains F).getD q.atom.slot [], ∃ k : Int, v = Value.int k :=
      fun v hv => allInt_getD hint _ v (hJ.fits _ v hv)
    obtain ⟨k0, rfl⟩ := hints x hx
    obtain ⟨atom, pos⟩ := q
    simp only [Atom.slot] at hfalse hx hints hD ⊢
    have hE := hJ.expl
    cases atom with
    | boolEq s b => exact Or.inl (litFalseAtRoot_boolEq_int hint s b pos)
    | intLe s k =>
        cases pos with
        | true =>
            obtain ⟨mn, hmn⟩ := domMinI_exists hx rfl
            obtain ⟨⟨x1, hx1, hx1v⟩, -⟩ := domMinI_spec hmn
            obtain ⟨k1, rfl⟩ := hints x1 hx1
            have hk1 : k1 = mn := by simpa [Value.intView] using hx1v
            subst hk1
            have := hfalse _ hx1
            simp [Literal.valueHolds, Value.intView] at this
            exact sf_posLe_mono ((hE s).1.2 k1 hmn) (by omega)
        | false =>
            obtain ⟨mx, hmx⟩ := domMaxI_exists hx rfl
            obtain ⟨⟨x2, hx2, hx2v⟩, -⟩ := domMaxI_spec hmx
            obtain ⟨k2, rfl⟩ := hints x2 hx2
            have hk2 : k2 = mx := by simpa [Value.intView] using hx2v
            subst hk2
            have := hfalse _ hx2
            simp [Literal.valueHolds, Value.intView] at this
            exact sf_negLe_mono ((hE s).1.1 k2 hmx) (by omega)
    | intNe s k =>
        cases pos with
        | true =>
            have hall : ∀ y ∈ (Frame.domains F).getD s [], y = Value.int k := by
              intro y hy
              obtain ⟨k', rfl⟩ := hints y hy
              have := hfalse _ hy
              simp [Literal.valueHolds, Value.intView] at this
              rw [this]
            have hxk : Value.int k0 = Value.int k := hall _ hx
            rw [hxk] at hx
            have hD1 : (Frame.domains F).getD s [] = [Value.int k] :=
              list_eq_singleton_of_nodup hx (domains_getD_nodup hS.2 s) hall
            exact (hE s).2.1 k hD1
        | false =>
            obtain ⟨mn, hmn⟩ := domMinI_exists hx rfl
            obtain ⟨mx, hmx⟩ := domMaxI_exists hx rfl
            obtain ⟨⟨x1, hx1, hx1v⟩, hallmn⟩ := domMinI_spec hmn
            obtain ⟨⟨x2, hx2, hx2v⟩, hallmx⟩ := domMaxI_spec hmx
            have hne : ∀ y ∈ (Frame.domains F).getD s [], ∀ k', y.intView = some k' → k' ≠ k := by
              intro y hy k' hyk hk'
              subst hk'
              obtain ⟨k'', rfl⟩ := hints y hy
              have := hfalse _ hy
              simp [Literal.valueHolds, Value.intView] at this hyk
              exact this hyk
            have hmnk : mn ≠ k := hne x1 hx1 mn hx1v
            have hmxk : mx ≠ k := hne x2 hx2 mx hx2v
            by_cases hlt : k < mn
            · exact sf_posLe_to_negNe ((hE s).1.2 mn hmn) (by omega)
            · by_cases hgt : mx < k
              · exact sf_negLe_to_negNe ((hE s).1.1 mx hmx) hgt
              · refine (hE s).2.2 k ⟨x1, hx1, mn, hx1v, by omega⟩ ⟨x2, hx2, mx, hx2v, by omega⟩ ?_
                intro v hv hvk
                exact hne v hv k hvk rfl

/-! ## R3 the event contract -/

theorem scanDatabase_implied {original : List Clause} {f : BranchFrame} :
    ∀ {db : List Clause} {l : Literal} {c : Clause} {lr fl : Bool},
      scanDatabase original f db = .implied l c lr fl →
        c ∈ db ∧ clauseRemaining f c = [l] := by
  intro db
  induction db with
  | nil => intro l c lr fl h; simp [scanDatabase] at h
  | cons c0 rest ih =>
      intro l c lr fl h
      unfold scanDatabase at h
      cases hr : clauseRemaining f c0 with
      | nil => rw [hr] at h; simp at h
      | cons a tl =>
          rw [hr] at h
          cases tl with
          | nil =>
              simp only at h
              by_cases hp : productive a f = true
              · rw [if_pos hp] at h
                simp only [PruningEvent.implied.injEq] at h
                obtain ⟨rfl, rfl, -, -⟩ := h
                exact ⟨List.mem_cons_self, hr⟩
              · rw [if_neg hp] at h
                obtain ⟨h1, h2⟩ := ih h
                exact ⟨List.mem_cons_of_mem _ h1, h2⟩
          | cons b tl' =>
              simp only at h
              obtain ⟨h1, h2⟩ := ih h
              exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem scanPropagators_implied {bs : BranchState leaf} {orig : List Domain}
    {props : List Propagator} (hP : ∀ p ∈ props, PropSemContract orig p bs) :
    ∀ {ps : List Propagator}, (∀ p ∈ ps, p ∈ props) →
      ∀ {l : Literal} {c : Clause} {lr fl : Bool},
        scanPropagators bs.frame ps = .implied l c lr fl → SemReasonOK orig bs.trail l c := by
  intro ps
  induction ps with
  | nil => intro _ l c lr fl h; simp [scanPropagators] at h
  | cons p rest ih =>
      intro hsub l c lr fl h
      unfold scanPropagators at h
      have hpP := hP p (hsub p List.mem_cons_self)
      cases hrun : p.run (frameState bs.frame) with
      | stable =>
          rw [hrun] at h
          exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h
      | conflict cc => rw [hrun] at h; simp at h
      | implied l' r =>
          rw [hrun] at h
          simp only at h
          by_cases hp : productive l' bs.frame = true
          · rw [if_pos hp] at h
            simp only [PruningEvent.implied.injEq] at h
            obtain ⟨rfl, rfl, -, -⟩ := h
            exact hpP.1 _ r hrun
          · rw [if_neg hp] at h
            exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) h

theorem not_boolEq_of_remaining {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hJ : FrameJ orig tr F) {l : Literal}
    (hrem : literalImpossible F l = false) : ∀ s b, l.atom ≠ Atom.boolEq s b := by
  intro s b hb
  unfold literalImpossible at hrem
  have := List.all_eq_false.mp hrem
  obtain ⟨v, hv, hvh⟩ := this
  obtain ⟨k, rfl⟩ := allInt_getD hint _ v (hJ.fits _ v hv)
  obtain ⟨atom, pos⟩ := l
  simp only at hb
  subst hb
  simp [Literal.valueHolds] at hvh

/-- The semantic reason contract of a database unit propagation on a live integer frame. -/
theorem dbUnit_sem {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : AllIntBox orig) (hJ : FrameJ orig tr F) (hS : FrameShape orig F)
    (hlive : ∀ d ∈ F.1, d ≠ []) {c : Clause} {l : Literal}
    (hrem : clauseRemaining F c = [l]) : SemReasonOK orig tr l c := by
  have hlmem : l ∈ c.filter (fun q => !literalImpossible F q) := by
    unfold clauseRemaining at hrem; rw [hrem]; exact List.mem_cons_self
  obtain ⟨hlc, hlp⟩ := List.mem_filter.mp hlmem
  have hlf : literalImpossible F l = false := by simpa using hlp
  have hnb := not_boolEq_of_remaining hint hJ hlf
  have hnorm : l.norm = l := by
    obtain ⟨atom, pos⟩ := l
    cases atom with
    | boolEq s b => exact absurd rfl (hnb s b)
    | intLe s u => rfl
    | intNe s u => rfl
  refine ⟨by rw [hnorm]; exact hlc, fun q hq hne => ?_⟩
  have hqimp : literalImpossible F q = true := by
    cases hh : literalImpossible F q with
    | true => rfl
    | false =>
        exfalso
        have : q ∈ clauseRemaining F c := List.mem_filter.mpr ⟨hq, by simp [hh]⟩
        rw [hrem] at this
        have : q = l := List.mem_singleton.mp this
        subst this
        simp [litEqB] at hne
  exact frameFalse_sem hint hJ hS hlive hqimp

theorem nextPruningEvent_implied_sem {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    (hint : AllIntBox orig) (hJ : FrameJ orig bs.trail bs.frame) (hS : FrameShape orig bs.frame)
    (hP : ∀ p ∈ props, PropSemContract orig p bs) {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl) :
    SemReasonOK orig bs.trail l c := by
  unfold nextPruningEvent at h
  cases hd : scanDatabase original bs.frame bs.learned with
  | stable =>
      rw [hd] at h
      by_cases hv : frameViewedB bs.frame = true
      · rw [if_pos hv] at h
        exact scanPropagators_implied hP (fun x hx => hx) h
      · rw [if_neg hv] at h; cases h
  | conflict cs => rw [hd] at h; cases h
  | implied l' c' lr' fl' =>
      rw [hd] at h
      simp only at h
      by_cases hl : frameLiveB bs.frame = true
      · rw [if_pos hl] at h
        simp only [PruningEvent.implied.injEq] at h
        obtain ⟨rfl, rfl, -, -⟩ := h
        obtain ⟨-, hrem⟩ := scanDatabase_implied hd
        have hlive : ∀ d ∈ bs.frame.1, d ≠ [] := by
          intro d hd' hnil
          have := List.all_eq_true.mp hl d hd'
          simp [hnil] at this
        exact dbUnit_sem hint hJ hS hlive hrem
      · rw [if_neg hl] at h; cases h

theorem explainedDeduction_event {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    ∃ lr fl, nextPruningEvent original props bs.frame bs.learned
      = .implied d.literal d.reason lr fl := by
  unfold explainedDeduction at h
  cases hev : nextPruningEvent original props bs.frame bs.learned with
  | stable => rw [hev] at h; cases h
  | conflict cs => rw [hev] at h; cases h
  | implied l c lr fl =>
      rw [hev] at h
      simp only at h
      cases hr : TrailRedundant bs.trail l with
      | true => rw [hr] at h; cases h
      | false =>
          rw [hr] at h
          simp only at h
          split at h
          · cases h
          · rename_i g hg
            split at h
            · cases h; exact ⟨lr, fl, rfl⟩
            · cases h

/-! ## R4 closure -/

/-- The clamped family kit satisfies `PropSemContract` at every integer-box state whose frame
is explained and whose trail is snap-fixed (state-level form of `runSemContract_of_families`). -/
theorem propSem_of_state {orig : List Domain} {dcs : List DomConstraint}
    {raw props : List Propagator} (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw) (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    {bs : BranchState leaf} (hF : FrameExplainedFull orig bs)
    (hsnap : TrailSnapFixed orig bs.trail) : ∀ p ∈ props, PropSemContract orig p bs := by
  intro p hp
  subst hprops
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  rw [hraw] at hp0
  obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hp0
  exact propSem_clamp hsnap (propSem_of_family hF dc (hfam dc hdc) hprop)

theorem stepNarrowSync_trailSem {orig : List Domain} (bs : BranchState leaf)
    (d : ProductiveDeduction leaf bs) (hT : TrailSem orig bs.trail)
    (hsem : SemReasonOK orig bs.trail d.literal d.reason) :
    TrailSem orig (stepNarrowSync orig bs d).trail := by
  unfold stepNarrowSync
  apply syncSlot_trailSem
  simp only [narrowState]
  exact hT.snoc_propagated (semReasonOK_norm hsem)

theorem explainedClosure_trail_sub (orig : List Domain) (original : List Clause)
    (props : List Propagator) :
    ∀ (bs : BranchState leaf), ∀ e ∈ bs.trail, e ∈ (explainedClosure orig original props bs).trail := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      ∀ e ∈ bs.trail, e ∈ (explainedClosure orig original props bs).trail from
    fun bs => h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle e he
    rw [explainedClosure]
    split
    · exact he
    · rename_i d _
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle e he
    rw [explainedClosure]
    split
    · exact he
    · rename_i d _
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      refine ih _ hmass e ?_
      obtain ⟨ex, hex, -⟩ := stepNarrowSync_trail orig bs d
      rw [hex]
      exact List.mem_append_left _ (List.mem_append_left _ he)

theorem explainedClosure_none {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf}
    (h : explainedDeduction original props bs = none) :
    explainedClosure orig original props bs = bs := by
  rw [explainedClosure]
  split
  · rfl
  · rename_i d hd; rw [h] at hd; cases hd

theorem explainedClosure_some {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    (h : explainedDeduction original props bs = some d) :
    explainedClosure orig original props bs
      = explainedClosure orig original props (stepNarrowSync orig bs d) := by
  rw [explainedClosure]
  split
  · rename_i hd; rw [h] at hd; cases hd
  · rename_i d' hd
    rw [h] at hd
    cases hd
    rfl

/-- **`TrailSem` through the explained closure** (the propagation resumed by a jump). -/
theorem trailSem_closure {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hint : AllIntBox orig)
    (hP : ∀ (bs : BranchState leaf), FrameExplainedFull orig bs →
      TrailSnapFixed orig bs.trail → ∀ p ∈ props, PropSemContract orig p bs) :
    ∀ (bs : BranchState leaf), FrameJ orig bs.trail bs.frame → FrameShape orig bs.frame →
      TrailSem orig bs.trail →
      TrailSnapFixed orig (explainedClosure orig original props bs).trail →
      TrailSem orig (explainedClosure orig original props bs).trail := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      FrameJ orig bs.trail bs.frame → FrameShape orig bs.frame → TrailSem orig bs.trail →
      TrailSnapFixed orig (explainedClosure orig original props bs).trail →
      TrailSem orig (explainedClosure orig original props bs).trail from
    fun bs => h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
    intro bs hle hJ hS hT hsn
    cases hd : explainedDeduction original props bs with
    | none => rw [explainedClosure_none hd]; exact hT
    | some d =>
      exfalso
      have := d.decreases
      omega
  | succ fuel ih =>
    intro bs hle hJ hS hT hsn
    cases hd : explainedDeduction original props bs with
    | none => rw [explainedClosure_none hd]; exact hT
    | some d =>
      rw [explainedClosure_some hd] at hsn ⊢
      have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
        simp only [stepNarrowSync_frame]
        have := d.decreases
        omega
      have hsn0 : TrailSnapFixed orig bs.trail := by
        intro e he
        apply hsn
        have := explainedClosure_trail_sub (leaf := leaf) orig original props
          (stepNarrowSync orig bs d) e
        refine this ?_
        obtain ⟨ex, hex, -⟩ := stepNarrowSync_trail orig bs d
        rw [hex]
        exact List.mem_append_left _ (List.mem_append_left _ he)
      have hF := frameExplainedFull_of_explDoms hint hJ.expl
      have hPs := hP bs hF hsn0
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hsem := nextPruningEvent_implied_sem (original := original) hint hJ hS hPs hev
      exact ih _ hmass (frameJ_stepNarrowSync hint bs d hJ)
        (by rw [stepNarrowSync_frame]; exact frameShape_filter d.filtered hS)
        (stepNarrowSync_trailSem bs d hT hsem) hsn

/-! ## R5 the jump -/

/-- **`TrailSem` through `BackjumpPlan.perform`**: the asserting entry's reason is the (named)
premise `hA`; restoration is the checkpoint prefix; the rest is synchronisation and closure. -/
theorem trailSem_perform {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hint : AllIntBox orig)
    (hP : ∀ (bs : BranchState leaf), FrameExplainedFull orig bs →
      TrailSnapFixed orig bs.trail → ∀ p ∈ props, PropSemContract orig p bs)
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hJcp : FrameJ orig p.checkpoint.trail p.checkpoint.frame)
    (hScp : FrameShape orig p.checkpoint.frame)
    (hTcp : TrailSem orig p.checkpoint.trail)
    (hA : SemReasonOK orig p.checkpoint.trail p.asserting.norm p.learned)
    (hperf : p.perform bs orig original props = some restored)
    (hsn : TrailSnapFixed orig restored.trail) : TrailSem orig restored.trail := by
  unfold BackjumpPlan.perform at hperf
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hperf
  subst hres
  obtain ⟨g, hf, hsf, hst⟩ := restoreNarrow_shape hs
  have hTs : TrailSem orig s.trail := by
    rw [hst]
    rcases p.assertExtra_cases with hx | hx
    · rw [hx, List.append_nil]; exact hTcp
    · rw [hx]
      exact hTcp.snoc_propagated (lit := p.asserting.norm) (lvl := p.target)
        (r := { clause := p.learned }) hA
  have hTa : TrailSem orig (syncAll orig s).trail := syncAll_trailSem s hTs
  have hJa := frameJ_perform_aux hint hJcp hf s hsf hst
  have hSa : FrameShape orig g := frameShape_filter hf hScp
  exact trailSem_closure hint hP (syncAll orig s)
    (by rw [syncAll_frame, hsf]; exact hJa) (by rw [syncAll_frame, hsf]; exact hSa) hTa hsn

end LeanFzn.Solver.UIP.LcgRunInv
