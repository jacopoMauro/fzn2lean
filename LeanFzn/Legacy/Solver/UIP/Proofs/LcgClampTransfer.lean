/-
File: LeanFzn/Solver/UIP/Proofs/LcgClampTransfer.lean
U1e transfer: `PropSemContract` of a raw propagator carries over to its runtime
clamp (`Propagator.clamp`), relative to the named premise `TrailSnapFixed`
(every trail literal is a fixed point of `snapLit`, i.e. pooled / in range).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamilies
import LeanFzn.Legacy.Solver.UIP.Proofs.ClampPool
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies
open LeanFzn.Solver.UIP.ClampPool

namespace LeanFzn.Solver.UIP.LcgClamp

variable {leaf : Assignment → Bool}

/-- Named premise: every trail literal is a `snapLit` fixed point. -/
def TrailSnapFixed (orig : List Domain) (tr : List TrailEntry) : Prop :=
  ∀ e ∈ tr, snapLit orig e.literal = e.literal

theorem snapBound_le_or {ints : List Int} (k : Int) :
    snapBound ints k ≤ k ∨ snapBound ints k = clampMin (clampPool ints) := by
  unfold snapBound
  rcases foldl_max_mem ((clampPool ints).filter (· ≤ k)) (clampMin (clampPool ints)) with h' | h'
  · exact Or.inr h'
  · left; simpa using (List.mem_filter.mp h').2

theorem snapBound_ge_of_mem {ints : List Int} {x k : Int} (hx : x ∈ clampPool ints)
    (hk : x ≤ k) : x ≤ snapBound ints k :=
  le_foldl_max_of_mem (List.mem_filter.mpr ⟨hx, by simpa using hk⟩) _

theorem snap_negate (orig : List Domain) (l : Literal) :
    snapLit orig l.negate = (snapLit orig l).negate := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => simp [snapLit, Literal.negate]
  | intLe s k =>
      simp only [snapLit, Literal.negate]
      cases hd : orig[s]? with
      | none => rfl
      | some d => simp only; split <;> simp
  | intNe s v =>
      simp only [snapLit, Literal.negate]
      cases hd : orig[s]? with
      | none => rfl
      | some d => simp only; split <;> simp


/-- Root falsity survives the clamp. -/
theorem litFalseAtRoot_snap (orig : List Domain) (q : Literal)
    (h : litFalseAtRoot orig q = true) : litFalseAtRoot orig (snapLit orig q) = true := by
  obtain ⟨atom, pos⟩ := q
  cases atom with
  | boolEq s b => simpa [snapLit] using h
  | intLe s k =>
      simp only [snapLit]
      cases hd : orig[s]? with
      | none => simpa using h
      | some d =>
          simp only
          by_cases hemp : (clampInts d).isEmpty = true
          · simpa [hemp] using h
          · simp only [hemp, if_false, Bool.false_eq_true]
            have hg := getD_of_getElem? hd
            simp only [litFalseAtRoot, List.all_eq_true, Atom.slot, hg] at h ⊢
            intro v hv
            have hh := h v hv
            cases hi : v.intView with
            | none => simp [Atom.evalAtValue, hi]
            | some x =>
                have hiff := snapBound_iff (ints := clampInts d) k (clampInts_of_mem hv hi)
                simp only [Atom.evalAtValue, hi, Option.map_some] at hh ⊢
                cases pos <;> simp at hh ⊢ <;> omega
  | intNe s v0 =>
      simp only [snapLit]
      cases hd : orig[s]? with
      | none => simpa using h
      | some d =>
          simp only
          by_cases hc : (clampInts d).isEmpty = true ∨ v0 ∈ clampInts d
          · simpa only [if_pos hc] using h
          · simp only [hc, if_false]
            have hg := getD_of_getElem? hd
            have hemp : ¬ (clampInts d).isEmpty = true := fun h => hc (Or.inl h)
            have hvn : v0 ∉ clampInts d := fun h => hc (Or.inr h)
            have hne : clampInts d ≠ [] := by
              intro h; apply hemp; simp [h]
            simp only [litFalseAtRoot, List.all_eq_true, Atom.slot, hg] at h ⊢
            intro v hv
            have hh := h v hv
            cases hi : v.intView with
            | none => simp [Atom.evalAtValue, hi]
            | some x =>
                have hx := clampInts_of_mem hv hi
                have hxv : x ≠ v0 := fun e => hvn (e ▸ hx)
                have hlt := clampMin_lt hx
                simp only [Atom.evalAtValue, hi, Option.map_some] at hh ⊢
                cases pos <;> simp at hh ⊢ <;> omega

/-- Fixed point of the clamp on an order literal: threshold is pooled. -/
theorem fixed_intLe {orig : List Domain} {s : Nat} {k : Int} {p : Bool} {d : Domain}
    (hd : orig[s]? = some d) (hne : ¬ (clampInts d).isEmpty = true)
    (h : snapLit orig ⟨.intLe s k, p⟩ = ⟨.intLe s k, p⟩) : k ∈ clampPool (clampInts d) := by
  have hne' : clampInts d ≠ [] := by intro h; apply hne; simp [h]
  simp only [snapLit, hd, hne, if_false, Bool.false_eq_true, Literal.mk.injEq, Atom.intLe.injEq, true_and, and_true] at h
  rw [← h]; exact snapBound_mem hne' k

theorem fixed_intNe {orig : List Domain} {s : Nat} {v : Int} {p : Bool} {d : Domain}
    (hd : orig[s]? = some d) (hne : ¬ (clampInts d).isEmpty = true)
    (h : snapLit orig ⟨.intNe s v, p⟩ = ⟨.intNe s v, p⟩) : v ∈ clampInts d := by
  refine Classical.byContradiction fun hv => ?_
  have hc : ¬ ((clampInts d).isEmpty = true ∨ v ∈ clampInts d) := fun h' => h'.elim hne hv
  simp only [snapLit, hd, hc, if_false] at h
  cases h

theorem zero_mem_pool_of_bool {orig : List Domain} {s : Nat} {d : Domain}
    (hd : orig[s]? = some d) (hne : ¬ (clampInts d).isEmpty = true)
    (hB : slotBoolB orig s = true) : (0 : Int) ∈ clampPool (clampInts d) := by
  have hg := getD_of_getElem? hd
  unfold slotBoolB at hB
  rw [hg] at hB
  obtain ⟨x, hx⟩ : ∃ x, x ∈ clampInts d := by
    cases hc : clampInts d with
    | nil => rw [hc] at hne; simp at hne
    | cons x xs => exact ⟨x, by simp⟩
  unfold clampInts at hx
  obtain ⟨v, hv, hvx⟩ := List.mem_filterMap.mp hx
  have := List.all_eq_true.mp hB v hv
  cases v with
  | bool y =>
      simp only [Value.intView] at hvx
      cases y
      · simp at hvx; subst hvx
        exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, hv, by simp [Value.intView]⟩)
      · simp at hvx; subst hvx
        exact List.mem_append_right _ (List.mem_map.mpr ⟨1, List.mem_filterMap.mpr ⟨_, hv, by simp [Value.intView]⟩, by simp⟩)
  | _ => simp at this

theorem slotHasBool_view_mem {orig : List Domain} {s : Nat} {c : Bool} {d : Domain}
    (hd : orig[s]? = some d) (h : slotHasBool orig s c = true) :
    (if c then (1 : Int) else 0) ∈ clampInts d := by
  have hg := getD_of_getElem? hd
  unfold slotHasBool at h
  rw [hg, List.any_eq_true] at h
  obtain ⟨v, hv, hvb⟩ := h
  cases v with
  | bool x =>
      simp only [beq_iff_eq] at hvb
      subst hvb
      exact List.mem_filterMap.mpr ⟨_, hv, by cases x <;> simp [Value.intView]⟩
  | _ => simp at hvb

theorem imp_posLe_snap {orig : List Domain} {t : Literal} {s : Nat} {k : Int} {d : Domain}
    (hd : orig[s]? = some d) (hne : ¬ (clampInts d).isEmpty = true)
    (hfix : snapLit orig t = t) (h : impliesP orig t (posLe s k) = true) :
    impliesP orig t (posLe s (snapBound (clampInts d) k)) = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    by_cases hbk : ({ atom := a, positive := p } : Literal).boolKind = true
    · rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩
      · cases b <;> cases p <;> simp [impliesBase, impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at h ⊢ <;> simp only [Atom.slot] at h ⊢
        all_goals
          (obtain ⟨hB, hs | hs⟩ := h <;> obtain ⟨rfl, hk0⟩ := hs <;>
            exact ⟨hB, Or.inr ⟨rfl, snapBound_ge_of_mem (zero_mem_pool_of_bool hd hne hB) (by omega)⟩⟩)
      · simp [Literal.boolKind] at hbk
      · simp [Literal.boolKind] at hbk
    · have hbk' : ({ atom := a, positive := p } : Literal).boolKind = false := by simpa using hbk
      cases a <;> cases p <;> simp [impliesBase, impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at hbk' h ⊢ <;> simp only [Atom.slot] at h ⊢
      · rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> right <;>
          exact ⟨rfl, snapBound_ge_of_mem (fixed_intLe hd hne hfix) (by omega)⟩
      · obtain ⟨rfl, hk⟩ := h
        exact ⟨rfl, snapBound_ge_of_mem (List.mem_append_left _ (fixed_intNe hd hne hfix)) hk⟩
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have h1 := ht c hh hc
    have hs' : t.atom.slot = s := hs
    rw [hs'] at hh
    have hmem : (if c then (1 : Int) else 0) ∈ clampPool (clampInts d) :=
      List.mem_append_left _ (slotHasBool_view_mem hd hh)
    cases c <;> simp [Literal.truthAtBool, posLe] at h1 ⊢ <;> exact snapBound_ge_of_mem hmem h1

theorem imp_negNe_cases {orig : List Domain} {t : Literal} {s : Nat} {v : Int}
    (h : impliesP orig t ⟨.intNe s v, false⟩ = true) :
    t = ⟨.intNe s v, false⟩ ∨ boolSlotImp orig t ⟨.intNe s v, false⟩ = true := by
  rcases impliesP_cases h with h | h
  · left
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h
    generalize slotBoolB orig _ = B at h
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
      simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at h ⊢
    exact h
  · exact Or.inr h

/-- Legacy syntactic equality lemma, intentionally restricted to the base relation. -/
theorem imp_negNe_eq {orig : List Domain} {t : Literal} {s : Nat} {v : Int}
    (h : impliesBase orig t ⟨.intNe s v, false⟩ = true) : t = ⟨.intNe s v, false⟩ := by
  obtain ⟨a, p⟩ := t
  unfold impliesBase at h
  generalize slotBoolB orig _ = B at h
  rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
    simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB, posLe, negLe, Literal.negate] at h ⊢
  exact h

theorem litFalseAtRoot_min {orig : List Domain} {s : Nat} {d : Domain}
    (hd : orig[s]? = some d) :
    litFalseAtRoot orig (posLe s (clampMin (clampPool (clampInts d)))) = true := by
  have hg := getD_of_getElem? hd
  simp only [litFalseAtRoot, List.all_eq_true, posLe, Atom.slot, hg]
  intro v hv
  cases hi : v.intView with
  | none => simp [Atom.evalAtValue, hi]
  | some x =>
      have hlt := clampMin_lt (clampInts_of_mem hv hi)
      simp [Atom.evalAtValue, hi]
      omega

theorem semFalsified_snap {orig : List Domain} {pre : List TrailEntry}
    (hfix : ∀ e ∈ pre, snapLit orig e.literal = e.literal) {q : Literal}
    (h : SemFalsifiedBefore orig pre q) : SemFalsifiedBefore orig pre (snapLit orig q) := by
  rcases h with h | ⟨e, he, hi⟩
  · exact Or.inl (litFalseAtRoot_snap orig q h)
  · have hf := hfix e he
    obtain ⟨atom, pos⟩ := q
    cases atom with
    | boolEq s b => exact Or.inr ⟨e, he, by simpa [snapLit] using hi⟩
    | intLe s k =>
        simp only [snapLit]
        cases hd : orig[s]? with
        | none => exact Or.inr ⟨e, he, by simpa using hi⟩
        | some d =>
            simp only
            by_cases hemp : (clampInts d).isEmpty = true
            · exact Or.inr ⟨e, he, by simpa [hemp] using hi⟩
            · simp only [hemp, if_false, Bool.false_eq_true]
              cases pos
              · refine Or.inr ⟨e, he, ?_⟩
                have hi' : impliesP orig e.literal (posLe s k) = true := by
                  simpa [Literal.negate, Literal.norm, posLe] using hi
                simpa [Literal.negate, Literal.norm, posLe] using imp_posLe_snap hd hemp hf hi'
              · rcases snapBound_le_or (ints := clampInts d) k with hle | heq
                · refine Or.inr ⟨e, he, ?_⟩
                  have hi' : impliesP orig e.literal (negLe s k) = true := by
                    simpa [Literal.negate, Literal.norm, negLe] using hi
                  simpa [Literal.negate, Literal.norm, negLe] using
                    impliesP_negLe_mono hi' hle
                · left
                  have := litFalseAtRoot_min hd
                  rw [← heq] at this
                  simpa [posLe] using this
    | intNe s v =>
        simp only [snapLit]
        cases hd : orig[s]? with
        | none => exact Or.inr ⟨e, he, by simpa using hi⟩
        | some d =>
            simp only
            by_cases hc : (clampInts d).isEmpty = true ∨ v ∈ clampInts d
            · exact Or.inr ⟨e, he, by simpa only [if_pos hc] using hi⟩
            · simp only [hc, if_false]
              have hemp : ¬ (clampInts d).isEmpty = true := fun h => hc (Or.inl h)
              cases pos
              · left
                simpa [posLe] using litFalseAtRoot_min hd
              · have hi' : impliesP orig e.literal ⟨.intNe s v, false⟩ = true := by
                  simpa [Literal.negate, Literal.norm] using hi
                rcases imp_negNe_cases hi' with this | htab
                · exfalso
                  rw [this] at hf
                  exact hc (Or.inr (fixed_intNe hd hemp hf))
                · refine Or.inr ⟨e, he, ?_⟩
                  refine impliesP_of_table ?_
                  obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim htab
                  refine boolSlotImp_intro hs hb (fun c hh hc' => ?_)
                  exfalso
                  have h1 := ht c hh hc'
                  have hs' : e.literal.atom.slot = s := hs
                  rw [hs'] at hh
                  have hmem := slotHasBool_view_mem hd hh
                  have hv : (if c then (1 : Int) else 0) = v := by
                    cases c <;> simp [Literal.truthAtBool] at h1 ⊢ <;> omega
                  rw [hv] at hmem
                  exact hc (Or.inr hmem)

theorem semReasonOK_snap {orig : List Domain} {pre : List TrailEntry}
    (hfix : ∀ e ∈ pre, snapLit orig e.literal = e.literal) {l : Literal} {c : Clause}
    (h : SemReasonOK orig pre l c) :
    SemReasonOK orig pre (snapLit orig l) (snapClause orig c) := by
  refine ⟨?_, ?_⟩
  · rw [snapLit_norm]
    exact List.mem_map_of_mem h.1
  · intro q' hq' hne
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    apply semFalsified_snap hfix
    apply h.2 q hq
    cases hb : litEqB q.norm l.norm
    · rfl
    · exfalso
      have heq : q.norm = l.norm := by simpa [litEqB] using hb
      rw [snapLit_norm, snapLit_norm, heq] at hne
      simp [litEqB] at hne

theorem snap_conflict {orig : List Domain} {pre : List TrailEntry}
    (hfix : ∀ e ∈ pre, snapLit orig e.literal = e.literal) {c : Clause}
    (h : ClauseSemFalsifiedR orig pre c) : ClauseSemFalsifiedR orig pre (snapClause orig c) := by
  intro q' hq'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  exact semFalsified_snap hfix (h q hq)

/-- **Clamp transfer** of the per-propagator semantic contract. -/
theorem propSem_clamp {orig : List Domain} {p : Propagator} {bs : BranchState leaf}
    (hfix : TrailSnapFixed orig bs.trail) (h : PropSemContract orig p bs) :
    PropSemContract orig (p.clamp orig) bs := by
  refine ⟨fun l r hr => ?_, fun c hc => ?_⟩
  · obtain ⟨l0, r0, hr0, rfl, hcl⟩ := clamp_run_implied hr
    rw [hcl]
    exact semReasonOK_snap hfix (h.1 l0 r0 hr0)
  · obtain ⟨c0, hc0, rfl⟩ := clamp_run_conflict hc
    exact snap_conflict hfix (h.2 c0 hc0)

end LeanFzn.Solver.UIP.LcgClamp
