import LeanFzn.Legacy.Solver.Propagation.LiteralClamp
import LeanFzn.Legacy.Solver.UIP.Proofs.EmissionVocabulary
import LeanFzn.Legacy.Solver.UIP.Proofs.SyncVocabulary

/-!
# U1e: the literal clamp preserves meaning under `Fits orig` and lands in `litPool orig`

* `snapLit_eval` : `a.Fits orig → (snapLit orig l).eval a = l.eval a`.
* `snapLit_norm` : `snapLit` commutes with `Literal.norm`.
* `snapLit_norm_mem_litPool` : a well-slotted literal's clamp is pooled.
* `emissionPoolAt_clampProps` : the clamped propagators emit only pooled literals
  (premise: the raw emissions are well-slotted, `EmissionTyped`).
-/

namespace LeanFzn.Solver.UIP.ClampPool
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.UIP

/-! ## 1. Integer helpers -/

theorem imax_le_left (a x : Int) : a ≤ max a x := by rw [Int.max_def]; split <;> omega
theorem imax_le_right (a x : Int) : x ≤ max a x := by rw [Int.max_def]; split <;> omega
theorem imax_eq_right {a x : Int} (h : a ≤ x) : max a x = x := by rw [Int.max_def, if_pos h]
theorem imax_eq_left {a x : Int} (h : x ≤ a) : max a x = a := by
  rw [Int.max_def]; split <;> omega
theorem imin_le_left (a x : Int) : min a x ≤ a := by rw [Int.min_def]; split <;> omega
theorem imin_le_right (a x : Int) : min a x ≤ x := by rw [Int.min_def]; split <;> omega
theorem imin_eq_left {a x : Int} (h : a ≤ x) : min a x = a := by rw [Int.min_def, if_pos h]
theorem imin_eq_right {a x : Int} (h : x ≤ a) : min a x = x := by
  rw [Int.min_def]; split <;> omega

theorem foldl_max_mem (l : List Int) : ∀ a : Int, l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons x xs ih =>
      intro a
      rcases ih (max a x) with h | h
      · by_cases hax : a ≤ x
        · right; rw [List.foldl_cons, h]; simp [imax_eq_right hax]
        · left; rw [List.foldl_cons, h]; simp [imax_eq_left (Int.le_of_not_le hax)]
      · right; rw [List.foldl_cons]; exact List.mem_cons_of_mem _ h

theorem le_foldl_max_init (l : List Int) : ∀ a : Int, a ≤ l.foldl max a := by
  induction l with
  | nil => intro a; exact Int.le_refl _
  | cons x xs ih =>
      intro a
      rw [List.foldl_cons]
      exact Int.le_trans (imax_le_left a x) (ih _)

theorem le_foldl_max_of_mem {l : List Int} {x : Int} (hx : x ∈ l) :
    ∀ a : Int, x ≤ l.foldl max a := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
      intro a
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans (imax_le_right a x) (le_foldl_max_init ys _)
      · exact ih hx _

theorem foldl_min_mem (l : List Int) : ∀ a : Int, l.foldl min a = a ∨ l.foldl min a ∈ l := by
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons x xs ih =>
      intro a
      rcases ih (min a x) with h | h
      · by_cases hax : a ≤ x
        · left; rw [List.foldl_cons, h]; simp [imin_eq_left hax]
        · right; rw [List.foldl_cons, h]; simp [imin_eq_right (Int.le_of_not_le hax)]
      · right; rw [List.foldl_cons]; exact List.mem_cons_of_mem _ h

theorem foldl_min_le_init (l : List Int) : ∀ a : Int, l.foldl min a ≤ a := by
  induction l with
  | nil => intro a; exact Int.le_refl _
  | cons x xs ih =>
      intro a
      rw [List.foldl_cons]
      exact Int.le_trans (ih _) (imin_le_left a x)

theorem foldl_min_le_of_mem {l : List Int} {x : Int} (hx : x ∈ l) :
    ∀ a : Int, l.foldl min a ≤ x := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
      intro a
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans (foldl_min_le_init ys _) (imin_le_right a x)
      · exact ih hx _

/-- Pool of a nonempty integer list is nonempty and `clampMin` is a minimal member. -/
theorem clampMin_mem {ints : List Int} (h : ints ≠ []) :
    clampMin (clampPool ints) ∈ clampPool ints := by
  have hhead : (clampPool ints).headD 0 ∈ clampPool ints := by
    cases ints with
    | nil => exact absurd rfl h
    | cons x xs => simp [clampPool]
  rcases foldl_min_mem (clampPool ints) ((clampPool ints).headD 0) with h' | h'
  · unfold clampMin; rw [h']; exact hhead
  · exact h'

theorem clampMin_le {ints : List Int} {x : Int} (hx : x ∈ clampPool ints) :
    clampMin (clampPool ints) ≤ x := foldl_min_le_of_mem hx _

theorem clampMin_lt {ints : List Int} {v : Int} (hv : v ∈ ints) :
    clampMin (clampPool ints) < v := by
  have : v - 1 ∈ clampPool ints := List.mem_append_right _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
  have := clampMin_le this
  omega

theorem snapBound_mem {ints : List Int} (h : ints ≠ []) (k : Int) :
    snapBound ints k ∈ clampPool ints := by
  unfold snapBound
  rcases foldl_max_mem ((clampPool ints).filter (· ≤ k)) (clampMin (clampPool ints)) with h' | h'
  · rw [h']; exact clampMin_mem h
  · exact (List.mem_filter.mp h').1

theorem snapBound_iff {ints : List Int} (k : Int) {v : Int} (hv : v ∈ ints) :
    v ≤ snapBound ints k ↔ v ≤ k := by
  have hvp : v ∈ clampPool ints := List.mem_append_left _ hv
  unfold snapBound
  constructor
  · intro hle
    rcases foldl_max_mem ((clampPool ints).filter (· ≤ k)) (clampMin (clampPool ints)) with h' | h'
    · rw [h'] at hle
      have := clampMin_lt hv
      omega
    · have := (List.mem_filter.mp h').2
      have hk : snapBound ints k ≤ k := by simpa [snapBound] using this
      exact Int.le_trans hle hk
  · intro hk
    exact Int.le_trans (le_foldl_max_of_mem
      (List.mem_filter.mpr ⟨hvp, by simpa using hk⟩) _) (Int.le_refl _)

/-! ## 2. Meaning preservation -/

theorem clampInts_of_mem {d : Domain} {w : Value} {x : Int}
    (hw : w ∈ Dom.enum d) (hx : w.intView = some x) : x ∈ clampInts d :=
  List.mem_filterMap.mpr ⟨w, hw, hx⟩

theorem getD_of_getElem? {orig : List Domain} {s : Nat} {d : Domain}
    (h : orig[s]? = some d) : orig.getD s Dom.empty = d := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- The slot's integer view of a fitting assignment is a domain integer. -/
theorem slotInt_mem_clampInts {orig : List Domain} {a : Assignment}
    (hfit : a.Fits orig) {s : Nat} {d : Domain} (hd : orig[s]? = some d) {x : Int}
    (hx : slotInt a s = some x) : x ∈ clampInts d := by
  unfold slotInt at hx
  cases hw : a[s]? with
  | none => rw [hw] at hx; cases hx
  | some w =>
      rw [hw] at hx
      have hmem := hfit.2 s w hw
      simp only [domEmpty_eq] at hmem
      rw [getD_of_getElem? hd] at hmem
      exact clampInts_of_mem ((DomainLike.mem_iff d w).mp hmem) hx

theorem snapLit_eval {orig : List Domain} {a : Assignment} (hfit : a.Fits orig)
    (l : Literal) : (snapLit orig l).eval a = l.eval a := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => simp [snapLit]
  | intLe s k =>
      simp only [snapLit]
      cases hd : orig[s]? with
      | none => rfl
      | some d =>
          simp only
          by_cases hemp : (clampInts d).isEmpty = true
          · simp [hemp]
          · simp only [hemp, if_false, Bool.false_eq_true]
            have hne : clampInts d ≠ [] := by
              intro h; apply hemp; simp [h]
            cases hx : slotInt a s with
            | none => simp [Literal.eval, Atom.eval, hx]
            | some x =>
                have hxm := slotInt_mem_clampInts hfit hd hx
                have hiff := snapBound_iff (ints := clampInts d) k hxm
                simp [Literal.eval, Atom.eval, hx, hiff]
  | intNe s v =>
      simp only [snapLit]
      cases hd : orig[s]? with
      | none => rfl
      | some d =>
          simp only
          by_cases hc : (clampInts d).isEmpty = true ∨ v ∈ clampInts d
          · simp only [if_pos hc]
          · simp only [hc, if_false]
            have hemp : ¬ (clampInts d).isEmpty = true := fun h => hc (Or.inl h)
            have hvn : v ∉ clampInts d := fun h => hc (Or.inr h)
            have hne : clampInts d ≠ [] := by
              intro h; apply hemp; simp [h]
            cases hx : slotInt a s with
            | none => simp [Literal.eval, Atom.eval, hx]
            | some x =>
                have hxm := slotInt_mem_clampInts hfit hd hx
                have hxv : x ≠ v := fun h => hvn (h ▸ hxm)
                have hlt := clampMin_lt (ints := clampInts d) hxm
                have hnle : ¬ x ≤ clampMin (clampPool (clampInts d)) := by omega
                cases pos <;> simp [Literal.eval, Atom.eval, hx, hxv, hnle]

theorem snapClause_satisfied {orig : List Domain} {a : Assignment} (hfit : a.Fits orig)
    {c : Clause} : (snapClause orig c).SatisfiedBy a ↔ c.SatisfiedBy a := by
  unfold snapClause Clause.SatisfiedBy
  constructor
  · rintro ⟨q, hq, hev⟩
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact ⟨q0, hq0, by rw [← snapLit_eval hfit]; exact hev⟩
  · rintro ⟨q, hq, hev⟩
    exact ⟨snapLit orig q, List.mem_map_of_mem hq, by rw [snapLit_eval hfit]; exact hev⟩

/-! ## 3. Normalization commutes -/

theorem snapLit_norm (orig : List Domain) (l : Literal) :
    (snapLit orig l).norm = snapLit orig l.norm := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => cases pos <;> simp [snapLit, Literal.norm]
  | intLe s k =>
      simp only [snapLit, Literal.norm]
      cases hd : orig[s]? with
      | none => rfl
      | some d =>
          simp only
          by_cases hh : (clampInts d).isEmpty = true <;> simp [hh, Literal.norm]
  | intNe s v =>
      simp only [snapLit, Literal.norm]
      cases hd : orig[s]? with
      | none => rfl
      | some d =>
          simp only
          by_cases hh : (clampInts d).isEmpty = true ∨ v ∈ clampInts d
          · simp only [if_pos hh, Literal.norm]
          · simp only [if_neg hh, Literal.norm]

/-! ## 4. Pool membership -/

/-- A literal is *well-slotted* in `orig`: Boolean atoms name a box slot; order
and removal atoms name a slot whose original domain has an integer view. -/
def LitWF (orig : List Domain) (l : Literal) : Prop :=
  match l.atom with
  | .boolEq s _ => s < orig.length
  | .intLe s _ => ∃ d, orig[s]? = some d ∧ clampInts d ≠ []
  | .intNe s _ => ∃ d, orig[s]? = some d ∧ clampInts d ≠ []

theorem snapLit_norm_mem_litPool {orig : List Domain} {l : Literal} (h : LitWF orig l) :
    (snapLit orig l).norm ∈ litPool orig := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b =>
      have hs : s < orig.length := h
      have ha : ∀ b', Atom.boolEq s b' ∈ atomPoolBase 0 orig := fun b' =>
        slotAtomPool_mem_atomPoolBase hs (boolEq_mem_slotAtomPool s _ b')
      cases pos
      · have : (snapLit orig ⟨.boolEq s b, false⟩).norm = posLit (.boolEq s (!b)) := by
          simp [snapLit, Literal.norm, posLit]
        rw [this]
        exact posLit_mem (List.mem_append_left _ (ha _))
      · have : (snapLit orig ⟨.boolEq s b, true⟩).norm = posLit (.boolEq s b) := by
          simp [snapLit, Literal.norm, posLit]
        rw [this]
        exact posLit_mem (List.mem_append_left _ (ha _))
  | intLe s k =>
      obtain ⟨d, hd, hne⟩ := (h : ∃ d, orig[s]? = some d ∧ clampInts d ≠ [])
      have hemp : ¬ (clampInts d).isEmpty = true := by
        intro h'; apply hne; simpa using h'
      have hg := getD_of_getElem? hd
      have hthr : snapBound (clampInts d) k ∈ threshPool (orig.getD s Dom.empty) := by
        rw [hg]; exact snapBound_mem hne k
      have : snapLit orig ⟨.intLe s k, pos⟩ = ⟨.intLe s (snapBound (clampInts d) k), pos⟩ := by
        simp [snapLit, hd, hemp]
      rw [this]
      cases pos
      · exact negLe_mem_litPool_of_thresh hthr
      · exact posLe_mem_litPool_of_thresh hthr
  | intNe s v =>
      obtain ⟨d, hd, hne⟩ := (h : ∃ d, orig[s]? = some d ∧ clampInts d ≠ [])
      have hemp : ¬ (clampInts d).isEmpty = true := by
        intro h'; apply hne; simpa using h'
      have hg := getD_of_getElem? hd
      have hs : s < orig.length := (List.getElem?_eq_some_iff.mp hd).1
      by_cases hv : v ∈ clampInts d
      · have : snapLit orig ⟨.intNe s v, pos⟩ = ⟨.intNe s v, pos⟩ := by
          simp [snapLit, hd, hv]
        rw [this]
        have ha : Atom.intNe s v ∈ slotAtomPool s (orig.getD s Dom.empty) := by
          rw [hg]; exact intNe_mem_slotAtomPool hv
        have hb := slotAtomPool_mem_atomPoolBase hs ha
        cases pos
        · exact negLit_mem (List.mem_append_left _ hb)
        · exact posLit_mem (List.mem_append_left _ hb)
      · have hthr : clampMin (clampPool (clampInts d)) ∈ threshPool (orig.getD s Dom.empty) := by
          rw [hg]; exact clampMin_mem hne
        have : snapLit orig ⟨.intNe s v, pos⟩
            = ⟨.intLe s (clampMin (clampPool (clampInts d))), !pos⟩ := by
          simp [snapLit, hd, hemp, hv]
        rw [this]
        cases pos
        · exact posLe_mem_litPool_of_thresh hthr
        · exact negLe_mem_litPool_of_thresh hthr

/-! ## 5. The clamped kit emits only pooled literals -/

/-- **Well-slotted emissions** of a raw propagator list (exact named premise: every
literal a registered propagator emits names a real box slot, with an integer view
for order/removal atoms). -/
def EmissionTyped (orig : List Domain) (props : List Propagator) : Prop :=
  (∀ p ∈ props, ∀ st l r, p.run st = .implied l r →
    LitWF orig l ∧ ∀ q ∈ r.clause, LitWF orig q) ∧
  (∀ p ∈ props, ∀ st c, p.run st = .conflict c → ∀ q ∈ c, LitWF orig q)

theorem clamp_run_implied {orig : List Domain} {p : Propagator} {st : State}
    {l : Literal} {r : Reason} (h : (p.clamp orig).run st = .implied l r) :
    ∃ l0 r0, p.run st = .implied l0 r0 ∧ l = snapLit orig l0 ∧
      r.clause = snapClause orig r0.clause := by
  simp only [Propagator.clamp] at h
  cases hr : p.run st with
  | stable => rw [hr] at h; simp [snapResult] at h
  | implied l0 r0 =>
      rw [hr] at h
      simp only [snapResult, PropagationResult.implied.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l0, r0, rfl, rfl, rfl⟩
  | conflict c => rw [hr] at h; simp [snapResult] at h

theorem clamp_run_conflict {orig : List Domain} {p : Propagator} {st : State}
    {c : Clause} (h : (p.clamp orig).run st = .conflict c) :
    ∃ c0, p.run st = .conflict c0 ∧ c = snapClause orig c0 := by
  simp only [Propagator.clamp] at h
  cases hr : p.run st with
  | stable => rw [hr] at h; simp [snapResult] at h
  | implied l0 r0 => rw [hr] at h; simp [snapResult] at h
  | conflict c0 =>
      rw [hr] at h
      simp only [snapResult, PropagationResult.conflict.injEq] at h
      exact ⟨c0, rfl, h.symm⟩

theorem emissionPoolAt_clampProps {orig : List Domain} {props : List Propagator}
    (h : EmissionTyped orig props) :
    EmissionPoolAt (litPool orig) (clampProps orig props) := by
  constructor
  · intro p hp st l r hr
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
    obtain ⟨l0, r0, hrun, rfl, hcl⟩ := clamp_run_implied hr
    obtain ⟨hl, hc⟩ := h.1 p0 hp0 st l0 r0 hrun
    refine ⟨snapLit_norm_mem_litPool hl, fun q hq => ?_⟩
    rw [hcl] at hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact snapLit_norm_mem_litPool (hc q0 hq0)
  · intro p hp st c hc q hq
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
    obtain ⟨c0, hrun, rfl⟩ := clamp_run_conflict hc
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact snapLit_norm_mem_litPool (h.2 p0 hp0 st c0 hrun q0 hq0)

end LeanFzn.Solver.UIP.ClampPool
