/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamiliesAllDiff.lean
U1b: `PropSemContract` for `allDiff` (`propAllDiffLCG`, conflict-only Hall
clause): bounds via `BoundsExpl`, interior holes via `HolesExpl`.
-/
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesBasic
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesNe
import LeanFzn.Solver.Propagation.Proofs.Fam.AllDiff
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies

namespace LeanFzn.Solver.UIP.LcgFamilies

/-- Interior holes: an integer strictly inside the hull of a slot domain but
absent from it is semantically excluded (`s = h` is semantically falsified).
Part of the frame-explanation invariant, for `allDiff`. -/
def HolesExpl (orig : List Domain) (pre : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s h, (∃ v ∈ doms.getD s [], ∃ a, v.intView = some a ∧ a ≤ h) →
    (∃ v ∈ doms.getD s [], ∃ a, v.intView = some a ∧ h ≤ a) →
    (∀ v ∈ doms.getD s [], v.intView ≠ some h) →
    SemFalsifiedBefore orig pre (negNe s h)

private def stepMin : Option Int → Int → Option Int
  | none, i => some i
  | some c, i => some (minI c i)

private def stepMax : Option Int → Int → Option Int
  | none, i => some i
  | some c, i => some (maxI c i)

private theorem foldl_stepMin (l : List Int) : ∀ (acc : Option Int) (m : Int),
    l.foldl stepMin acc = some m →
    (m ∈ l ∨ acc = some m) ∧ (∀ w ∈ l, m ≤ w) ∧ (∀ a, acc = some a → m ≤ a) := by
  induction l with
  | nil =>
      intro acc m h
      simp only [List.foldl_nil] at h
      subst h
      exact ⟨Or.inr rfl, by simp, fun a ha => by simp at ha; omega⟩
  | cons x l ih =>
      intro acc m h
      simp only [List.foldl_cons] at h
      obtain ⟨h1, h2, h3⟩ := ih _ m h
      refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · cases acc with
          | none => simp [stepMin] at h1; subst h1; exact Or.inl List.mem_cons_self
          | some c =>
              simp only [stepMin, Option.some.injEq] at h1
              unfold minI at h1
              split at h1
              · subst h1; exact Or.inr rfl
              · subst h1; exact Or.inl List.mem_cons_self
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · cases acc with
          | none => exact h3 _ (by simp [stepMin])
          | some c =>
              have := h3 (minI c w) (by simp [stepMin])
              simp [minI] at this ⊢
              split at this <;> omega
        · exact h2 w hw
      · intro a ha
        subst ha
        have := h3 (minI a x) (by simp [stepMin])
        simp [minI] at this ⊢
        split at this <;> omega

private theorem foldl_stepMax (l : List Int) : ∀ (acc : Option Int) (m : Int),
    l.foldl stepMax acc = some m →
    (m ∈ l ∨ acc = some m) ∧ (∀ w ∈ l, w ≤ m) ∧ (∀ a, acc = some a → a ≤ m) := by
  induction l with
  | nil =>
      intro acc m h
      simp only [List.foldl_nil] at h
      subst h
      exact ⟨Or.inr rfl, by simp, fun a ha => by simp at ha; omega⟩
  | cons x l ih =>
      intro acc m h
      simp only [List.foldl_cons] at h
      obtain ⟨h1, h2, h3⟩ := ih _ m h
      refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · cases acc with
          | none => simp [stepMax] at h1; subst h1; exact Or.inl List.mem_cons_self
          | some c =>
              simp only [stepMax, Option.some.injEq] at h1
              unfold maxI at h1
              split at h1
              · subst h1; exact Or.inl List.mem_cons_self
              · subst h1; exact Or.inr rfl
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · cases acc with
          | none => exact h3 _ (by simp [stepMax])
          | some c =>
              have := h3 (maxI c w) (by simp [stepMax])
              simp [maxI] at this ⊢
              split at this <;> omega
        · exact h2 w hw
      · intro a ha
        subst ha
        have := h3 (maxI a x) (by simp [stepMax])
        simp [maxI] at this ⊢
        split at this <;> omega

private theorem foldl_some (f : Option Int → Int → Option Int)
    (hf : ∀ a x, ∃ y, f a x = some y) (l : List Int) :
    ∀ (acc : Option Int), (l ≠ [] ∨ acc ≠ none) → ∃ m, l.foldl f acc = some m := by
  induction l with
  | nil =>
      intro acc h
      cases acc with
      | none => simp at h
      | some a => exact ⟨a, rfl⟩
  | cons x l ih =>
      intro acc _
      simp only [List.foldl_cons]
      obtain ⟨y, hy⟩ := hf acc x
      exact ih _ (Or.inr (by rw [hy]; simp))

private theorem domInts_eq (d : List Value) : domInts d = d.filterMap Value.intView := by
  induction d with
  | nil => rfl
  | cons v d ih =>
      cases v <;> simp [domInts, Value.intView, List.filterMap_cons] <;> exact ih

private theorem mem_domInts {d : List Value} {w : Int} :
    w ∈ domInts d ↔ ∃ x ∈ d, x.intView = some w := by
  rw [domInts_eq, List.mem_filterMap]

private theorem domMinI_eq (d : List Value) :
    domMinI d = (domInts d).foldl stepMin none := by
  unfold domMinI
  congr 1
  funext acc i
  cases acc <;> rfl

private theorem domMaxI_eq (d : List Value) :
    domMaxI d = (domInts d).foldl stepMax none := by
  unfold domMaxI
  congr 1
  funext acc i
  cases acc <;> rfl

theorem domMinI_spec {d : List Value} {m : Int} (h : domMinI d = some m) :
    (∃ x ∈ d, x.intView = some m) ∧ ∀ x ∈ d, ∀ w, x.intView = some w → m ≤ w := by
  have hh : (domInts d).foldl stepMin none = some m := by
    rw [← domMinI_eq]; exact h
  obtain ⟨h1, h2, _⟩ := foldl_stepMin _ none m hh
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact mem_domInts.mp h1
    · simp at h1
  · intro x hx w hw
    exact h2 w (mem_domInts.mpr ⟨x, hx, hw⟩)

theorem domMaxI_spec {d : List Value} {m : Int} (h : domMaxI d = some m) :
    (∃ x ∈ d, x.intView = some m) ∧ ∀ x ∈ d, ∀ w, x.intView = some w → w ≤ m := by
  have hh : (domInts d).foldl stepMax none = some m := by
    rw [← domMaxI_eq]; exact h
  obtain ⟨h1, h2, _⟩ := foldl_stepMax _ none m hh
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact mem_domInts.mp h1
    · simp at h1
  · intro x hx w hw
    exact h2 w (mem_domInts.mpr ⟨x, hx, hw⟩)

theorem domMinI_exists {d : List Value} {x : Value} (hx : x ∈ d) {w : Int}
    (hw : x.intView = some w) : ∃ m, domMinI d = some m := by
  rw [domMinI_eq]
  have hne : domInts d ≠ [] := fun he => by
    have : w ∈ domInts d := mem_domInts.mpr ⟨x, hx, hw⟩
    rw [he] at this; cases this
  obtain ⟨m, hm⟩ := foldl_some stepMin (fun a x => by cases a <;> simp [stepMin]) (domInts d) none
    (Or.inl hne)
  exact ⟨m, hm⟩

theorem domMaxI_exists {d : List Value} {x : Value} (hx : x ∈ d) {w : Int}
    (hw : x.intView = some w) : ∃ m, domMaxI d = some m := by
  rw [domMaxI_eq]
  have hne : domInts d ≠ [] := fun he => by
    have : w ∈ domInts d := mem_domInts.mpr ⟨x, hx, hw⟩
    rw [he] at this; cases this
  obtain ⟨m, hm⟩ := foldl_some stepMax (fun a x => by cases a <;> simp [stepMax]) (domInts d) none
    (Or.inl hne)
  exact ⟨m, hm⟩


private theorem foldl_min_mem (vs : List Int) : ∀ v0 : Int, vs.foldl min v0 ∈ v0 :: vs := by
  induction vs with
  | nil => intro v0; simp
  | cons a as ih =>
      intro v0
      simp only [List.foldl_cons]
      have := ih (min v0 a)
      rcases List.mem_cons.mp this with h | h
      · rw [h]
        rcases (by omega : min v0 a = v0 ∨ min v0 a = a) with h' | h'
        · rw [h']; simp
        · rw [h']; simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

private theorem foldl_max_mem (vs : List Int) : ∀ v0 : Int, vs.foldl max v0 ∈ v0 :: vs := by
  induction vs with
  | nil => intro v0; simp
  | cons a as ih =>
      intro v0
      simp only [List.foldl_cons]
      have := ih (max v0 a)
      rcases List.mem_cons.mp this with h | h
      · rw [h]
        rcases (by omega : max v0 a = v0 ∨ max v0 a = a) with h' | h'
        · rw [h']; simp
        · rw [h']; simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem slotHall_attain {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) :
    ∃ lo hi : Int, (∃ x ∈ d, x.intView = some lo) ∧ (∃ x ∈ d, x.intView = some hi) ∧
      ∀ q ∈ cl, q = posLe s (lo - 1) ∨ q = negLe s hi ∨
        ∃ hh : Int, q = negNe s hh ∧ lo ≤ hh ∧ hh ≤ hi ∧ ∀ x ∈ d, x.intView ≠ some hh := by
  unfold slotHall at h
  split at h
  · exact absurd h (by simp)
  · rename_i v0 vs hL
    split at h
    · exact absurd h (by simp)
    · dsimp only at h
      split at h
      · exact absurd h (by simp)
      · have hmemL : ∀ w, w ∈ v0 :: vs ↔ ∃ x ∈ d, Value.intView x = some w := by
          intro w
          rw [← hL, List.mem_filterMap]
        refine ⟨vs.foldl min v0, vs.foldl max v0, (hmemL _).1 (foldl_min_mem vs v0),
          (hmemL _).1 (foldl_max_mem vs v0), ?_⟩
        intro q hq
        rw [← Option.some.inj h] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl rfl
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr (Or.inl rfl)
        obtain ⟨hh, hhm, rfl⟩ := List.mem_map.mp hq
        refine Or.inr (Or.inr ⟨hh, rfl, ?_⟩)
        have hmem := List.mem_filter.mp hhm
        obtain ⟨k, hk, hkh⟩ := List.mem_map.mp hmem.1
        have hk' := List.mem_range.mp hk
        have hc : (v0 :: vs).contains hh = false := by simpa using hmem.2
        refine ⟨by omega, by omega, ?_⟩
        intro x hx hxv
        have : hh ∈ v0 :: vs := (hmemL hh).2 ⟨x, hx, hxv⟩
        have := List.contains_iff_mem.mpr this
        simp_all

theorem slotHall_sf {orig : List Domain} {pre : List TrailEntry} {doms : List Domain}
    (hB : BoundsExpl orig pre doms) (hH : HolesExpl orig pre doms) {s : Nat} {cl : Clause}
    (h : slotHall s (doms.getD s []) = some cl) :
    ∀ q ∈ cl, SemFalsifiedBefore orig pre q := by
  obtain ⟨_, lo', hi', holes', hcl', hbd, hholes, _⟩ := slotHall_spec h
  obtain ⟨lo, hi, ⟨xl, hxl, hvl⟩, ⟨xh, hxh, hvh⟩, hq⟩ := slotHall_attain h
  -- the extrema of the domain are exactly lo and hi
  obtain ⟨m, hm⟩ := domMinI_exists hxl hvl
  obtain ⟨M, hM⟩ := domMaxI_exists hxh hvh
  obtain ⟨⟨xm, hxm, hvm⟩, hmin⟩ := domMinI_spec hm
  obtain ⟨⟨xM, hxM, hvM⟩, hmax⟩ := domMaxI_spec hM
  have hlo' : lo' = lo := by
    have hmem : posLe s (lo' - 1) ∈ cl := by rw [hcl']; simp
    rcases hq _ hmem with e | e | ⟨hh, e, _⟩
    · simp [posLe] at e; omega
    · simp [posLe, negLe] at e
    · simp [posLe, negNe] at e
  have hhi' : hi' = hi := by
    have hmem : negLe s hi' ∈ cl := by rw [hcl']; simp
    rcases hq _ hmem with e | e | ⟨hh, e, _⟩
    · simp [posLe, negLe] at e
    · simp [negLe] at e; omega
    · simp [negLe, negNe] at e
  have hlm : m = lo := by
    have h1 := hmin xl hxl lo hvl
    have h2 := hbd xm hxm m hvm
    omega
  have hMm : M = hi := by
    have h1 := hmax xh hxh hi hvh
    have h2 := hbd xM hxM M hvM
    omega
  intro q hq0
  rcases hq q hq0 with rfl | rfl | ⟨hh, rfl, hl, hh', hno⟩
  · rw [← hlm]; exact (hB s).2 m hm
  · rw [← hMm]; exact (hB s).1 M hM
  · exact hH s hh ⟨xl, hxl, lo, hvl, hl⟩ ⟨xh, hxh, hi, hvh, hh'⟩ hno


theorem hallClauses_sf {orig : List Domain} {pre : List TrailEntry} {doms : List Domain}
    (hB : BoundsExpl orig pre doms) (hH : HolesExpl orig pre doms) :
    ∀ (ss : List Nat) (c : Clause), hallClauses doms ss = some c →
      ∀ q ∈ c, SemFalsifiedBefore orig pre q := by
  intro ss
  induction ss with
  | nil =>
      intro c hc q hq
      simp [hallClauses] at hc; subst hc; simp at hq
  | cons s ss ih =>
      intro c hc q hq
      simp only [hallClauses] at hc
      split at hc
      · rename_i c1 c2 h1 h2
        have hc' := Option.some.inj hc
        subst hc'
        rcases List.mem_append.mp hq with hq | hq
        · exact slotHall_sf hB hH h1 q hq
        · exact ih c2 h2 q hq
      · exact absurd hc (by simp)

/-- PLAN L8: `propAllDiffLCG`'s result contract. The pigeonhole conflict stays
    the Hall clause (its literals are falsified by `BoundsExpl` +
    `HolesExpl`); each VALUE ELIMINATION is falsified by the fixed slot's
    bounds (`BoundsExpl`), its absence of Boolean values (`AbsentExpl`,
    the `neBoolLit` typing causes) and the target slot's `domNeGate`. -/
theorem propAllDiffLCG_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (hH : HolesExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (is : List Nat) : ResSem orig pre (propAllDiffLCG st is) := by
  unfold propAllDiffLCG
  split
  · intro q hq
    unfold hallClause at hq
    split at hq
    · rename_i c hc
      exact hallClauses_sf hB hH _ c hc q hq
    · simp at hq
  · split
    · rename_i i j c hf
      obtain ⟨-, hsi, -, hb⟩ := allDiffElimFirst_spec hf
      obtain ⟨-, -, -, hgate, -⟩ := allDiffElimB_eq hb
      have hm1 : domMinI (st.domains.getD i []) = some c := by rw [hsi]; rfl
      have hm2 : domMaxI (st.domains.getD i []) = some c := by rw [hsi]; rfl
      have b1 := (hB i).2 c hm1
      have b2 := (hB i).1 c hm2
      have b3 := neBoolLit_sf_self hA hsi b2
      have b4 := neBoolLit_sf_other hA hgate b2
      exact reasonOK_of_fix (by rfl) (by simp [allDiffElimClause])
        (sf_cons _ (by sfs))
    · trivial

end LeanFzn.Solver.UIP.LcgFamilies
