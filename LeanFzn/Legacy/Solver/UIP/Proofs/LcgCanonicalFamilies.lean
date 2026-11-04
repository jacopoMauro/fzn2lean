/-
Purpose: canonical emission proofs for registered LCG constraint families.
Dependencies: LcgCanonicalClauses supplies result/clauses and narrowing combinators;
LcgEmissionTyped supplies exact emission inversions already used by typing proofs.
DAG: canonical emission algebra -> family producers -> learned-database run invariant.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalClauses
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPropCheck
namespace LeanFzn.Solver.UIP.LcgCanonicalFamilies
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgCanonicalClauses LeanFzn.Solver.UIP.LcgEmissionTyped
open LeanFzn.Solver.UIP.LcgPropCheck

theorem le_canonical (st : State) (i j : Nat) :
    ResCanonical (propLe st i j) := by
  unfold propLe
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

theorem lt_canonical (st : State) (i j : Nat) :
    ResCanonical (propLt st i j) := by
  unfold propLt
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

theorem eq_canonical (st : State) (i j : Nat) :
    ResCanonical (propEq st i j) := by
  unfold propEq
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

theorem plus_canonical (st : State) (i j k : Nat) :
    ResCanonical (propPlus st i j k) := by
  unfold propPlus
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

/-- PLAN L3: the `minSlot` bound propagator `propMin` is canonical: its four
    narrowings all carry explicit cause clauses whose literals are order
    literals (loop `min_canonical`). -/
theorem min_canonical (st : State) (i j k : Nat) :
    ResCanonical (propMin st i j k) := by
  unfold propMin
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

/-- PLAN C9c: the n-ary array-minimum result propagator `propMinGen` is
    canonical: its two narrowings carry order literals as causes. -/
theorem minGen_canonical (st : State) (os : List DomIntArg) (r : DomIntArg) :
    ResCanonical (propMinGen st os r) := by
  unfold propMinGen
  split
  case h_1 => trivial
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      refine firstEvent_canonical _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_canonical st (clauseCanonical_cons (negLe_norm _ _)
          (by intro q hq
              exact (clauseCanonical_flatMap (os := os)
                (fun o _ => argLoCause_canonical st o) q hq).symm))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_canonical st (clauseCanonical_cons (posLe_norm _ _)
          (by intro q hq
              exact (clauseCanonical_flatMap (os := os)
                (fun o _ => argHiCause_canonical st o) q hq).symm))
    case h_2 => trivial

/-- PLAN C9c: the n-ary array-maximum twin of `minGen_canonical`. -/
theorem maxGen_canonical (st : State) (os : List DomIntArg) (r : DomIntArg) :
    ResCanonical (propMaxGen st os r) := by
  unfold propMaxGen
  split
  case h_1 => trivial
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      refine firstEvent_canonical _ ?_
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_canonical st (clauseCanonical_cons (negLe_norm _ _)
          (by intro q hq
              exact (clauseCanonical_flatMap (os := os)
                (fun o _ => argLoCause_canonical st o) q hq).symm))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_canonical st (clauseCanonical_cons (posLe_norm _ _)
          (by intro q hq
              exact (clauseCanonical_flatMap (os := os)
                (fun o _ => argHiCause_canonical st o) q hq).symm))
    case h_2 => trivial

/-- PLAN L2: `propLinNe` emits only value-removal literals (always canonical). -/
theorem linNe_canonical (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    ResCanonical (propLinNe st coeffs is b) := by
  have hcauses : ClauseCanonical (linNeCauses st.domains (coeffs.zip is)) := by
    intro q hq
    obtain ⟨c, s, v, -, -, rfl⟩ := linNeCauses_mem.mp hq
    rfl
  cases hres : propLinNe st coeffs is b with
  | stable => trivial
  | implied l rs =>
      obtain ⟨-, c, m, -, -, -, -, hl, hrs⟩ := propLinNe_implied_inv hres
      subst hl
      subst hrs
      refine ⟨rfl, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact hcauses q hq
  | conflict cc =>
      obtain ⟨-, -, -, hcl⟩ := propLinNe_conflict_inv hres
      subst hcl
      exact hcauses

/-- PLAN L3: the `maxSlot` twin of `min_canonical`. -/
theorem max_canonical (st : State) (i j k : Nat) :
    ResCanonical (propMax st i j k) := by
  unfold propMax
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

/-- PLAN L6: the `timesSlot` bound propagator `propTimes` is canonical: its
    two corner narrowings and eight guarded sign narrowings all carry
    explicit cause clauses whose literals are order literals. -/
theorem times_canonical (st : State) (i j k : Nat) :
    ResCanonical (propTimes st i j k) := by
  unfold propTimes
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    rcases times_sign_arm hr with hcorner | hcorner |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ |
      ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩ | ⟨-, -, hr⟩
    · rw [hcorner]; exact narrowLo_canonical st (by canonical_clause)
    · rw [hcorner]; exact narrowHi_canonical st (by canonical_clause)
    · rw [hr]; exact narrowLo_canonical st (by canonical_clause)
    · rw [hr]; exact narrowHi_canonical st (by canonical_clause)
    · rw [hr]; exact narrowHi_canonical st (by canonical_clause)
    · rw [hr]; exact narrowLo_canonical st (by canonical_clause)
    · rw [hr]; exact narrowLo_canonical st (by canonical_clause)
    · rw [hr]; exact narrowHi_canonical st (by canonical_clause)
    · rw [hr]; exact narrowHi_canonical st (by canonical_clause)
    · rw [hr]; exact narrowLo_canonical st (by canonical_clause)
  · trivial
/-- PLAN L7: the `absSlot` bound propagator `propAbs` is canonical: its five
    narrowings all carry explicit cause clauses whose literals are order
    literals. -/
theorem abs_canonical (st : State) (i k : Nat) :
    ResCanonical (propAbs st i k) := by
  unfold propAbs
  split
  · refine firstEvent_canonical _ ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact narrowHi_canonical st (by canonical_clause)
      | exact narrowLo_canonical st (by canonical_clause)
  · trivial

/-- PLAN L7: the general-arithmetic `divGen` lower-arm reason clause is
    canonical (order literals only, once the operand match unfolds). -/
theorem divReasonLo_canonical (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) :
    ClauseCanonical (divReasonLo o₂ i k d pl ph) := by
  cases o₂ <;>
    simp [ClauseCanonical, Literal.norm, posBool, posLe, negLe, posNe, negNe,
      divReasonLo]

/-- PLAN L7: the general-arithmetic `divGen` upper-arm reason clause is
    canonical. -/
theorem divReasonHi_canonical (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) :
    ClauseCanonical (divReasonHi o₂ i k d pl ph) := by
  cases o₂ <;>
    simp [ClauseCanonical, Literal.norm, posBool, posLe, negLe, posNe, negNe,
      divReasonHi]

/-- PLAN L7: the general-arithmetic `modGen` lower-arm reason clause is
    canonical. -/
theorem modReasonLo_canonical (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) :
    ClauseCanonical (modReasonLo o₂ i k d pl ph) := by
  cases o₂ <;>
    simp [ClauseCanonical, Literal.norm, posBool, posLe, negLe, posNe, negNe,
      modReasonLo]

/-- PLAN L7: the general-arithmetic `modGen` upper-arm reason clause is
    canonical. -/
theorem modReasonHi_canonical (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) :
    ClauseCanonical (modReasonHi o₂ i k d pl ph) := by
  cases o₂ <;>
    simp [ClauseCanonical, Literal.norm, posBool, posLe, negLe, posNe, negNe,
      modReasonHi]

/-- PLAN L7: the general `int_div` bound propagator `propDiv` is
    canonical: its narrowings all carry explicit cause clauses whose
    literals are order literals, and its zero-divisor conflict clause is
    `[]` (a literal divisor) or the value-removal literal `[o_j ≠ 0]`. -/
theorem div_canonical (st : State) (o₁ o₂ r : DomIntArg) :
    ResCanonical (propDiv st o₁ o₂ r) := by
  unfold propDiv
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' => exact clauseCanonical_nil
      | slot j =>
          change ClauseCanonical [posNe j 0]
          canonical_clause
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          refine firstEvent_canonical _ ?_
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact narrowLo_canonical st
              (divReasonLo_canonical o₂ i k d pl ph)
          · exact narrowHi_canonical st
              (divReasonHi_canonical o₂ i k d pl ph)
        · trivial
      · trivial
  · trivial

/-- PLAN L7: the general `int_mod` bound propagator `propMod`, the
    `modGen` twin of `div_canonical`. -/
theorem mod_canonical (st : State) (o₁ o₂ r : DomIntArg) :
    ResCanonical (propMod st o₁ o₂ r) := by
  unfold propMod
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' => exact clauseCanonical_nil
      | slot j =>
          change ClauseCanonical [posNe j 0]
          canonical_clause
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          refine firstEvent_canonical _ ?_
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact narrowLo_canonical st
              (modReasonLo_canonical o₂ i k d pl ph)
          · exact narrowHi_canonical st
              (modReasonHi_canonical o₂ i k d pl ph)
        · trivial
      · trivial
  · trivial


theorem constEq_canonical (st : State) (i : Nat) (v : Value) :
    ResCanonical (LeanFzn.Solver.Propagation.propConstEq st i v) := by
  cases v with
  | int k =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      refine firstEvent_canonical _ ?_
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · exact narrowHi_canonical st (by canonical_clause)
      · exact narrowLo_canonical st (by canonical_clause)
  | bool b =>
      simp only [LeanFzn.Solver.Propagation.propConstEq]
      split
      · split
        · trivial
        · exact ⟨rfl, by canonical_clause⟩
      · change ClauseCanonical [posBool i b]
        canonical_clause
  | _ => trivial

theorem neBoolLit_canonical (p s : Nat) (c : Int) :
    (neBoolLit p s c).norm = neBoolLit p s c := by
  unfold neBoolLit
  split <;> rfl

theorem ne_canonical (st : State) (i j : Nat) : ResCanonical (propNe st i j) := by
  cases hr : propNe st i j with
  | stable => trivial
  | implied l r =>
      rcases propNe_implied_inv hr with
        ⟨x, c, _, rfl, rfl, _, _, _, _⟩ | ⟨y, c, _, rfl, rfl, _, _, _, _⟩
      all_goals
        refine ⟨rfl, ?_⟩
        intro q hq
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | exact neBoolLit_canonical _ _ _
  | conflict c =>
      obtain ⟨x, y, _, _, _, rfl⟩ := propNe_conflict_inv hr
      cases x <;> simp [ResCanonical, ClauseCanonical, neConflictClause,
        Literal.norm, posBool, posNe]

theorem linCauseMinPair_canonical {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMinPair st p = some q) : q.norm = q := by
  unfold linCauseMinPair at h
  split at h
  · cases hd : domMinI (st.domains.getD p.2 Dom.empty) with
    | none => rw [hd] at h; simp at h
    | some mn => rw [hd] at h; simp at h; subst h; rfl
  · split at h
    · cases hd : domMaxI (st.domains.getD p.2 Dom.empty) with
      | none => rw [hd] at h; simp at h
      | some mx => rw [hd] at h; simp at h; subst h; rfl
    · cases h

theorem linCausesMin_canonical (st : State) (rest : List (Int × Nat)) :
    ClauseCanonical (linCausesMin st rest) := by
  intro q hq
  obtain ⟨p, _, hpq⟩ := List.mem_filterMap.mp hq
  exact linCauseMinPair_canonical hpq

theorem linCauseMaxPair_canonical {st : State} {p : Int × Nat} {q : Literal}
    (h : linCauseMaxPair st p = some q) : q.norm = q := by
  unfold linCauseMaxPair at h
  split at h
  · cases hd : domMaxI (st.domains.getD p.2 Dom.empty) with
    | none => rw [hd] at h; simp at h
    | some mx => rw [hd] at h; simp at h; subst h; rfl
  · split at h
    · cases hd : domMinI (st.domains.getD p.2 Dom.empty) with
      | none => rw [hd] at h; simp at h
      | some mn => rw [hd] at h; simp at h; subst h; rfl
    · cases h

theorem linCausesMax_canonical (st : State) (rest : List (Int × Nat)) :
    ClauseCanonical (linCausesMax st rest) := by
  intro q hq
  obtain ⟨p, _, hpq⟩ := List.mem_filterMap.mp hq
  exact linCauseMaxPair_canonical hpq

theorem arm_hi_min_canonical {st : State} {m : Nat} {v : Int}
    {rest : List (Int × Nat)} {res : PropagationResult}
    (hr : res = narrowHi st m v ([posLe m v] ++ linCausesMin st rest)) :
    ResCanonical res := by
  rw [hr]
  exact narrowHi_canonical st
    (clauseCanonical_append (by canonical_clause) (linCausesMin_canonical st rest))

theorem arm_lo_min_canonical {st : State} {m : Nat} {v : Int}
    {rest : List (Int × Nat)} {res : PropagationResult}
    (hr : res = narrowLo st m v ([negLe m (v - 1)] ++ linCausesMin st rest)) :
    ResCanonical res := by
  rw [hr]
  exact narrowLo_canonical st
    (clauseCanonical_append (by canonical_clause) (linCausesMin_canonical st rest))

theorem arm_hi_max_canonical {st : State} {m : Nat} {v : Int}
    {rest : List (Int × Nat)} {res : PropagationResult}
    (hr : res = narrowHi st m v ([posLe m v] ++ linCausesMax st rest)) :
    ResCanonical res := by
  rw [hr]
  exact narrowHi_canonical st
    (clauseCanonical_append (by canonical_clause) (linCausesMax_canonical st rest))

theorem arm_lo_max_canonical {st : State} {m : Nat} {v : Int}
    {rest : List (Int × Nat)} {res : PropagationResult}
    (hr : res = narrowLo st m v ([negLe m (v - 1)] ++ linCausesMax st rest)) :
    ResCanonical res := by
  rw [hr]
  exact narrowLo_canonical st
    (clauseCanonical_append (by canonical_clause) (linCausesMax_canonical st rest))

theorem linLe_canonical (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    ResCanonical (propLinLe2 st coeffs is b) := by
  rcases propLinLe2_emission_inv (res := propLinLe2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩
  · rw [hs]; trivial
  · exact arm_hi_min_canonical hres
  · exact arm_lo_min_canonical hres
  · exact arm_hi_min_canonical hres
  · exact arm_lo_min_canonical hres

theorem clauseCanonical_insertAfterHead {extras c : Clause}
    (he : ClauseCanonical extras) (hc : ClauseCanonical c) :
    ClauseCanonical (insertAfterHead extras c) := by
  intro q hq
  rcases mem_insertAfterHead hq with hq | hq
  · exact hc q hq
  · exact he q hq

theorem resCanonical_augment {extras : Clause} {res : PropagationResult}
    (he : ClauseCanonical extras) (h : ResCanonical res) :
    ResCanonical (augmentRes extras res) := by
  cases res with
  | stable => trivial
  | implied l rs =>
      obtain ⟨hln, hc⟩ := h
      exact ⟨hln, clauseCanonical_insertAfterHead he hc⟩
  | conflict c =>
      exact clauseCanonical_insertAfterHead he h

theorem resCanonical_conflictsOnly {res : PropagationResult}
    (h : ResCanonical res) : ResCanonical (conflictsOnly res) := by
  cases res with
  | stable => trivial
  | implied l rs => trivial
  | conflict c => exact h

theorem linLeReifEscTrue_canonical (r : Nat) :
    ClauseCanonical (linLeReifEscTrue r) := by
  intro q hq
  simp only [linLeReifEscTrue, List.mem_singleton] at hq
  rw [hq]
  rfl

theorem linLeReifEscFalse_canonical (is : List Nat) (r : Nat) :
    ClauseCanonical (linLeReifEscFalse is r) := by
  intro q hq
  rw [linLeReifEscFalse] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rfl
  · obtain ⟨i, -, hq2⟩ := List.mem_flatMap.mp hq
    rcases List.mem_cons.mp hq2 with rfl | hq2
    · rfl
    · rw [List.mem_singleton.mp hq2]
      rfl

theorem linLeReifEscB_canonical (is : List Nat) :
    ClauseCanonical (linLeReifEscB is) := by
  intro q hq
  rw [linLeReifEscB] at hq
  obtain ⟨i, -, hq2⟩ := List.mem_flatMap.mp hq
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · rfl
  · rw [List.mem_singleton.mp hq2]
    rfl

theorem linLeReif_canonical (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    ResCanonical (propLinLeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinLeReif_run_true hlenB h1]
      exact resCanonical_augment (linLeReifEscTrue_canonical r)
        (linLe_canonical st coeffs is b)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinLeReif_run_false hlenB h1 h2]
        exact resCanonical_augment
          (linLeReifEscFalse_canonical is r)
          (linLe_canonical st (coeffs.map (fun c => -c)) is (-(b + 1)))
      · -- PLAN L1b/G1d: the bounds arm's implied pins and their operand
        -- escapes and max-/min-causes
        rw [propLinLeReif_run_b hlenB h1 h2]
        rcases propLinLeReifB_emission_inv
            (res := propLinLeReifB st coeffs is b r) rfl with
          hstable | ⟨-, -, -, -, -, -, -, -, hres⟩ |
          ⟨-, -, -, -, -, -, -, -, hres⟩
        · rw [hstable]
          trivial
        · rw [hres]
          refine ⟨rfl, ?_⟩
          exact clauseCanonical_cons rfl
            (clauseCanonical_append (linLeReifEscB_canonical is)
              (linCausesMax_canonical st (coeffs.zip is)))
        · rw [hres]
          refine ⟨rfl, ?_⟩
          exact clauseCanonical_cons rfl
            (clauseCanonical_append (linLeReifEscB_canonical is)
              (linCausesMin_canonical st (coeffs.zip is)))
  · rw [propLinLeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

/-- PLAN L4: canonical emission of the `leReifSlot` delegation. -/
theorem leReifSlot_canonical (st : State) (i j r : Nat) :
    ResCanonical (propLeReifSlot st i j r) := by
  rcases propLeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resCanonical_augment (extras := [posBool r false])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (le_canonical st i j)
  · rw [he]
    exact resCanonical_augment (extras := [posBool r true])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (lt_canonical st j i)
  · rw [he]; trivial

/-- PLAN G1: canonical emission of the strengthened `leReifSlot` run; the
    bounds arm's pivot and both cause literals are in normal form. -/
theorem leReifSlotB_canonical (st : State) (i j r : Nat) :
    ResCanonical (propLeReifSlotB st i j r) := by
  rcases propLeReifSlotB_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩
  · rw [he]
    exact resCanonical_augment (extras := [posBool r false])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (le_canonical st i j)
  · rw [he]
    exact resCanonical_augment (extras := [posBool r true])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (lt_canonical st j i)
  · rw [he]
    rcases propLeReifB_cases st i j r with
      hstable | ⟨-, -, -, -, mn_i, mx_i, mn_j, mx_j,
        hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩ |
      ⟨-, -, -, -, mn_i, mx_i, mn_j, mx_j,
        hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩
    · rw [hstable]; trivial
    · rw [hres]
      exact ⟨posBool_norm r true, clauseCanonical_cons (posBool_norm r true)
        (clauseCanonical_cons (negLe_norm i mx_i)
          (clauseCanonical_cons (posLe_norm j (mn_j - 1)) clauseCanonical_nil))⟩
    · rw [hres]
      exact ⟨posBool_norm r false, clauseCanonical_cons (posBool_norm r false)
        (clauseCanonical_cons (posLe_norm i (mn_i - 1))
          (clauseCanonical_cons (negLe_norm j mx_j) clauseCanonical_nil))⟩

/-- PLAN G1-B: canonical emission of the `bool2intSlot` channel propagator;
    the `implyBool` arms are canonical in their implied and conflict shapes. -/
theorem bool2intSlot_canonical (st : State) (i k : Nat) :
    ResCanonical (propBool2intSlot st i k) := by
  rcases propBool2intSlot_cases st i k with hstable | ⟨-, w, hfb, he⟩ | ⟨-, w, hfb, he⟩ |
    ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ | ⟨w, hfb, he⟩ | ⟨mx, mn, -, -, -, he⟩ |
    ⟨mx, mn, -, -, -, he⟩
  · rw [hstable]; trivial
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons (posBool_norm i false) clauseCanonical_nil)⟩
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons (posBool_norm i true) clauseCanonical_nil)⟩
  · rw [he]
    exact clauseCanonical_cons (posBool_norm i true)
      (clauseCanonical_cons (posBool_norm i false) clauseCanonical_nil)
  · rw [he]
    unfold implyBool
    by_cases hmem : valueMemB (.bool false) (slotEnum st.domains i) = true
    · rw [if_pos hmem]
      by_cases heq : valuesEqB (slotEnum st.domains i) [.bool false] = true
      · rw [if_pos heq]; trivial
      · rw [if_neg heq]
        exact ⟨posBool_norm i false, clauseCanonical_cons (posBool_norm i false)
          (clauseCanonical_cons rfl clauseCanonical_nil)⟩
    · rw [if_neg hmem]
      exact clauseCanonical_cons (posBool_norm i false)
        (clauseCanonical_cons rfl clauseCanonical_nil)
  · rw [he]
    unfold implyBool
    by_cases hmem : valueMemB (.bool true) (slotEnum st.domains i) = true
    · rw [if_pos hmem]
      by_cases heq : valuesEqB (slotEnum st.domains i) [.bool true] = true
      · rw [if_pos heq]; trivial
      · rw [if_neg heq]
        exact ⟨posBool_norm i true, clauseCanonical_cons (posBool_norm i true)
          (clauseCanonical_cons rfl clauseCanonical_nil)⟩
    · rw [if_neg hmem]
      exact clauseCanonical_cons (posBool_norm i true)
        (clauseCanonical_cons rfl clauseCanonical_nil)
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · rw [he]
    exact clauseCanonical_cons (negLe_norm k (-1)) clauseCanonical_nil
  · rw [he]
    exact clauseCanonical_cons (posLe_norm k 1) clauseCanonical_nil

/-- PLAN G1c: canonical emission of the constant-table element propagator;
    the removal pivots and causes are in normal form. -/
theorem arrayIntElementSlot_canonical (st : State) (xs : List Int) (i k : Nat) :
    ResCanonical (propArrayIntElement st xs i k) := by
  rcases propArrayIntElement_cases st xs i k with hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, v, w, hidx, hent, hfb, he⟩ | ⟨v, idx, hk, hfb, he⟩ |
    ⟨idx, hfb, he⟩ | ⟨idx, v, hg, hfb, hent, he⟩
  · rw [hstable]; trivial
  · rw [he]
    exact clauseCanonical_cons rfl clauseCanonical_nil
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl clauseCanonical_nil)⟩
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl clauseCanonical_nil)⟩
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl clauseCanonical_nil)⟩

/-- A mapped list of `negNe · w` literals is canonical. -/
theorem avie_map_negNe_canonical (is : List Nat) (w : Int) :
    ClauseCanonical (is.map (fun j => negNe j w)) := by
  intro q hq
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
  exact (negNe_norm j w).symm

/-- PLAN §3.3: canonical emission of the variable-table element
    propagator; the removal pivots and causes are in normal form. -/
theorem arrayVarIntElementSlot_canonical (st : State) (is : List Nat)
    (i k : Nat) : ResCanonical (propArrayVarIntElement st is i k) := by
  rcases propArrayVarIntElement_cases st is i k with
    hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, j, w, hidx, hent, hfb, he⟩ |
    ⟨idx, j, w, hidx, hent, hfbK, hfb, he⟩ |
    ⟨idx, v, hk, hnone, hfb, he⟩ |
    ⟨idx, v, j, hk, hent, hvm, hfb, he⟩ |
    ⟨idx, hnone, hfb, he⟩ |
    ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, he⟩ |
    ⟨idx, j, mx, mn, hent, hmx, hmn, hlt, hfb, he⟩ |
    ⟨idx, j, w, hent, hdj, hvm, hfb, he⟩ |
    ⟨w, hfbOut, hfbBelow, hfbAbove, hfbSingle, hfbw, he⟩
  · rw [hstable]; trivial
  · -- pinned-index out-of-range conflict: `[posNe i idx]`
    rw [he]
    exact clauseCanonical_cons rfl clauseCanonical_nil
  · -- pinned-index target removal: `[posNe k w, posNe i idx, negNe j w]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- pinned-index entry removal: `[posNe j w, posNe i idx, negNe k w]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- pinned-target out-of-range removal: `[posNe i idx]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · -- pinned-target entry removal:
    -- `[posNe i idx, posNe k v, negNe j v]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- unpinned out-of-range removal: `[posNe i idx]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · -- below-hull removal:
    -- `[posNe i idx, negLe j mx, posLe k (mn - 1)]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- above-hull removal:
    -- `[posNe i idx, negLe k mx, posLe j (mn - 1)]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- singleton-entry removal: `[posNe i idx, posNe j w, negNe k w]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons rfl (clauseCanonical_cons rfl
        clauseCanonical_nil))⟩
  · -- no-support removal: `posNe k w :: is.map (negNe · w)`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (avie_map_negNe_canonical is w)⟩

/-- A mapped list of `posBool · b` literals is canonical. -/
theorem avbe_map_posBool_canonical (is : List Nat) (b : Bool) :
    ClauseCanonical (is.map (fun j => posBool j b)) := by
  intro q hq
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
  exact posBool_norm j b

/-- PLAN §3.3 item 2: canonical emission of the variable-table Boolean
    element propagator; the Boolean pivots and causes are in normal
    form. -/
theorem arrayVarBoolElementSlot_canonical (st : State) (is : List Nat)
    (i k : Nat) : ResCanonical (propArrayVarBoolElement st is i k) := by
  rcases propArrayVarBoolElement_cases st is i k with
    hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, j, b, hidx, hent, hfb, he⟩ |
    ⟨idx, j, b, hidx, hent, hfbK, hfb, he⟩ |
    ⟨idx, v, hk, hnone, hfb, he⟩ |
    ⟨idx, v, j, hk, hent, hvm, hfb, he⟩ |
    ⟨idx, hnone, hfb, he⟩ |
    ⟨idx, j, b, hent, hdj, hvm, hfb, he⟩ |
    ⟨b, hfbOut, hfbSingle, hfbw, he⟩
  · rw [hstable]; trivial
  · -- pinned-index out-of-range conflict: `[posNe i idx]`
    rw [he]
    exact clauseCanonical_cons rfl clauseCanonical_nil
  · -- pinned-index target removal through the emitter
    rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm k (!b))
        (clauseCanonical_cons rfl
          (clauseCanonical_cons (posBool_norm j b) clauseCanonical_nil)))
  · -- pinned-index entry removal through the emitter
    rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm j (!b))
        (clauseCanonical_cons rfl
          (clauseCanonical_cons (posBool_norm k b) clauseCanonical_nil)))
  · -- pinned-target out-of-range removal: `[posNe i idx]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · -- pinned-target entry removal:
    -- `[posNe i idx, posBool k (!v), posBool j v]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons (posBool_norm k (!v))
        (clauseCanonical_cons (posBool_norm j v) clauseCanonical_nil))⟩
  · -- unpinned out-of-range removal: `[posNe i idx]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl clauseCanonical_nil⟩
  · -- opposite-singleton removal:
    -- `[posNe i idx, posBool j (!b), posBool k b]`
    rw [he]
    exact ⟨rfl, clauseCanonical_cons rfl
      (clauseCanonical_cons (posBool_norm j (!b))
        (clauseCanonical_cons (posBool_norm k b) clauseCanonical_nil))⟩
  · -- no-support removal through the emitter
    rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm k (!b))
        (avbe_map_posBool_canonical is b))

/-- A mapped list of `posBool · false` literals is canonical. -/
theorem aba_map_false_canonical (is : List Nat) :
    ClauseCanonical (is.map (fun i => posBool i false)) := by
  intro q hq
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
  exact (posBool_norm i false).symm

/-- PLAN G1e: canonical emission of the array-Boolean conjunction
    propagator; every emitted clause is a list of positive Boolean
    literals. -/
theorem arrayBoolAndSlot_canonical (st : State) (is : List Nat) (k : Nat) :
    ResCanonical (propArrayBoolAnd st is k) := by
  rcases propArrayBoolAnd_cases st is k with
    hstable | ⟨hall, he⟩ | ⟨i, hfb, he⟩ | ⟨hk, i, hfb, he⟩ |
    ⟨hkf, i, his, hb, he⟩
  · rw [hstable]; trivial
  · rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm k true)
        (aba_map_false_canonical is))
  · rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm k false)
        (clauseCanonical_cons (posBool_norm i true) clauseCanonical_nil))
  · rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm i true)
        (clauseCanonical_cons (posBool_norm k false) clauseCanonical_nil))
  · rw [he]
    exact implyBool_canonical st
      (clauseCanonical_cons (posBool_norm i false)
        (clauseCanonical_cons (posBool_norm k true) clauseCanonical_nil))

/-- PLAN L4: canonical emission of the `eqReifSlot` delegation. -/
theorem eqReifSlot_canonical (st : State) (i j r : Nat) :
    ResCanonical (propEqReifSlot st i j r) := by
  rcases propEqReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resCanonical_augment (extras := [posBool r false])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (eq_canonical st i j)
  · rw [he]
    exact resCanonical_augment (extras := [posBool r true])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (ne_canonical st i j)
  · rw [he]; trivial

/-- PLAN L4: canonical emission of the `neReifSlot` delegation. -/
theorem neReifSlot_canonical (st : State) (i j r : Nat) :
    ResCanonical (propNeReifSlot st i j r) := by
  rcases propNeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resCanonical_augment (extras := [posBool r false])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (ne_canonical st i j)
  · rw [he]
    exact resCanonical_augment (extras := [posBool r true])
      (fun q hq => by rw [List.mem_singleton.mp hq]; rfl) (eq_canonical st i j)
  · rw [he]; trivial

theorem linEq_canonical (st : State) (coeffs : List Int) (is : List Nat) (b : Int) :
    ResCanonical (propLinEq2 st coeffs is b) := by
  rcases propLinEq2_emission_inv (res := propLinEq2 st coeffs is b) rfl with
    hs | ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, hmem, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, hmem, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, c, hmem, -, hrest, -, -, hres⟩ |
    ⟨m, i, rest, lr, c, hmem, -, hrest, -, -, hres⟩ | ⟨m, i, rest, hr, c, hmem, -, hrest, -, -, hres⟩
  · rw [hs]; trivial
  · exact arm_hi_min_canonical hres
  · exact arm_lo_max_canonical hres
  · exact arm_lo_min_canonical hres
  · exact arm_hi_max_canonical hres
  · exact arm_hi_min_canonical hres
  · exact arm_lo_max_canonical hres
  · exact arm_lo_min_canonical hres
  · exact arm_hi_max_canonical hres

/-- PLAN L5: canonical emission of the `linEqReif` delegation. -/
theorem linEqReif_canonical (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    ResCanonical (propLinEqReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinEqReif_run_true hlenB h1]
      exact resCanonical_augment (linLeReifEscTrue_canonical r)
        (linEq_canonical st coeffs is b)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinEqReif_run_false hlenB h1 h2]
        exact resCanonical_conflictsOnly (resCanonical_augment
          (linLeReifEscFalse_canonical is r) (linNe_canonical st coeffs is b))
      · rw [propLinEqReif_run_stable hlenB h1 h2]
        trivial
  · rw [propLinEqReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

/-- PLAN L5: canonical emission of the `linNeReif` delegation. -/
theorem linNeReif_canonical (st : State) (coeffs : List Int) (is : List Nat)
    (b : Int) (r : Nat) :
    ResCanonical (propLinNeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinNeReif_run_true hlenB h1]
      exact resCanonical_augment (linLeReifEscTrue_canonical r)
        (linNe_canonical st coeffs is b)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinNeReif_run_false hlenB h1 h2]
        exact resCanonical_conflictsOnly (resCanonical_augment
          (linLeReifEscFalse_canonical is r) (linEq_canonical st coeffs is b))
      · rw [propLinNeReif_run_stable hlenB h1 h2]
        trivial
  · rw [propLinNeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

theorem slotHall_canonical {s : Nat} {d : Domain} {cl : Clause}
    (h : slotHall s d = some cl) : ClauseCanonical cl := by
  unfold slotHall at h
  split at h
  · cases h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
      · injection h with h1
        subst h1
        intro q hq
        simp only [List.mem_cons, List.mem_map] at hq
        rcases hq with rfl | rfl | ⟨a, -, rfl⟩
        · rfl
        · rfl
        · rfl

theorem hallClauses_canonical (doms : List Domain) :
    ∀ (ss : List Nat) (c : Clause), hallClauses doms ss = some c → ClauseCanonical c := by
  intro ss
  induction ss with
  | nil =>
      intro c h
      simp only [hallClauses, Option.some.injEq] at h
      subst c
      exact clauseCanonical_nil
  | cons s ss ih =>
      intro c h
      unfold hallClauses at h
      split at h
      · rename_i c1 c2 h1 h2
        injection h with heq
        subst c
        exact clauseCanonical_append (slotHall_canonical h1) (ih c2 h2)
      · cases h

theorem hallClause_canonical (doms : List Domain) (is : List Nat) :
    ClauseCanonical (hallClause doms is) := by
  unfold hallClause
  split
  · rename_i c hc
    exact hallClauses_canonical doms _ c hc
  · exact clauseCanonical_nil

theorem allDiff_canonical (st : State) (is : List Nat) :
    ResCanonical (propAllDiffLCG st is) := by
  cases hr : propAllDiffLCG st is with
  | stable => trivial
  | implied l r =>
      obtain ⟨i, j, c, -, hl, hr2⟩ := propAllDiffLCG_implied_inv hr
      subst hl
      subst hr2
      exact ⟨rfl, fun q hq => (allDiffElimClause_norm hq).symm⟩
  | conflict c =>
      obtain ⟨_, rfl⟩ := propAllDiffLCG_conflict_inv hr
      exact hallClause_canonical st.domains is

/-- Every registered family in the LCG gate has canonical implied/conflict
emissions at every state, derived from its actual runtime equations. -/
theorem emissionCanonical_of_families {dcs : List DomConstraint}
    (hfam : ∀ dc ∈ dcs, LeanFzn.Solver.UIP.LcgFamilies.lcgFamB dc = true) :
    EmissionCanonical (dcs.filterMap propagatorOfProved) := by
  intro p hp st
  obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hp
  have hf := hfam dc hdc
  cases dc with
  | eqSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact eq_canonical st i j
  | neSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact ne_canonical st i j
  | leSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact le_canonical st i j
  | ltSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact lt_canonical st i j
  | constEq i v =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact constEq_canonical st i v
  | plusSlot i j k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact plus_canonical st i j k
  | leConstHi i c =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact leConstHi_canonical st i c
  | leConstLo i c =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact leConstLo_canonical st i c
  | ltConstHi i c =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact ltConstHi_canonical st i c
  | ltConstLo i c =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact ltConstLo_canonical st i c
  | allDiff is =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact allDiff_canonical st is
  | linLe coeffs is b =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linLe_canonical st coeffs is b
  | linEq coeffs is b =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linEq_canonical st coeffs is b
  | boolNotSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact boolNot_canonical st i j
  | boolAndSlot i j k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact boolAnd_canonical st i j k
  | boolOrSlot i j k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact boolOr_canonical st i j k
  | minSlot i j k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact min_canonical st i j k
  | maxSlot i j k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact max_canonical st i j k
  | linNe coeffs is b =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linNe_canonical st coeffs is b
  | absSlot i k =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propAbs`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact abs_canonical st i k
  | divGen o₁ o₂ r =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propDiv`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact div_canonical st o₁ o₂ r
  | modGen o₁ o₂ r =>
      -- PLAN L7: the registered propagator is the bound propagator
      -- `propMod`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact mod_canonical st o₁ o₂ r
  | timesSlot i j k =>
      -- PLAN L6: the registered propagator is the bound propagator
      -- `propTimes`.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact times_canonical st i j k
  | boolClauseSlot ps ns =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | arrayBoolAndSlot is k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact arrayBoolAndSlot_canonical st is k
  | bool2intSlot i k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact bool2intSlot_canonical st i k
  | boolEqSlot i j =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | arrayIntElementSlot xs i k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact arrayIntElementSlot_canonical st xs i k
  | arrayVarIntElementSlot is i k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved,
        Option.some.injEq] at hprop
      subst hprop
      exact arrayVarIntElementSlot_canonical st is i k
  | arrayVarBoolElementSlot is i k =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved,
        Option.some.injEq] at hprop
      subst hprop
      exact arrayVarBoolElementSlot_canonical st is i k
  | leReifSlot i j r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact leReifSlotB_canonical st i j r
  | eqReifSlot i j r =>
      -- PLAN L4: the pinned-direction `propEqReifSlot` delegation.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact eqReifSlot_canonical st i j r
  | neReifSlot i j r =>
      -- PLAN L4: the pinned-direction `propNeReifSlot` delegation.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact neReifSlot_canonical st i j r
  | linLeReif coeffs is b r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linLeReif_canonical st coeffs is b r
  | linEqReif coeffs is b r =>
      -- PLAN L5: the pinned-direction `propLinEqReif` delegation.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linEqReif_canonical st coeffs is b r
  | linNeReif coeffs is b r =>
      -- PLAN L5: the pinned-direction `propLinNeReif` delegation.
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact linNeReif_canonical st coeffs is b r
  | minPair o₀ o₁ r | maxPair o₀ o₁ r =>
      cases o₀ <;> cases o₁ <;> cases r <;>
        (simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
         subst hprop
         first
           | exact min_canonical st _ _ _
           | exact max_canonical st _ _ _
           | simpa only [Propagator.run_mk] using propCheck_canonical _ st)
  | maxGen os r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact maxGen_canonical st os r
  | minGen os r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved, Option.some.injEq] at hprop
      subst hprop
      exact minGen_canonical st os r
  | setInSlot i s =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | setInReifSlot i s r =>
      simp only [LeanFzn.Solver.Propagation.propagatorOfProved] at hprop
      exact absurd hprop (by intro hc; cases hc)

end LeanFzn.Solver.UIP.LcgCanonicalFamilies
