/-
File: LeanFzn/Solver/UIP/Proofs/LcgFamiliesRun.lean
U1a/U1b assembly: `PropSemContract` for `propagatorOfProved dc` for every
constraint of the gate `lcgFamB`, and `RunSemContract` for the gate "all
constraints in proved families", relative to the named frame-explanation
invariant `FrameExplainedFull` (premise, NOT proved here: it is the
`syncAll` coverage fact, U1c).

Every constructor is in the gate `lcgFamB` since PLAN L0b1: the seventeen
families without a dedicated pruning propagator register `propCheck`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesLin
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesNe
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgFamiliesAllDiff
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgClampTransfer
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp

namespace LeanFzn.Solver.UIP.LcgFamilies

variable {leaf : Assignment → Bool}

/-- The full frame-explanation invariant (bounds, Boolean absence, integer
fixing, interior holes). -/
structure FrameExplainedFull (orig : List Domain) (bs : BranchState leaf) : Prop where
  base : FrameExplained orig bs
  holes : HolesExpl orig bs.trail (Frame.domains bs.frame)

/-- Semantic soundness of `propCheck` (PLAN L0a/L0b1; re-exported as
`LcgPropCheck.propCheck_sem`): placed here because `propSem_of_family`
needs it and `LcgPropCheck` imports this module. -/
theorem propCheck_sem_aux {orig : List Domain} {bs : BranchState leaf}
    (hF : FrameExplainedFull orig bs) (dc : DomConstraint) :
    ResSem orig bs.trail ((propCheck dc).run (frameState bs.frame)) := by
  cases hres : (propCheck dc).run (frameState bs.frame) with
  | stable => trivial
  | implied l r => exact (propCheck_implied_elim hres).elim
  | conflict c =>
      intro q hq
      obtain ⟨-, -, hc⟩ := propCheck_conflict_inv hres
      rw [hc] at hq
      obtain ⟨s, -, hbind⟩ := mem_propCheckConflict_iff.mp hq
      obtain ⟨v, hv, hv2⟩ := Option.bind_eq_some_iff.mp hbind
      cases v with
      | int c' =>
          simp only [singletonLit] at hv2
          injection hv2 with hv2
          rw [← hv2]
          exact hF.base.fix s c' (frameSingleton_iff.mp hv)
      | bool b =>
          simp only [singletonLit] at hv2
          injection hv2 with hv2
          rw [← hv2]
          have habs : valueMemB (.bool (!b)) (Dom.enum ((frameState bs.frame).domains.getD s Dom.empty)) = false := by
            rw [frameSingleton_iff.mp hv]
            cases b <;> decide
          exact hF.base.absent s (!b) habs
      | setOfInt w => simp [singletonLit] at hv2
      | array w => simp [singletonLit] at hv2

/-- The constraint families covered by the semantic contract.  Since PLAN
    L0b1 every constructor is covered: the seventeen families without a
    dedicated pruning propagator (`minSlot`, `maxSlot`, `absSlot`,
    `timesSlot`, `linNe`, the reified, pair, `divGen`/`modGen` and
    `maxGen`/`minGen` families) register the checking propagator
    `propCheck`; `bool2intSlot` (PLAN G1-B) registers the explained
    channel propagator `propBool2intSlot`; the six leaf-enforced families
    (`boolClauseSlot`, `arrayBoolAndSlot`, `boolEqSlot`, the three element
    families) have no propagator and stay in the gate as before. -/
def lcgFamB : DomConstraint → Bool
  | .minSlot .. => true
  | .maxSlot .. => true
  | .absSlot .. => true
  | .timesSlot .. => true
  | .linNe .. => true
  | .eqReifSlot .. => true
  | .leReifSlot .. => true
  | .neReifSlot .. => true
  | .linEqReif .. => true
  | .linLeReif .. => true
  | .linNeReif .. => true
  | .minPair .. => true
  | .maxPair .. => true
  | .divGen .. => true
  | .modGen .. => true
  | .maxGen .. => true
  | .minGen .. => true
  | _ => true

theorem resSem_augment {orig : List Domain} {pre : List TrailEntry}
    {res : PropagationResult} {extras : Clause}
    (h : ResSem orig pre res)
    (he : ∀ q ∈ extras, SemFalsifiedBefore orig pre q) :
    ResSem orig pre (augmentRes extras res) := by
  cases res with
  | stable => trivial
  | implied l rs =>
      obtain ⟨hmem, hrest⟩ := h
      refine ⟨?_, ?_⟩
      · exact mem_insertAfterHead_of_mem hmem
      · intro q hq hqne
        rcases mem_insertAfterHead hq with hq | hq
        · exact hrest q hq hqne
        · exact he q hq
  | conflict c =>
      intro q hq
      rcases mem_insertAfterHead hq with hq | hq
      · exact h q hq
      · exact he q hq

theorem resSem_conflictsOnly {orig : List Domain} {pre : List TrailEntry}
    {res : PropagationResult} (h : ResSem orig pre res) :
    ResSem orig pre (conflictsOnly res) := by
  cases res with
  | stable => trivial
  | implied l rs => trivial
  | conflict c => exact h

theorem valueMemB_bool_eq_false_of_ints {d : List Value} {b : Bool}
    (h : ∀ v ∈ d, ∃ k : Int, v = .int k) :
    valueMemB (.bool b) d = false := by
  by_cases hc : valueMemB (.bool b) d = true
  · obtain ⟨k, hk⟩ := h (.bool b) (valueMemB_iff.mp hc)
    exact absurd hk (by simp)
  · exact Bool.eq_false_iff.mpr hc

theorem linLeReifEscTrue_sf {orig : List Domain} {pre : List TrailEntry}
    {st : State} {r : Nat}
    (hA : AbsentExpl orig pre st.domains)
    (hpin : domBoolPin st.domains r true = true) :
    ∀ q ∈ linLeReifEscTrue r, SemFalsifiedBefore orig pre q := by
  intro q hq
  simp only [linLeReifEscTrue, List.mem_singleton] at hq
  rw [hq]
  exact pins_of_absent hA hpin

theorem linLeReifEscFalse_sf {orig : List Domain} {pre : List TrailEntry}
    {st : State} {is : List Nat} {r : Nat}
    (hA : AbsentExpl orig pre st.domains)
    (hpin : domBoolPin st.domains r false = true)
    (hg : domsIntOnlyB st.domains is = true) :
    ∀ q ∈ linLeReifEscFalse is r, SemFalsifiedBefore orig pre q := by
  intro q hq
  rw [linLeReifEscFalse] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact pins_of_absent hA hpin
  · obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
    obtain ⟨-, -, hint⟩ := domsIntOnlyB_eq hg i hi
    have hno : valueMemB (.bool false) (slotEnum st.domains i) = false :=
      valueMemB_bool_eq_false_of_ints hint
    rcases List.mem_cons.mp hq2 with rfl | hq2
    · exact hA i false hno
    · rw [List.mem_singleton.mp hq2]
      exact hA i true (by
        rw [valueMemB_bool_eq_false_of_ints
          (b := true) (d := slotEnum st.domains i) hint])

/-- The bounds arm's operand escapes are falsified before the trail: the
    operand domains are integer-only, so no operand slot can read a
    Boolean (`AbsentExpl` turns that into falsity). -/
theorem linLeReifEscB_sf {orig : List Domain} {pre : List TrailEntry}
    {st : State} {is : List Nat}
    (hA : AbsentExpl orig pre st.domains)
    (hg : domsIntOnlyB st.domains is = true) :
    ∀ q ∈ linLeReifEscB is, SemFalsifiedBefore orig pre q := by
  intro q hq
  rw [linLeReifEscB] at hq
  obtain ⟨i, hi, hq2⟩ := List.mem_flatMap.mp hq
  obtain ⟨-, -, hint⟩ := domsIntOnlyB_eq hg i hi
  have hno : valueMemB (.bool false) (slotEnum st.domains i) = false :=
    valueMemB_bool_eq_false_of_ints hint
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact hA i false hno
  · rw [List.mem_singleton.mp hq2]
    exact hA i true (by
      rw [valueMemB_bool_eq_false_of_ints
        (b := true) (d := slotEnum st.domains i) hint])

theorem propLinLeReif_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains) :
    ResSem orig pre (propLinLeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinLeReif_run_true hlenB h1]
      exact resSem_augment (propLinLe2_sem hB coeffs is b)
        (linLeReifEscTrue_sf hA h1)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinLeReif_run_false hlenB h1 h2]
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        exact resSem_augment
          (propLinLe2_sem hB (coeffs.map (fun c => -c)) is (-(b + 1)))
          (linLeReifEscFalse_sf hA hpf hg)
      · -- PLAN L1b/G1d: the unpinned arm's IMPLIED pins over the operand
        -- escapes and the max-/min-causes
        rw [propLinLeReif_run_b hlenB h1 h2]
        rcases propLinLeReifB_emission_inv
            (res := propLinLeReifB st coeffs is b r) rfl with
          hstable | ⟨-, -, -, hg, -, -, -, -, hres⟩ |
          ⟨-, -, -, hg, -, -, -, -, hres⟩
        · rw [hstable]
          trivial
        · rw [hres]
          refine reasonOK_of_bool List.mem_cons_self ?_
          intro q hq hne
          rcases List.mem_cons.mp hq with rfl | hq
          · exact absurd rfl hne
          · rcases List.mem_append.mp hq with hq | hq
            · exact linLeReifEscB_sf hA hg q hq
            · exact linCausesMax_sf hB _ q hq
        · rw [hres]
          refine reasonOK_of_bool List.mem_cons_self ?_
          intro q hq hne
          rcases List.mem_cons.mp hq with rfl | hq
          · exact absurd rfl hne
          · rcases List.mem_append.mp hq with hq | hq
            · exact linLeReifEscB_sf hA hg q hq
            · exact linCausesMin_sf hB _ q hq
  · rw [propLinLeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

/-- PLAN L3: `propMin`'s result contract (`min x y = z` over
    slots `i j k`): each of the four narrowings' pivot literals is
    semantically falsified by the state's bounds (a cause literal on
    `i`, `j` or `k`), so every arm's reason is a semantically valid
    contract and non-firing arms are `.stable`. -/
theorem propMin_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (i j k : Nat) :
    ResSem orig pre (propMin st i j k) := by
  unfold propMin
  split
  · rename_i xi' xi yj' yj zk' h1 h2 h3 h4 h5
    have b1 : SemFalsifiedBefore orig pre (posLe i (xi' - 1)) := (hB i).2 xi' h1
    have b2 : SemFalsifiedBefore orig pre (negLe i xi) := (hB i).1 xi h2
    have b3 : SemFalsifiedBefore orig pre (posLe j (yj' - 1)) := (hB j).2 yj' h3
    have b4 : SemFalsifiedBefore orig pre (negLe j yj) := (hB j).1 yj h4
    have b5 : SemFalsifiedBefore orig pre (posLe k (zk' - 1)) := (hB k).2 zk' h5
    apply firstEvent_sem
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · trivial

/-- PLAN L3: `propMax`'s result contract (the dual of `propMin_sem`,
    reading `k`'s upper bound and narrowing `i`/`j` from above). -/
theorem propMax_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (i j k : Nat) :
    ResSem orig pre (propMax st i j k) := by
  unfold propMax
  split
  · rename_i xi' xi yj' yj zk h1 h2 h3 h4 h5
    have b1 : SemFalsifiedBefore orig pre (posLe i (xi' - 1)) := (hB i).2 xi' h1
    have b2 : SemFalsifiedBefore orig pre (negLe i xi) := (hB i).1 xi h2
    have b3 : SemFalsifiedBefore orig pre (posLe j (yj' - 1)) := (hB j).2 yj' h3
    have b4 : SemFalsifiedBefore orig pre (negLe j yj) := (hB j).1 yj h4
    have b5 : SemFalsifiedBefore orig pre (negLe k zk) := (hB k).1 zk h5
    apply firstEvent_sem
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
  · trivial

/-- PLAN C9c: the lower-bound causes of an operand list are semantically
    falsified by the state bounds. -/
theorem argLoCause_sf {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (os : List DomIntArg) :
    ∀ q ∈ os.flatMap (argLoCause st), SemFalsifiedBefore orig pre q := by
  intro q hq
  obtain ⟨o, ho, hq2⟩ := List.mem_flatMap.mp hq
  cases o with
  | lit k => cases hq2
  | slot i =>
      cases hl : domMinI (st.domains.getD i Dom.empty) with
      | none =>
          rw [argLoCause_slot_none hl] at hq2
          cases hq2
      | some l =>
          rw [argLoCause_slot_some hl] at hq2
          rw [List.mem_singleton] at hq2
          rw [hq2]
          exact (hB i).2 l hl

/-- PLAN C9c: the upper-bound causes of an operand list are semantically
    falsified by the state bounds. -/
theorem argHiCause_sf {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (os : List DomIntArg) :
    ∀ q ∈ os.flatMap (argHiCause st), SemFalsifiedBefore orig pre q := by
  intro q hq
  obtain ⟨o, ho, hq2⟩ := List.mem_flatMap.mp hq
  cases o with
  | lit k => cases hq2
  | slot i =>
      cases hh : domMaxI (st.domains.getD i Dom.empty) with
      | none =>
          rw [argHiCause_slot_none hh] at hq2
          cases hq2
      | some h =>
          rw [argHiCause_slot_some hh] at hq2
          rw [List.mem_singleton] at hq2
          rw [hq2]
          exact (hB i).1 h hh

/-- PLAN C9c: `propMinGen`'s result contract (the n-ary array minimum):
    the two attained-operand narrowings carry the operand bound literals
    as causes, all semantically falsified by the state bounds, so each
    arm's reason is a semantically valid contract and non-firing arms
    are `.stable`. -/
theorem propMinGen_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (os : List DomIntArg) (r : DomIntArg) :
    ResSem orig pre (propMinGen st os r) := by
  unfold propMinGen
  split
  case h_1 => trivial
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      apply firstEvent_sem
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_sem hB List.mem_cons_self (sf_cons _ (argLoCause_sf hB os))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_sem hB List.mem_cons_self (sf_cons _ (argHiCause_sf hB os))
    case h_2 => trivial

/-- PLAN C9c: `propMaxGen`'s result contract (the n-ary array maximum) —
    the twin of `propMinGen_sem`. -/
theorem propMaxGen_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (os : List DomIntArg) (r : DomIntArg) :
    ResSem orig pre (propMaxGen st os r) := by
  unfold propMaxGen
  split
  case h_1 => trivial
  case h_2 =>
    rename_i r' k
    split
    case h_1 =>
      rename_i m_lo m_hi hlo hhi
      apply firstEvent_sem
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact narrowLo_sem hB List.mem_cons_self (sf_cons _ (argLoCause_sf hB os))
      · rw [List.mem_singleton] at hrr
        rw [hrr]
        exact narrowHi_sem hB List.mem_cons_self (sf_cons _ (argHiCause_sf hB os))
    case h_2 => trivial

/-- PLAN L6: `propTimes`'s result contract (`x · y = z` over slots `i j k`):
    the two corner narrowings carry the state-bound causes of `x`/`y`, and
    the eight guarded sign narrowings additionally read `z`'s extrema through
    the monotonicity of the order literals; non-firing arms are `.stable`. -/
theorem propTimes_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (i j k : Nat) :
    ResSem orig pre (propTimes st i j k) := by
  unfold propTimes
  split
  · rename_i xi' xi yj' yj zk' zk h1 h2 h3 h4 h5 h6
    have b1 : SemFalsifiedBefore orig pre (posLe i (xi' - 1)) := (hB i).2 xi' h1
    have b2 : SemFalsifiedBefore orig pre (negLe i xi) := (hB i).1 xi h2
    have b3 : SemFalsifiedBefore orig pre (posLe j (yj' - 1)) := (hB j).2 yj' h3
    have b4 : SemFalsifiedBefore orig pre (negLe j yj) := (hB j).1 yj h4
    have b5 : SemFalsifiedBefore orig pre (posLe k (zk' - 1)) := (hB k).2 zk' h5
    have b6 : SemFalsifiedBefore orig pre (negLe k zk) := (hB k).1 zk h6
    apply firstEvent_sem
    intro r hr
    rcases times_sign_arm hr with hcorner | hcorner |
      ⟨hyj', hzk', hr⟩ | ⟨hyj', hzk, hr⟩ |
      ⟨hyj, hzk', hr⟩ | ⟨hyj, hzk, hr⟩ |
      ⟨hxi', hzk', hr⟩ | ⟨hxi', hzk, hr⟩ |
      ⟨hxi, hzk', hr⟩ | ⟨hxi, hzk, hr⟩
    · -- z ≥ cornerMin xi' xi yj' yj (causes: x ≥ xi', x ≤ xi, y ≥ yj', y ≤ yj)
      rw [hcorner]
      exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · -- z ≤ cornerMax xi' xi yj' yj (same four causes)
      rw [hcorner]
      exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · -- x ≥ 0 (guards 0 < yj', 0 ≤ zk')
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (posLe k (-1)) :=
        sf_posLe_mono b5 (by omega)
      exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · -- x ≤ 0 (guards 0 < yj', zk ≤ 0)
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (negLe k 0) :=
        sf_negLe_mono b6 (by omega)
      exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · -- x ≤ 0 (guards yj < 0, 0 ≤ zk')
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (posLe k (-1)) :=
        sf_posLe_mono b5 (by omega)
      exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · -- x ≥ 0 (guards yj < 0, zk ≤ 0)
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (negLe k 0) :=
        sf_negLe_mono b6 (by omega)
      exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · -- y ≥ 0 (guards 0 < xi', 0 ≤ zk')
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (posLe k (-1)) :=
        sf_posLe_mono b5 (by omega)
      exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · -- y ≤ 0 (guards 0 < xi', zk ≤ 0)
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (negLe k 0) :=
        sf_negLe_mono b6 (by omega)
      exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · -- y ≤ 0 (guards xi < 0, 0 ≤ zk')
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (posLe k (-1)) :=
        sf_posLe_mono b5 (by omega)
      exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · -- y ≥ 0 (guards xi < 0, zk ≤ 0)
      rw [hr]
      have bk : SemFalsifiedBefore orig pre (negLe k 0) :=
        sf_negLe_mono b6 (by omega)
      exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · trivial

/-- PLAN L7: `propAbs`'s result contract (`r = |x|` over slots `i k`):
    each of the five narrowings' pivot literals is semantically falsified
    by the state's bounds (a cause literal on `i` or `k`), so every arm's
    reason is a semantically valid contract and non-firing arms are
    `.stable`. -/
theorem propAbs_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (i k : Nat) :
    ResSem orig pre (propAbs st i k) := by
  unfold propAbs
  split
  · rename_i xi' xi rk h1 h2 h3
    have b1 : SemFalsifiedBefore orig pre (posLe i (xi' - 1)) := (hB i).2 xi' h1
    have b2 : SemFalsifiedBefore orig pre (negLe i xi) := (hB i).1 xi h2
    have b3 : SemFalsifiedBefore orig pre (negLe k rk) := (hB k).1 rk h3
    apply firstEvent_sem
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowHi_sem hB (by simp) (sf_cons _ (by sfs))
    · exact narrowLo_sem hB (by simp) (sf_cons _ (by sfs))
  · trivial

/-- PLAN L7: `propDiv`'s result contract: the zero-divisor conflict
    clause is either empty (a literal `0` divisor) or the removal
    literal `o_j ≠ 0` of a slot whose domain is exactly `[.int 0]`
    (the `FixExpl` shape); every narrowing's pivot is falsified by the
    result slot's bounds and its causes by the operand bounds
    (`BoundsExpl`, with the divisor slot's extrema from `divPin`). -/
theorem propDiv_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (hF : FixExpl orig pre st.domains)
    (o₁ o₂ r : DomIntArg) :
    ResSem orig pre (propDiv st o₁ o₂ r) := by
  unfold propDiv
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' =>
          intro q hq
          simp [divZeroClause] at hq
      | slot j =>
          intro q hq
          rw [divZeroClause] at hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rw [hq]
          exact hF j 0 (by rw [divPin_slot_dom hpin, hd0])
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          apply firstEvent_sem
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · -- narrowLo
            have bi1 : SemFalsifiedBefore orig pre (posLe i (pl - 1)) :=
              (hB i).2 pl hpl
            have bi2 : SemFalsifiedBefore orig pre (negLe i ph) :=
              (hB i).1 ph hph
            cases o₂ with
            | lit d' =>
                exact narrowLo_sem hB (by simp [divReasonLo])
                  (sf_cons _ (by sfs))
            | slot j =>
                have hmin : domMinI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).1
                have hmax : domMaxI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).2
                have bj1 : SemFalsifiedBefore orig pre (posLe j (d - 1)) :=
                  (hB j).2 d hmin
                have bj2 : SemFalsifiedBefore orig pre (negLe j d) :=
                  (hB j).1 d hmax
                exact narrowLo_sem hB (by simp [divReasonLo])
                  (sf_cons _ (by sfs))
          · -- narrowHi
            have bi1 : SemFalsifiedBefore orig pre (posLe i (pl - 1)) :=
              (hB i).2 pl hpl
            have bi2 : SemFalsifiedBefore orig pre (negLe i ph) :=
              (hB i).1 ph hph
            cases o₂ with
            | lit d' =>
                exact narrowHi_sem hB (by simp [divReasonHi])
                  (sf_cons _ (by sfs))
            | slot j =>
                have hmin : domMinI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).1
                have hmax : domMaxI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).2
                have bj1 : SemFalsifiedBefore orig pre (posLe j (d - 1)) :=
                  (hB j).2 d hmin
                have bj2 : SemFalsifiedBefore orig pre (negLe j d) :=
                  (hB j).1 d hmax
                exact narrowHi_sem hB (by simp [divReasonHi])
                  (sf_cons _ (by sfs))
        · trivial
      · trivial
  · trivial

/-- PLAN L7: `propMod`'s result contract, the `modGen` twin of
    `propDiv_sem`. -/
theorem propMod_sem {orig : List Domain} {pre : List TrailEntry} {st : State}
    (hB : BoundsExpl orig pre st.domains) (hF : FixExpl orig pre st.domains)
    (o₁ o₂ r : DomIntArg) :
    ResSem orig pre (propMod st o₁ o₂ r) := by
  unfold propMod
  split
  · rename_i x d hpin
    split
    · -- the zero-divisor conflict
      rename_i hd0
      cases o₂ with
      | lit d' =>
          intro q hq
          simp [divZeroClause] at hq
      | slot j =>
          intro q hq
          rw [divZeroClause] at hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rw [hq]
          exact hF j 0 (by rw [divPin_slot_dom hpin, hd0])
    · split
      · rename_i i k
        split
        · rename_i pl ph hpl hph
          apply firstEvent_sem
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · -- narrowLo
            have bi1 : SemFalsifiedBefore orig pre (posLe i (pl - 1)) :=
              (hB i).2 pl hpl
            have bi2 : SemFalsifiedBefore orig pre (negLe i ph) :=
              (hB i).1 ph hph
            cases o₂ with
            | lit d' =>
                exact narrowLo_sem hB (by simp [modReasonLo])
                  (sf_cons _ (by sfs))
            | slot j =>
                have hmin : domMinI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).1
                have hmax : domMaxI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).2
                have bj1 : SemFalsifiedBefore orig pre (posLe j (d - 1)) :=
                  (hB j).2 d hmin
                have bj2 : SemFalsifiedBefore orig pre (negLe j d) :=
                  (hB j).1 d hmax
                exact narrowLo_sem hB (by simp [modReasonLo])
                  (sf_cons _ (by sfs))
          · -- narrowHi
            have bi1 : SemFalsifiedBefore orig pre (posLe i (pl - 1)) :=
              (hB i).2 pl hpl
            have bi2 : SemFalsifiedBefore orig pre (negLe i ph) :=
              (hB i).1 ph hph
            cases o₂ with
            | lit d' =>
                exact narrowHi_sem hB (by simp [modReasonHi])
                  (sf_cons _ (by sfs))
            | slot j =>
                have hmin : domMinI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).1
                have hmax : domMaxI (st.domains.getD j Dom.empty) = some d :=
                  (divPin_slot hpin).2
                have bj1 : SemFalsifiedBefore orig pre (posLe j (d - 1)) :=
                  (hB j).2 d hmin
                have bj2 : SemFalsifiedBefore orig pre (negLe j d) :=
                  (hB j).1 d hmax
                exact narrowHi_sem hB (by simp [modReasonHi])
                  (sf_cons _ (by sfs))
        · trivial
      · trivial
  · trivial

/-- PLAN L2: `propLinNe`'s result contract. The conflict clause and the
    reason's causes are the fix literals `x_s ≠ v_s` of the pinned operands,
    each falsified by `FixExpl`. -/
theorem propLinNe_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int}
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propLinNe st coeffs is b) := by
  have hcauses : ∀ q ∈ linNeCauses st.domains (coeffs.zip is),
      SemFalsifiedBefore orig pre q := by
    intro q hq
    obtain ⟨c, s, v, -, hv, rfl⟩ := linNeCauses_mem.mp hq
    exact hX s v (eq_of_pinInt hv)
  cases hres : propLinNe st coeffs is b with
  | stable => trivial
  | implied l rs =>
      obtain ⟨-, c, m, -, -, -, -, hl, hrs⟩ := propLinNe_implied_inv hres
      subst hrs
      subst hl
      refine reasonOK_of_fix (by simp [posNe, Literal.norm]) (by simp) ?_
      intro q hq hne
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd rfl hne
      · exact hcauses q hq
  | conflict cc =>
      obtain ⟨-, -, -, hcl⟩ := propLinNe_conflict_inv hres
      subst hcl
      exact hcauses

/-- PLAN L4: the `leReifSlot` delegation's result contract: the pin escape is
    semantically falsified by the pinned absent value. -/
theorem propLeReifSlot_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {i j r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains) :
    ResSem orig pre (propLeReifSlot st i j r) := by
  rcases propLeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resSem_augment (propLe_sem hB i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h1)
  · rw [he]
    exact resSem_augment (propLt_sem hB j i) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h2)
  · rw [he]; trivial

/-- PLAN G1: the strengthened `leReifSlot` run's result contract: the pinned
    delegations as in `propLeReifSlot_sem`; the unpinned bounds arm's cause
    literals are the state bound facts (`BoundsExpl`), and its pivot is the
    Boolean pin escape. -/
theorem propLeReifSlotB_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {i j r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains) :
    ResSem orig pre (propLeReifSlotB st i j r) := by
  rcases propLeReifSlotB_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩
  · rw [he]
    exact resSem_augment (propLe_sem hB i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h1)
  · rw [he]
    exact resSem_augment (propLt_sem hB j i) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h2)
  · rw [he]
    rcases propLeReifB_emission_inv (res := propLeReifB st i j r) rfl with
      hstable | ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
        hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩ |
      ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
        hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩
    · rw [hstable]; trivial
    · rw [hres]
      refine reasonOK_of_bool List.mem_cons_self ?_
      intro q hq hne
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd rfl hne
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact (hB i).1 mx_i hmx_i
        · rw [List.mem_singleton.mp hq]
          exact (hB j).2 mn_j hmn_j
    · rw [hres]
      refine reasonOK_of_bool List.mem_cons_self ?_
      intro q hq hne
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd rfl hne
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact (hB i).2 mn_i hmn_i
        · rw [List.mem_singleton.mp hq]
          exact (hB j).1 mx_j hmx_j

/-- PLAN G1-B: the `bool2intSlot` channel propagator's result contract.
    Each pinned removal's cause is the negated Boolean pin (`AbsentExpl`);
    the unpinned unit removals have no causes; the two bound conflicts use
    the domain extrema (`BoundsExpl`); the raw `[.int 0]`/`[.int 1]` pins
    use the fix literal (`FixExpl`). -/
theorem propBool2intSlot_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {i k : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propBool2intSlot st i k) := by
  rcases propBool2intSlot_cases st i k with hstable | ⟨hpt, w, hfb, he⟩ |
    ⟨hpf, w, hfb, he⟩ | ⟨hnb, he⟩ | ⟨hd0, he⟩ | ⟨hd1, he⟩ |
    ⟨w, hfb, he⟩ | ⟨mx, mn, hmx, hmn, hlt, he⟩ | ⟨mx, mn, hmx, hmn, hgt, he⟩
  · rw [hstable]; trivial
  · rw [he]
    refine reasonOK_of_fix (l := posNe k w) rfl List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton] at hq
      subst hq
      exact pins_of_absent hA hpt
  · rw [he]
    refine reasonOK_of_fix (l := posNe k w) rfl List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton] at hq
      subst hq
      exact pins_of_absent hA hpf
  · rw [he]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hA i true (Bool.or_eq_false_iff.mp hnb).1
    · rw [List.mem_singleton] at hq
      subst hq
      exact hA i false (Bool.or_eq_false_iff.mp hnb).2
  · rw [he]
    unfold implyBool
    by_cases hmem : valueMemB (.bool false) (slotEnum st.domains i) = true
    · rw [if_pos hmem]
      by_cases heq : valuesEqB (slotEnum st.domains i) [.bool false] = true
      · rw [if_pos heq]; trivial
      · rw [if_neg heq]
        refine reasonOK_of_fix (l := posBool i false) (by simp [posBool_norm])
          (by simp) ?_
        intro q hq hne
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd rfl hne
        · rw [List.mem_singleton] at hq
          subst hq
          exact hX k 0 hd0
    · rw [if_neg hmem]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hA i false (Bool.eq_false_iff.mpr hmem)
      · rw [List.mem_singleton] at hq
        subst hq
        exact hX k 0 hd0
  · rw [he]
    unfold implyBool
    by_cases hmem : valueMemB (.bool true) (slotEnum st.domains i) = true
    · rw [if_pos hmem]
      by_cases heq : valuesEqB (slotEnum st.domains i) [.bool true] = true
      · rw [if_pos heq]; trivial
      · rw [if_neg heq]
        refine reasonOK_of_fix (l := posBool i true) (by simp [posBool_norm])
          (by simp) ?_
        intro q hq hne
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd rfl hne
        · rw [List.mem_singleton] at hq
          subst hq
          exact hX k 1 hd1
    · rw [if_neg hmem]
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hA i true (Bool.eq_false_iff.mpr hmem)
      · rw [List.mem_singleton] at hq
        subst hq
        exact hX k 1 hd1
  · rw [he]
    refine reasonOK_of_fix (l := posNe k w) rfl (List.mem_singleton_self _) ?_
    intro q hq hne
    rw [List.mem_singleton] at hq
    subst hq
    exact absurd rfl hne
  · rw [he]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact sf_negLe_mono ((hB k).1 mx hmx) (by omega)
  · rw [he]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact sf_posLe_mono ((hB k).2 mn hmn) (by omega)

/-! ### PLAN G1c: order-to-removal semantic falsity (family-local copies)

The monotonicity bridges `sf_posLe_to_negNe`/`sf_negLe_to_negNe` and their
`impliesP`/root-falsity kernels live downstream in
`LcgRunInvariantReasons`; the element propagator's no-support cause needs
them HERE, so the three kernels are duplicated under `aie_` names. -/

/-- Root falsity of a literal = it holds at no original value of its slot. -/
theorem aie_litFalseAtRoot_iff (orig : List Domain) (q : Literal) :
    litFalseAtRoot orig q = true ↔ ∀ v ∈ Dom.enum (orig.getD q.atom.slot Dom.empty),
      q.valueHolds v = false := by
  unfold litFalseAtRoot
  rw [List.all_eq_true]
  apply forall_congr'; intro v
  apply imp_congr_right; intro _
  obtain ⟨atom, pos⟩ := q
  cases atom <;> cases pos <;> cases v <;>
    simp [Atom.evalAtValue, Literal.valueHolds, Value.intView] <;>
    (try split) <;> simp_all

/-- A negative order literal implies the positive removals below its bound. -/
theorem aie_impliesP_negLe_posNe {orig : List Domain} {t : Literal} {s : Nat}
    {m k : Int} (h : impliesP orig t (negLe s m) = true) (hk : k ≤ m) :
    impliesP orig t (posNe s k) = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
      simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB,
      posNe, negLe, posLe, Literal.negate] at h ⊢ <;>
      simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩;
         rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, posNe, negLe] at this ⊢ <;> omega

/-- A positive order literal implies the positive removals above its bound. -/
theorem aie_impliesP_posLe_posNe {orig : List Domain} {t : Literal} {s : Nat}
    {m k : Int} (h : impliesP orig t (posLe s m) = true) (hk : m < k) :
    impliesP orig t (posNe s k) = true := by
  rcases impliesP_cases h with h | h
  · refine impliesP_of_base ?_
    obtain ⟨a, p⟩ := t
    unfold impliesBase at h ⊢
    generalize slotBoolB orig _ = B at h ⊢
    rcases a with ⟨s0, b⟩ | ⟨s0, u⟩ | ⟨s0, u⟩ <;> (try cases b) <;> cases p <;>
      simp [impliesLit, Literal.intForm, Literal.boolKind, litEqB,
      posNe, negLe, posLe, Literal.negate] at h ⊢ <;>
      simp only [Atom.slot] at h ⊢ <;> try omega
    all_goals first
      | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
      | (obtain ⟨hB, h⟩ := h; refine ⟨hB, ?_⟩;
         rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
  · refine impliesP_of_table ?_
    obtain ⟨hs, hb, ht⟩ := boolSlotImp_elim h
    refine boolSlotImp_intro hs hb fun c hh hc => ?_
    have := ht c hh hc
    cases c <;> simp [Literal.truthAtBool, posNe, posLe] at this ⊢ <;> omega

/-- A falsified upper bound `s ≤ m` excludes every value above `m`. -/
theorem aie_sf_posLe_to_negNe {orig : List Domain} {tr : List TrailEntry}
    {s : Nat} {m k : Int}
    (h : SemFalsifiedBefore orig tr (posLe s m)) (hk : k ≤ m) :
    SemFalsifiedBefore orig tr (negNe s k) := by
  rcases h with h | ⟨e, he, hi⟩
  · refine Or.inl ((aie_litFalseAtRoot_iff orig _).mpr fun v hv => ?_)
    have h' := (aie_litFalseAtRoot_iff orig _).mp h v hv
    cases hiv : v.intView with
    | none => simp [Literal.valueHolds, negNe, hiv]
    | some a =>
        simp [Literal.valueHolds, posLe, negNe, hiv] at h' ⊢
        omega
  · exact Or.inr ⟨e, he, aie_impliesP_negLe_posNe
      (m := m) (by simpa [posLe, negLe, Literal.negate, Literal.norm] using hi) hk⟩

/-- A falsified lower bound `s > m` excludes every value below `m`. -/
theorem aie_sf_negLe_to_negNe {orig : List Domain} {tr : List TrailEntry}
    {s : Nat} {m k : Int}
    (h : SemFalsifiedBefore orig tr (negLe s m)) (hk : m < k) :
    SemFalsifiedBefore orig tr (negNe s k) := by
  rcases h with h | ⟨e, he, hi⟩
  · refine Or.inl ((aie_litFalseAtRoot_iff orig _).mpr fun v hv => ?_)
    have h' := (aie_litFalseAtRoot_iff orig _).mp h v hv
    cases hiv : v.intView with
    | none => simp [Literal.valueHolds, negNe, hiv]
    | some a =>
        simp [Literal.valueHolds, negLe, negNe, hiv] at h' ⊢
        omega
  · exact Or.inr ⟨e, he, aie_impliesP_posLe_posNe
      (m := m) (by simpa [posLe, negLe, Literal.negate, Literal.norm] using hi) hk⟩

/-- PLAN G1c: a value missing from an integer-only, nonempty domain is
    semantically excluded: the extrema explain values outside the hull,
    `HolesExpl` explains an interior value. -/
theorem aie_negNe_falsified {orig : List Domain} {pre : List TrailEntry}
    {st : State} {k : Nat} {v : Int}
    (hB : BoundsExpl orig pre st.domains)
    (hH : HolesExpl orig pre st.domains)
    (hint : ∀ u ∈ Dom.enum (st.domains.getD k Dom.empty), ∃ w : Int, u = .int w)
    (hne : Dom.enum (st.domains.getD k Dom.empty) ≠ [])
    (hvm : valueMemB (.int v) (Dom.enum (st.domains.getD k Dom.empty)) = false) :
    SemFalsifiedBefore orig pre (negNe k v) := by
  have hnov : ∀ u ∈ st.domains.getD k Dom.empty, Value.intView u ≠ some v := by
    intro u hu hiv
    obtain ⟨w, hw⟩ := hint u ((DomainLike.mem_iff _ _).mp hu)
    rw [hw] at hiv
    have hwv : w = v := Option.some.inj (by simpa [Value.intView] using hiv)
    have hmem : (.int v : Value) ∈ Dom.enum (st.domains.getD k Dom.empty) := by
      rw [← hwv, ← hw]
      exact (DomainLike.mem_iff _ _).mp hu
    have htrue : valueMemB (.int v) (Dom.enum (st.domains.getD k Dom.empty)) = true :=
      valueMemB_iff.mpr hmem
    rw [hvm] at htrue
    exact absurd htrue (by simp)
  have hnei : domInts (Dom.enum (st.domains.getD k Dom.empty)) ≠ [] := by
    intro h0
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨w, hw⟩ := hint u hu
    have hmem : w ∈ domInts (Dom.enum (st.domains.getD k Dom.empty)) := by
      unfold domInts
      exact List.mem_filterMap.mpr ⟨u, hu, by rw [hw]⟩
    rw [h0] at hmem
    exact absurd hmem (by simp)
  by_cases hbelow : ∃ u ∈ st.domains.getD k Dom.empty, ∃ a : Int,
      Value.intView u = some a ∧ a < v
  · by_cases habove : ∃ u ∈ st.domains.getD k Dom.empty, ∃ a : Int,
        Value.intView u = some a ∧ v < a
    · refine hH k v ?_ ?_ ?_
      · obtain ⟨u, hu, a, hiv, hlt⟩ := hbelow
        exact ⟨u, hu, a, hiv, by omega⟩
      · obtain ⟨u, hu, a, hiv, hgt⟩ := habove
        exact ⟨u, hu, a, hiv, by omega⟩
      · exact hnov
    · cases hmx : domMaxI (st.domains.getD k Dom.empty) with
      | none =>
          have hmx' : domMaxI (Dom.enum (st.domains.getD k Dom.empty)) = none := by
            simpa only [domMaxI_enum] using hmx
          exact absurd hmx' (domMaxI_ne_none hnei)
      | some mx =>
          obtain ⟨u, hu, hiv⟩ := a2_domMaxI_attained hmx
          have hle : mx ≤ v := by
            by_cases hgt : v < mx
            · exact absurd ⟨u, hu, mx, hiv, hgt⟩ habove
            · omega
          have hmxv : mx ≠ v := by
            intro heq
            exact hnov u hu (by rw [heq] at hiv; exact hiv)
          exact aie_sf_negLe_to_negNe ((hB k).1 mx hmx) (by omega)
  · cases hmn : domMinI (st.domains.getD k Dom.empty) with
    | none =>
        have hmn' : domMinI (Dom.enum (st.domains.getD k Dom.empty)) = none := by
          simpa only [domMinI_enum] using hmn
        exact absurd hmn' (domMinI_ne_none hnei)
    | some mn =>
        obtain ⟨u, hu, hiv⟩ := a2_domMinI_attained hmn
        have hge : v ≤ mn := by
          by_cases hlt : mn < v
          · exact absurd ⟨u, hu, mn, hiv, hlt⟩ hbelow
          · omega
        have hmnv : mn ≠ v := by
          intro heq
          exact hnov u hu (by rw [heq] at hiv; exact hiv)
        exact aie_sf_posLe_to_negNe ((hB k).2 mn hmn) (by omega)


/-- PLAN G1c: the constant-table element propagator's result contract.
    The pinned-index conflict and removal causes are raw int singletons
    (`FixExpl`); the pinned-target removal's cause is the pinned target
    (`FixExpl`); the no-support removal's cause `k = v` is explained by
    the bounds (`BoundsExpl`) or an interior hole (`HolesExpl`). -/
theorem propArrayIntElement_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {xs : List Int} {i k : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hH : HolesExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propArrayIntElement st xs i k) := by
  rcases propArrayIntElement_cases st xs i k with hstable | ⟨idx, hidx, hnone, he⟩ |
    ⟨idx, v, w, hidx, hent, hfb, he⟩ | ⟨v, idx, hk, hfb, he⟩ |
    ⟨idx, hfb, he⟩ | ⟨idx, v, hg, hfb, hent, he⟩
  · rw [hstable]; trivial
  · rw [he]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hX i idx hidx
  · rw [he]
    refine reasonOK_of_fix (l := posNe k w) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton] at hq
      subst hq
      exact hX i idx hidx
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton] at hq
      subst hq
      exact hX k v hk
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · cases hq
  · rw [he]
    obtain ⟨hlen, hne, hint⟩ := domsIntOnlyB_eq hg k (by simp)
    obtain ⟨v', hent', hvm⟩ := aie_firstBadView_supportB_some hfb
    rw [hent] at hent'
    have hvv : v = v' := Value.int.inj (Option.some.inj hent')
    have hvm' : valueMemB (.int v) (Dom.enum (st.domains.getD k Dom.empty)) = false := by
      rw [hvv]
      exact hvm
    have hne' : Dom.enum (st.domains.getD k Dom.empty) ≠ [] := by
      intro h0
      rw [Dom.length_eq_enum, h0] at hne
      simp at hne
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne2
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne2
    · rw [List.mem_singleton] at hq
      subst hq
      exact aie_negNe_falsified hB hH hint hne' hvm'

/-- PLAN §3.3 item 1: the variable-table element propagator's result
    contract. All non-pivot causes are state-shape facts: raw singleton
    pins (`FixExpl`), domain extrema (`BoundsExpl`) and missing values
    (`HolesExpl`/`BoundsExpl` through `aie_negNe_falsified`). -/
theorem propArrayVarIntElement_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {is : List Nat} {i k : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hH : HolesExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propArrayVarIntElement st is i k) := by
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
  · rw [he]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hX i idx hidx
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResK])
    obtain ⟨-, -, -, hbad⟩ := firstBadView_some hfb
    obtain ⟨-, hneJ, hintJ⟩ := domsIntOnlyB_eq hg j
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (avieEntry_mem hent)))
    have hneJ' : Dom.enum (st.domains.getD j Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneJ; simp at hneJ
    refine reasonOK_of_fix (l := posNe k w) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX i idx hidx
      · rw [List.mem_singleton] at hq
        subst hq
        exact aie_negNe_falsified hB hH hintJ hneJ' hbad
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResJ])
    obtain ⟨-, -, -, hbad⟩ := firstBadView_some hfb
    obtain ⟨-, hneK, hintK⟩ := domsIntOnlyB_eq hg k (by simp)
    have hneK' : Dom.enum (st.domains.getD k Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneK; simp at hneK
    refine reasonOK_of_fix (l := posNe j w) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX i idx hidx
      · rw [List.mem_singleton] at hq
        subst hq
        exact aie_negNe_falsified hB hH hintK hneK' hbad
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · cases hq
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResPinVal])
    obtain ⟨-, hneJ, hintJ⟩ := domsIntOnlyB_eq hg j
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (avieEntry_mem hent)))
    have hneJ' : Dom.enum (st.domains.getD j Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneJ; simp at hneJ
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX k v hk
      · rw [List.mem_singleton] at hq
        subst hq
        exact aie_negNe_falsified hB hH hintJ hneJ' hvm
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · cases hq
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResBelow])
    obtain ⟨-, hneK, hintK⟩ := domsIntOnlyB_eq hg k (by simp)
    have hneK' : Dom.enum (st.domains.getD k Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneK; simp at hneK
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact (hB j).1 mx hmx
      · rw [List.mem_singleton] at hq
        subst hq
        exact (hB k).2 mn hmn
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResAbove])
    obtain ⟨-, hneJ, hintJ⟩ := domsIntOnlyB_eq hg j
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (avieEntry_mem hent)))
    have hneJ' : Dom.enum (st.domains.getD j Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneJ; simp at hneJ
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact (hB k).1 mx hmx
      · rw [List.mem_singleton] at hq
        subst hq
        exact (hB j).2 mn hmn
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResSingle])
    obtain ⟨-, hneK, hintK⟩ := domsIntOnlyB_eq hg k (by simp)
    have hneK' : Dom.enum (st.domains.getD k Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneK; simp at hneK
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX j w hdj
      · rw [List.mem_singleton] at hq
        subst hq
        exact aie_negNe_falsified hB hH hintK hneK' hvm
  · rw [he]
    have hg : domsIntOnlyB st.domains (i :: k :: is) = true :=
      avie_guard_of_res he (by simp [avieResNoSupp])
    obtain ⟨-, hneK, hintK⟩ := domsIntOnlyB_eq hg k (by simp)
    have hneK' : Dom.enum (st.domains.getD k Dom.empty) ≠ [] := by
      intro h0; rw [Dom.length_eq_enum, h0] at hneK; simp at hneK
    refine reasonOK_of_fix (l := posNe k w) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      obtain ⟨-, hneJ, hintJ⟩ := domsIntOnlyB_eq hg j
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
      have hneJ' : Dom.enum (st.domains.getD j Dom.empty) ≠ [] := by
        intro h0; rw [Dom.length_eq_enum, h0] at hneJ; simp at hneJ
      exact aie_negNe_falsified hB hH hintJ hneJ'
        (avieTableMemB_false (avie_firstBadView_false hfbw) hj)

/-- PLAN §3.3 item 2: the variable-table Boolean element propagator's
    result contract. All non-pivot causes are state-shape facts: the raw
    int index pin (`FixExpl`) and Boolean absences (`AbsentExpl`). -/
theorem propArrayVarBoolElement_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {is : List Nat} {i k : Nat}
    (hA : AbsentExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propArrayVarBoolElement st is i k) := by
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
  · rw [he]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hX i idx hidx
  · rw [he]
    obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfb
    refine implyBool_sem hA (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX i idx hidx
      · rw [List.mem_singleton] at hq
        subst hq
        exact hA j b hbad
  · rw [he]
    obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfb
    refine implyBool_sem hA (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hX i idx hidx
      · rw [List.mem_singleton] at hq
        subst hq
        exact hA k b hbad
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rw [List.mem_singleton] at hq
    subst hq
    exact absurd rfl hne
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hA k (!v) (by rw [hk]; cases v <;> rfl)
      · rw [List.mem_singleton] at hq
        subst hq
        exact hA j v hvm
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rw [List.mem_singleton] at hq
    subst hq
    exact absurd rfl hne
  · rw [he]
    refine reasonOK_of_fix (l := posNe i idx) (by simp [posNe_norm])
      (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hA j (!b) (by rw [hdj]; cases b <;> rfl)
      · rw [List.mem_singleton] at hq
        subst hq
        exact hA k b hvm
  · rw [he]
    obtain ⟨-, -, -, hbad⟩ := avbeFirstBad_some hfbw
    refine implyBool_sem hA (by simp) ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact hA j b (avbeTableMemB_false hbad hj)

/-- PLAN G1e: the array-Boolean conjunction propagator's result contract.
    Every cause is a Boolean absence fact (`AbsentExpl`): the input pins
    falsify the `posBool · false` causes and the target pins falsify the
    `posBool · true` causes; in the conflict rounds the emitter's own
    absence check falsifies the pivot. -/
theorem propArrayBoolAnd_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {is : List Nat} {k : Nat}
    (hA : AbsentExpl orig pre st.domains) :
    ResSem orig pre (propArrayBoolAnd st is k) := by
  rcases propArrayBoolAnd_cases st is k with
    hstable | ⟨hall, he⟩ | ⟨i, hfb, he⟩ | ⟨hk, i, hfb, he⟩ |
    ⟨hkf, i, his, hb, he⟩
  · rw [hstable]; trivial
  · rw [he]
    refine implyBool_sem hA (s := k) (b := true) List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_append.mp hq with hq | hq
    · rw [List.mem_singleton.mp hq] at hne
      exact absurd rfl hne
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact hA j false (by
        rw [domBoolPin_eq (List.all_eq_true.mp hall j hj)]
        simp [valueMemB, Value.eqB])
  · rw [he]
    refine implyBool_sem hA (s := k) (b := false) List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hq]
      exact hA i true (by
        rw [domBoolPin_eq (aba_find?_some_eq (fun j => domBoolPin st.domains j false) hfb)]
        simp [valueMemB, Value.eqB])
  · rw [he]
    refine implyBool_sem hA (s := i) (b := true) List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hq]
      exact hA k false (by
        rw [domBoolPin_eq hk]
        simp [valueMemB, Value.eqB])
  · rw [he]
    refine implyBool_sem hA (s := i) (b := false) List.mem_cons_self ?_
    intro q hq hne
    rcases List.mem_cons.mp hq with rfl | hq
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hq]
      exact hA k true (by
        rw [domBoolPin_eq hkf]
        simp [valueMemB, Value.eqB])

/-- PLAN L4: the `eqReifSlot` delegation's result contract. -/
theorem propEqReifSlot_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {i j r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (hF : FixExpl orig pre st.domains) :
    ResSem orig pre (propEqReifSlot st i j r) := by
  rcases propEqReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resSem_augment (propEq_sem hB i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h1)
  · rw [he]
    exact resSem_augment (propNe_sem hB hA hF i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h2)
  · rw [he]; trivial

/-- PLAN L4: the `neReifSlot` delegation's result contract. -/
theorem propNeReifSlot_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {i j r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (hF : FixExpl orig pre st.domains) :
    ResSem orig pre (propNeReifSlot st i j r) := by
  rcases propNeReifSlot_cases st i j r with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | he
  · rw [he]
    exact resSem_augment (propNe_sem hB hA hF i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h1)
  · rw [he]
    exact resSem_augment (propEq_sem hB i j) (by
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact pins_of_absent hA h2)
  · rw [he]; trivial

/-- PLAN L5: `propLinEqReif`'s result contract: the pin escape is
    semantically falsified by the pinned absent value, and the delegated
    `propLinEq2`/`propLinNe` kernels carry the Bounds/Absent/Fix
    explanations. -/
theorem propLinEqReif_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propLinEqReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinEqReif_run_true hlenB h1]
      exact resSem_augment (propLinEq2_sem hB coeffs is b)
        (linLeReifEscTrue_sf hA h1)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinEqReif_run_false hlenB h1 h2]
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        exact resSem_conflictsOnly (resSem_augment
          (propLinNe_sem hX)
          (linLeReifEscFalse_sf hA hpf hg))
      · rw [propLinEqReif_run_stable hlenB h1 h2]
        trivial
  · rw [propLinEqReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

/-- PLAN L5: `propLinNeReif`'s result contract (the `linEqReif` twin, with
    the delegated kernels swapped). -/
theorem propLinNeReif_sem {orig : List Domain} {pre : List TrailEntry}
    {st : State} {coeffs : List Int} {is : List Nat} {b : Int} {r : Nat}
    (hB : BoundsExpl orig pre st.domains)
    (hA : AbsentExpl orig pre st.domains)
    (hX : FixExpl orig pre st.domains) :
    ResSem orig pre (propLinNeReif st coeffs is b r) := by
  by_cases hlenB : (coeffs.length == is.length) = true
  · by_cases h1 : domBoolPin st.domains r true = true
    · rw [propLinNeReif_run_true hlenB h1]
      exact resSem_augment (propLinNe_sem hX)
        (linLeReifEscTrue_sf hA h1)
    · by_cases h2 : (domBoolPin st.domains r false
          && domsIntOnlyB st.domains is) = true
      · rw [propLinNeReif_run_false hlenB h1 h2]
        have h2' := h2
        rw [Bool.and_eq_true] at h2'
        obtain ⟨hpf, hg⟩ := h2'
        exact resSem_conflictsOnly (resSem_augment
          (propLinEq2_sem hB coeffs is b)
          (linLeReifEscFalse_sf hA hpf hg))
      · rw [propLinNeReif_run_stable hlenB h1 h2]
        trivial
  · rw [propLinNeReif_run_arity (Bool.eq_false_iff.mpr hlenB)]
    trivial

-- PLAN L4 note: the dispatch chain gained two more arms (the reified
-- equality/disequality delegations), which lifts the unification cost of the
-- `first` chain; the elaboration budget is raised locally.
set_option maxHeartbeats 1000000 in
theorem propSem_of_family {orig : List Domain} {bs : BranchState leaf}
    (hF : FrameExplainedFull orig bs) (dc : DomConstraint) (hfam : lcgFamB dc = true)
    {p : Propagator} (hp : propagatorOfProved dc = some p) :
    PropSemContract orig p bs := by
  have hB : BoundsExpl orig bs.trail (frameState bs.frame).domains := hF.base.bounds
  have hA : AbsentExpl orig bs.trail (frameState bs.frame).domains := hF.base.absent
  have hX : FixExpl orig bs.trail (frameState bs.frame).domains := hF.base.fix
  have hH : HolesExpl orig bs.trail (frameState bs.frame).domains := hF.holes
  cases dc <;> first
    | (simp only [propagatorOfProved] at hp
       contradiction)
    | (simp only [propagatorOfProved, Option.some.injEq] at hp
       subst hp
       exact propSem_iff.mpr (propCheck_sem_aux hF _))
    | (simp only [propagatorOfProved, Option.some.injEq] at hp
       subst hp
       refine propSem_iff.mpr ?_
       first
         | exact propLe_sem hB _ _
         | exact propLt_sem hB _ _
         | exact propEq_sem hB _ _
         | exact propPlus_sem hB _ _ _
         | exact propLinLe2_sem hB _ _ _
         | exact propLinEq2_sem hB _ _ _
         | exact propLeConstHi_sem hB _ _
         | exact propLeConstLo_sem hB _ _
         | exact propLtConstHi_sem hB _ _
         | exact propLtConstLo_sem hB _ _
         | exact propConstEq_sem hB hA _ _
         | exact propBoolNot_sem hA _ _
         | exact propBoolAnd_sem hA _ _ _
         | exact propBoolOr_sem hA _ _ _
         | exact propAllDiffLCG_sem hB hH hA _
         | exact propLinLeReif_sem hB hA
         | exact propLinEqReif_sem hB hA hX
         | exact propLinNeReif_sem hB hA hX
         | exact propLeReifSlotB_sem hB hA
         | exact propEqReifSlot_sem hB hA hX
         | exact propNeReifSlot_sem hB hA hX
         | exact propLinNe_sem hX
         | exact propMin_sem hB _ _ _
         | exact propMax_sem hB _ _ _
         | exact propTimes_sem hB _ _ _
         | exact propAbs_sem hB _ _
         | exact propDiv_sem hB hX _ _ _
         | exact propMod_sem hB hX _ _ _
         | exact propMinGen_sem hB _ _
         | exact propMaxGen_sem hB _ _
         | exact propNe_sem hB hA hX _ _
         | exact propBool2intSlot_sem hB hA hX
         | exact propArrayIntElement_sem hB hH hX
         | exact propArrayVarIntElement_sem hB hH hX
         | exact propArrayVarBoolElement_sem hA hX
         | exact propArrayBoolAnd_sem hA)
    | (rename_i o0 o1 r
       cases o0 <;> cases o1 <;> cases r <;>
         (simp only [propagatorOfProved, Option.some.injEq] at hp
          subst hp
          first
            | (refine propSem_iff.mpr ?_
               rw [Propagator.run_mk]
               exact propCheck_sem_aux hF _)
            | (refine propSem_iff.mpr ?_
               first
                 | exact propMin_sem hB _ _ _
                 | exact propMax_sem hB _ _ _)))

/-- **`RunSemContract` for the gate "all constraints in proved families"**,
given the frame-explanation invariant along the supported run. -/
theorem runSemContract_of_families {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {props : List Propagator}
    (hprops : props = clampProps orig (dcs.filterMap propagatorOfProved))
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hframe : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      FrameExplainedFull orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      TrailSnapFixed orig cfg.branch.trail) :
    RunSemContract orig original props leaf := by
  intro cfg hreach p hp
  have hreach' := hreach
  subst hprops
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  obtain ⟨dc, hdc, hprop⟩ := propagatorsOfProved_mem hp0
  exact propSem_clamp (htrail hreach') (propSem_of_family (hframe hreach') dc (hfam dc hdc) hprop)

/-- The `lcgKit` gate is discharged by the family gate and the invariant. -/
theorem lcgKit_gate_of_families {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {props : List Propagator}
    (hprops : props = clampProps orig (dcs.filterMap propagatorOfProved))
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hframe : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      FrameExplainedFull orig cfg.branch)
    (htrail : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      TrailSnapFixed orig cfg.branch.trail) :
    (lcgKit lcgFamB).Gate leaf orig original props :=
  ⟨⟨dcs, hprops, hfam⟩, runSemContract_of_families hprops hfam hframe htrail⟩


/-- The registered sparse-frame `boolNotSlot 0 1` witness
(`boolNot_sparse_emit`: reason `[0 = false, 1 = false]` over the domains
`[[F,T],[T]]`) satisfies the semantic contract once the pin `1 = true` is on
the trail. -/
theorem boolNot_sparse_semOK (orig : List Domain) :
    SemReasonOK orig [⟨posBool 1 true, 0, none⟩] (posBool 0 false)
      [posBool 0 false, posBool 1 false] :=
  reasonOK_of_bool (by simp)
    (sf_cons _ (fun q hq => by
      have : q = posBool 1 false := by simpa using hq
      subst this
      exact Or.inr ⟨⟨posBool 1 true, 0, none⟩, by simp, by simp [impliesP, impliesBase, litEqB, posBool, Literal.negate, Literal.norm]⟩))

end LeanFzn.Solver.UIP.LcgFamilies
