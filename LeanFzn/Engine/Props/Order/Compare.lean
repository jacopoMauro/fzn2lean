/-
Purpose: Order propagators: compare definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Order.Bounds
DAG: LeanFzn.Engine.Props.Order.Bounds -> LeanFzn.Engine.Props.Order.Compare.
-/
import LeanFzn.Engine.Props.Order.Bounds

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Binary comparisons -/

/-- The semantic content of `leSlot i j`: every accepted assignment reads
integers `x_i ≤ x_j`. -/
def LeSlotSem (p : CompiledProblem DomConstraint) (i j : Nat) : Prop :=
  ∀ a, a ∈ allAssigns p.domains → accepts p a = true →
    ∃ xi xj, slotInt a i = some xi ∧ slotInt a j = some xj ∧ xi ≤ xj

/-- The semantic content of `ltSlot i j`: every accepted assignment reads
integers `x_i < x_j`. -/
def LtSlotSem (p : CompiledProblem DomConstraint) (i j : Nat) : Prop :=
  ∀ a, a ∈ allAssigns p.domains → accepts p a = true →
    ∃ xi xj, slotInt a i = some xi ∧ slotInt a j = some xj ∧ xi < xj

theorem leSlot_sem {p : CompiledProblem DomConstraint} {i j : Nat}
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) :
    LeSlotSem p i j := by
  intro a _ha hacc
  have hdc : (DomConstraint.leSlot i j).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, hxi, hxj, hle⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hle⟩

theorem ltSlot_sem {p : CompiledProblem DomConstraint} {i j : Nat}
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) :
    LtSlotSem p i j := by
  intro a _ha hacc
  have hdc : (DomConstraint.ltSlot i j).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, hxi, hxj, hlt⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hlt⟩

theorem le_iUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {hij : Int} (hsem : LeSlotSem p i j) :
    Entailed p [posLe i hij, negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a _ha hacc
  by_cases h : xi ≤ hij
  · exact ⟨posLe i hij, by simp, (eval_posLe_iff a i hij).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

theorem le_jLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi : Int} (hsem : LeSlotSem p i j) :
    Entailed p [negLe j (loi - 1), posLe i (loi - 1)] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a _ha hacc
  by_cases h : loi - 1 < xj
  · exact ⟨negLe j (loi - 1), by simp,
      (eval_negLe_iff a j (loi - 1)).mpr ⟨xj, hxj, h⟩⟩
  · have hx : xi ≤ loi - 1 := by omega
    exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, hx⟩⟩

theorem le_conflict_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi hij : Int} (hsem : LeSlotSem p i j) (hconf : hij < loi) :
    Entailed p [posLe i (loi - 1), negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a _ha hacc
  by_cases h : xi ≤ loi - 1
  · exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

/-- `x_i ≤ x_j` interval propagator.  Conflicts when `i` lies entirely
above `j`; otherwise prunes `i`'s upper bound to `j`'s upper bound (first
priority) or `j`'s lower bound to `i`'s lower bound.  One bound is emitted
per run; repeated runs reach the interval fixpoint. -/
def lePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat) (hmem : DomConstraint.leSlot i j ∈ p.constraints) : PropV2 p T :=
  let hsem := leSlot_sem hmem
  { vars := (dcSlotsFull (DomConstraint.leSlot i j)).toArray
    events := #[(i, .bounds), (j, .bounds), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      match domBounds di, domBounds dj with
      | some (loi, hii), some (loj, hij) =>
          if hlt : hij < loi then
            .conflict (EClause.ofLiterals p T
              [posLe i (loi - 1), negLe j hij]
              (le_conflict_reason_entailed hsem hlt))
          else if _hiu : hii > hij then
            .prune #[(pLit (posLe i hij), EClause.ofLiterals p T
              [posLe i hij, negLe j hij]
              (le_iUpper_reason_entailed hsem))]
          else if _hjl : loj < loi then
            .prune #[(pLit (negLe j (loi - 1)), EClause.ofLiterals p T
              [negLe j (loi - 1), posLe i (loi - 1)]
              (le_jLower_reason_entailed hsem))]
          else .fix
      | _, _ => .fix }

theorem lePropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (lePropWith p T i j hmem).run view = .conflict ec) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      hij < loi ∧
      T.decodeClause ec.lits = [posLe i (loi - 1), negLe j hij] ∧
      Entailed p [posLe i (loi - 1), negLe j hij] := by
  unfold lePropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hlt
      injection h with hec
      subst hec
      refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hlt, ?_,
        le_conflict_reason_entailed (leSlot_sem hmem) hlt⟩
      change T.decodeClause
        ([posLe i (loi - 1), negLe j hij].toArray.map pLit) =
        [posLe i (loi - 1), negLe j hij]
      exact LitTable.decodeClause_map_pLit T _
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
  · cases h

theorem lePropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (lePropWith p T i j hmem).run view = .prune ps) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ hij < loi ∧
      ((hii > hij ∧
          (∀ q ∈ ps.toList, q.1.lit = posLe i hij ∧
            T.decodeClause q.2.lits = [posLe i hij, negLe j hij] ∧
            Entailed p [posLe i hij, negLe j hij])) ∨
        (¬ hii > hij ∧ loj < loi ∧
          (∀ q ∈ ps.toList, q.1.lit = negLe j (loi - 1) ∧
            T.decodeClause q.2.lits = [negLe j (loi - 1), posLe i (loi - 1)] ∧
            Entailed p [negLe j (loi - 1), posLe i (loi - 1)]))) := by
  unfold lePropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · cases h
    · rename_i hlt
      split at h
      · rename_i hiu
        cases h
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hlt,
          Or.inl ⟨hiu, ?_⟩⟩
        intro q hq
        have hq' : q = (pLit (posLe i hij), EClause.ofLiterals p T
            [posLe i hij, negLe j hij]
            (le_iUpper_reason_entailed (leSlot_sem hmem))) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, le_iUpper_reason_entailed (leSlot_sem hmem)⟩
        change T.decodeClause
          ([posLe i hij, negLe j hij].toArray.map pLit) =
          [posLe i hij, negLe j hij]
        exact LitTable.decodeClause_map_pLit T _
      · rename_i hiu
        split at h
        · rename_i hjl
          cases h
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hlt,
            Or.inr ⟨hiu, hjl, ?_⟩⟩
          intro q hq
          have hq' : q = (pLit (negLe j (loi - 1)), EClause.ofLiterals p T
              [negLe j (loi - 1), posLe i (loi - 1)]
              (le_jLower_reason_entailed (leSlot_sem hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_, le_jLower_reason_entailed (leSlot_sem hmem)⟩
          change T.decodeClause
            ([negLe j (loi - 1), posLe i (loi - 1)].toArray.map pLit) =
            [negLe j (loi - 1), posLe i (loi - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
  · cases h

theorem lePropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (lePropWith p T i j hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hdec, hent⟩ :=
    lePropWith_run_conflict p T i j hmem view h
  rwa [hdec]

theorem lePropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ec : EClause p T}
    (h : (lePropWith p T i j hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hlt, hdec, _hent⟩ :=
    lePropWith_run_conflict p T i j hmem view h
  rw [hdec]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have hle : loi ≤ hii :=
      DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
    exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
  · have hle : loj ≤ hij :=
      DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
    exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)

theorem lePropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (lePropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbranch⟩ :=
    lePropWith_run_prune p T i j hmem view h
  rcases hbranch with ⟨_, hfacts⟩ | ⟨_, _, hfacts⟩
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem lePropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (lePropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hlt, hbranch⟩ :=
    lePropWith_run_prune p T i j hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hiu, hfacts⟩ | ⟨hiu, hjl, hfacts⟩
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)

theorem lePropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (lePropWith p T i j hmem).run view = .fix := by
  unfold lePropWith
  dsimp only
  rw [hi]

theorem lePropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.leSlot i j ∈ p.constraints) (view : EngineView)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (lePropWith p T i j hmem).run view = .fix := by
  unfold lePropWith
  dsimp only
  rw [hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl
/-! ## Strict binary comparison -/

theorem lt_iUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {hij : Int} (hsem : LtSlotSem p i j) :
    Entailed p [posLe i (hij - 1), negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hlt⟩ := hsem a _ha hacc
  by_cases h : xi ≤ hij - 1
  · exact ⟨posLe i (hij - 1), by simp,
      (eval_posLe_iff a i (hij - 1)).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

theorem lt_jLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi : Int} (hsem : LtSlotSem p i j) :
    Entailed p [negLe j loi, posLe i (loi - 1)] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hlt⟩ := hsem a _ha hacc
  by_cases h : loi < xj
  · exact ⟨negLe j loi, by simp,
      (eval_negLe_iff a j loi).mpr ⟨xj, hxj, h⟩⟩
  · have hx : xi ≤ loi - 1 := by omega
    exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, hx⟩⟩

theorem lt_conflict_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi hij : Int} (hsem : LtSlotSem p i j) (hconf : hij ≤ loi) :
    Entailed p [posLe i (loi - 1), negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, hlt⟩ := hsem a _ha hacc
  by_cases h : xi ≤ loi - 1
  · exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

/-- `x_i < x_j` interval propagator.  Conflicts when `j`'s upper bound
does not exceed `i`'s lower bound; otherwise prunes `i`'s upper bound to
`j.hi - 1` (first priority) or `j`'s lower bound to `i.lo`.  One bound is
emitted per run; repeated runs reach the interval fixpoint. -/
def ltPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j : Nat) (hmem : DomConstraint.ltSlot i j ∈ p.constraints) : PropV2 p T :=
  let hsem := ltSlot_sem hmem
  { vars := (dcSlotsFull (DomConstraint.ltSlot i j)).toArray
    events := #[(i, .bounds), (j, .bounds), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      match domBounds di, domBounds dj with
      | some (loi, hii), some (loj, hij) =>
          if hconf : hij ≤ loi then
            .conflict (EClause.ofLiterals p T
              [posLe i (loi - 1), negLe j hij]
              (lt_conflict_reason_entailed hsem hconf))
          else if _hiu : hii ≥ hij then
            .prune #[(pLit (posLe i (hij - 1)), EClause.ofLiterals p T
              [posLe i (hij - 1), negLe j hij]
              (lt_iUpper_reason_entailed hsem))]
          else if _hjl : loj ≤ loi then
            .prune #[(pLit (negLe j loi), EClause.ofLiterals p T
              [negLe j loi, posLe i (loi - 1)]
              (lt_jLower_reason_entailed hsem))]
          else .fix
      | _, _ => .fix }

theorem ltPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltPropWith p T i j hmem).run view = .conflict ec) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      hij ≤ loi ∧
      T.decodeClause ec.lits = [posLe i (loi - 1), negLe j hij] ∧
      Entailed p [posLe i (loi - 1), negLe j hij] := by
  unfold ltPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hconf
      injection h with hec
      subst hec
      refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hconf, ?_,
        lt_conflict_reason_entailed (ltSlot_sem hmem) hconf⟩
      change T.decodeClause
        ([posLe i (loi - 1), negLe j hij].toArray.map pLit) =
        [posLe i (loi - 1), negLe j hij]
      exact LitTable.decodeClause_map_pLit T _
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
  · cases h

theorem ltPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltPropWith p T i j hmem).run view = .prune ps) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ hij ≤ loi ∧
      ((hii ≥ hij ∧
          (∀ q ∈ ps.toList, q.1.lit = posLe i (hij - 1) ∧
            T.decodeClause q.2.lits = [posLe i (hij - 1), negLe j hij] ∧
            Entailed p [posLe i (hij - 1), negLe j hij])) ∨
        (¬ hii ≥ hij ∧ loj ≤ loi ∧
          (∀ q ∈ ps.toList, q.1.lit = negLe j loi ∧
            T.decodeClause q.2.lits = [negLe j loi, posLe i (loi - 1)] ∧
            Entailed p [negLe j loi, posLe i (loi - 1)]))) := by
  unfold ltPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · cases h
    · rename_i hconf
      split at h
      · rename_i hiu
        cases h
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hconf,
          Or.inl ⟨hiu, ?_⟩⟩
        intro q hq
        have hq' : q = (pLit (posLe i (hij - 1)), EClause.ofLiterals p T
            [posLe i (hij - 1), negLe j hij]
            (lt_iUpper_reason_entailed (ltSlot_sem hmem))) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, lt_iUpper_reason_entailed (ltSlot_sem hmem)⟩
        change T.decodeClause
          ([posLe i (hij - 1), negLe j hij].toArray.map pLit) =
          [posLe i (hij - 1), negLe j hij]
        exact LitTable.decodeClause_map_pLit T _
      · rename_i hiu
        split at h
        · rename_i hjl
          cases h
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hconf,
            Or.inr ⟨hiu, hjl, ?_⟩⟩
          intro q hq
          have hq' : q = (pLit (negLe j loi), EClause.ofLiterals p T
              [negLe j loi, posLe i (loi - 1)]
              (lt_jLower_reason_entailed (ltSlot_sem hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_, lt_jLower_reason_entailed (ltSlot_sem hmem)⟩
          change T.decodeClause
            ([negLe j loi, posLe i (loi - 1)].toArray.map pLit) =
            [negLe j loi, posLe i (loi - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
  · cases h

theorem ltPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (ltPropWith p T i j hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hdec, hent⟩ :=
    ltPropWith_run_conflict p T i j hmem view h
  rwa [hdec]

theorem ltPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ec : EClause p T}
    (h : (ltPropWith p T i j hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hconf, hdec, _hent⟩ :=
    ltPropWith_run_conflict p T i j hmem view h
  rw [hdec]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have hle : loi ≤ hii :=
      DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
    exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
  · have hle : loj ≤ hij :=
      DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
    exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)

theorem ltPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (ltPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbranch⟩ :=
    ltPropWith_run_prune p T i j hmem view h
  rcases hbranch with ⟨_, hfacts⟩ | ⟨_, _, hfacts⟩
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem ltPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (ltPropWith p T i j hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hconf, hbranch⟩ :=
    ltPropWith_run_prune p T i j hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hiu, hfacts⟩ | ⟨hiu, hjl, hfacts⟩
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)

theorem ltPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (ltPropWith p T i j hmem).run view = .fix := by
  unfold ltPropWith
  dsimp only
  rw [hi]

theorem ltPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j : Nat)
    (hmem : DomConstraint.ltSlot i j ∈ p.constraints) (view : EngineView)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (ltPropWith p T i j hmem).run view = .fix := by
  unfold ltPropWith
  dsimp only
  rw [hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl

/-! ## Value equality -/

/-- Every member of a compact domain has an integer view (integers
themselves and Booleans as `0`/`1`). -/
theorem DomC.intView_isSome_of_mem {d : DomC} {w : Value}
    (hw : d.mem w = true) : ∃ x, Value.intView w = some x := by
  cases d <;> cases w <;> simp_all [DomC.mem, Value.intView]

/-- The semantic content of `eqSlot i j`: every accepted assignment reads
equal integer views in the two slots. -/
def EqSlotSem (p : CompiledProblem DomConstraint) (i j : Nat) : Prop :=
  ∀ a, a ∈ allAssigns p.domains → accepts p a = true →
    ∃ xi xj, slotInt a i = some xi ∧ slotInt a j = some xj ∧ xi = xj

/-- Accepted assignments of a value equality carry initial-domain members
in both slots. -/
theorem eqSlot_accepts_data (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) {b : Assignment}
    (hb : b ∈ allAssigns p.domains) (hacc : accepts p b = true) :
    ∃ wi wj, b[i]? = some wi ∧ b[j]? = some wj ∧ wi = wj ∧
      (init.getD i DomC.empty).mem wi = true ∧
      (init.getD j DomC.empty).mem wj = true := by
  have hfit := allAssigns_fits_dom p.domains b hb
  have hdc : (DomConstraint.eqSlot i j).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨wi, wj, hbi, hbj, hwij⟩ := (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hmi : (init.getD i DomC.empty).mem wi = true :=
    (DomC.mem_iff _ _ (hinit i (by simp)) wi).mpr (hfit.2 i wi hbi)
  have hmj : (init.getD j DomC.empty).mem wj = true :=
    (DomC.mem_iff _ _ (hinit j (by simp)) wj).mpr (hfit.2 j wj hbj)
  exact ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩

theorem eqSlot_sem (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) :
    EqSlotSem p i j := by
  intro a ha hacc
  obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
    eqSlot_accepts_data p init i j hinit hmem ha hacc
  obtain ⟨xi, hxi⟩ := DomC.intView_isSome_of_mem hmi
  obtain ⟨xj, hxj⟩ := DomC.intView_isSome_of_mem hmj
  refine ⟨xi, xj, ?_, ?_, ?_⟩
  · simp [slotInt, hbi, hxi]
  · simp [slotInt, hbj, hxj]
  · have hsome : some xi = some xj := by
      rw [← hxi, ← hxj, hwij]
    exact Option.some.inj hsome

theorem eq_iUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {hij : Int} (hsem : EqSlotSem p i j) :
    Entailed p [posLe i hij, negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : xi ≤ hij
  · exact ⟨posLe i hij, by simp, (eval_posLe_iff a i hij).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

theorem eq_jLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi : Int} (hsem : EqSlotSem p i j) :
    Entailed p [negLe j (loi - 1), posLe i (loi - 1)] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : loi - 1 < xj
  · exact ⟨negLe j (loi - 1), by simp,
      (eval_negLe_iff a j (loi - 1)).mpr ⟨xj, hxj, h⟩⟩
  · have hx : xi ≤ loi - 1 := by omega
    exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, hx⟩⟩

theorem eq_iLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loj : Int} (hsem : EqSlotSem p i j) :
    Entailed p [negLe i (loj - 1), posLe j (loj - 1)] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : loj - 1 < xi
  · exact ⟨negLe i (loj - 1), by simp,
      (eval_negLe_iff a i (loj - 1)).mpr ⟨xi, hxi, h⟩⟩
  · have hx : xj ≤ loj - 1 := by omega
    exact ⟨posLe j (loj - 1), by simp,
      (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, hx⟩⟩

theorem eq_jUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {hii : Int} (hsem : EqSlotSem p i j) :
    Entailed p [posLe j hii, negLe i hii] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : xj ≤ hii
  · exact ⟨posLe j hii, by simp, (eval_posLe_iff a j hii).mpr ⟨xj, hxj, h⟩⟩
  · have hx : hii < xi := by omega
    exact ⟨negLe i hii, by simp, (eval_negLe_iff a i hii).mpr ⟨xi, hxi, hx⟩⟩

theorem eq_conflict_ji_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loi hij : Int} (hsem : EqSlotSem p i j) (hconf : hij < loi) :
    Entailed p [posLe i (loi - 1), negLe j hij] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : xi ≤ loi - 1
  · exact ⟨posLe i (loi - 1), by simp,
      (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, h⟩⟩
  · have hx : hij < xj := by omega
    exact ⟨negLe j hij, by simp, (eval_negLe_iff a j hij).mpr ⟨xj, hxj, hx⟩⟩

theorem eq_conflict_ij_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {loj hii : Int} (hsem : EqSlotSem p i j) (hconf : hii < loj) :
    Entailed p [posLe j (loj - 1), negLe i hii] := by
  intro a _ha hacc
  obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a _ha hacc
  by_cases h : xj ≤ loj - 1
  · exact ⟨posLe j (loj - 1), by simp,
      (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, h⟩⟩
  · have hx : hii < xi := by omega
    exact ⟨negLe i hii, by simp, (eval_negLe_iff a i hii).mpr ⟨xi, hxi, hx⟩⟩

theorem eqConflict_reason_entailed (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints)
    (vi vj : Value) (hne : vi ≠ vj)
    (hgi : (init.getD i DomC.empty).mem vi = true)
    (hgj : (init.getD j DomC.empty).mem vj = true) :
    Entailed p [neLit i vi, neLit j vj] := by
  cases vi with
  | int x =>
      cases vj with
      | int y =>
          have hxy : x ≠ y := by
            intro h
            exact hne (by rw [h])
          intro b hb hacc
          obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
            eqSlot_accepts_data p init i j hinit hmem hb hacc
          have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
            (vi := .int x) (w := wi) hgi hmi hbi
          have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
            (vi := .int y) (w := wj) hgj hmj hbj
          by_cases htrue : (neLit i (.int x)).eval b = some true
          · exact ⟨neLit i (.int x), by simp, htrue⟩
          · have hwi : wi = .int x := by
              apply Classical.byContradiction
              intro hneq
              exact htrue (hiffi.mpr hneq)
            have hwj : wj = .int x := by rw [← hwij, hwi]
            refine ⟨neLit j (.int y), by simp, hiffj.mpr ?_⟩
            intro hwjy
            exact hxy (by
              have : (.int x : Value) = .int y := by rw [← hwj, hwjy]
              simpa using this)
      | bool c =>
          intro b hb hacc
          obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
            eqSlot_accepts_data p init i j hinit hmem hb hacc
          obtain ⟨yi, hwi⟩ := DomC.mem_int_kind hgi hmi
          obtain ⟨cj, hwj⟩ := DomC.mem_bool_kind hgj hmj
          rw [hwi, hwj] at hwij
          cases hwij
      | setOfInt _ => simp [DomC.mem] at hgj
      | array _ => simp [DomC.mem] at hgj
  | bool b =>
      cases vj with
      | int y =>
          intro bb hb hacc
          obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
            eqSlot_accepts_data p init i j hinit hmem hb hacc
          obtain ⟨bi, hwi⟩ := DomC.mem_bool_kind hgi hmi
          obtain ⟨yj, hwj⟩ := DomC.mem_int_kind hgj hmj
          rw [hwi, hwj] at hwij
          cases hwij
      | bool c =>
          have hbc : b ≠ c := by
            intro h
            exact hne (by rw [h])
          intro bb hb hacc
          obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
            eqSlot_accepts_data p init i j hinit hmem hb hacc
          have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
            (vi := .bool b) (w := wi) hgi hmi hbi
          have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
            (vi := .bool c) (w := wj) hgj hmj hbj
          by_cases htrue : (neLit i (.bool b)).eval bb = some true
          · exact ⟨neLit i (.bool b), by simp, htrue⟩
          · have hwi : wi = .bool b := by
              apply Classical.byContradiction
              intro hneq
              exact htrue (hiffi.mpr hneq)
            have hwj : wj = .bool b := by rw [← hwij, hwi]
            refine ⟨neLit j (.bool c), by simp, hiffj.mpr ?_⟩
            intro hwjc
            exact hbc (by
              have : (.bool b : Value) = .bool c := by rw [← hwj, hwjc]
              simpa using this)
      | setOfInt _ => simp [DomC.mem] at hgj
      | array _ => simp [DomC.mem] at hgj
  | setOfInt _ => simp [DomC.mem] at hgi
  | array _ => simp [DomC.mem] at hgi

theorem eqPropWith_prune_reason_entailed_i (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints)
    (vi : Value)
    (hgi : (init.getD i DomC.empty).mem vi = true)
    (hgj : (init.getD j DomC.empty).mem vi = true) :
    Entailed p [neLit i vi, eqLit j vi] := by
  intro b hb hacc
  obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
    eqSlot_accepts_data p init i j hinit hmem hb hacc
  have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
    (vi := vi) (w := wi) hgi hmi hbi
  have hiffj := eqLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
    (vi := vi) (w := wj) hgj hmj hbj
  by_cases htrue : (neLit i vi).eval b = some true
  · exact ⟨neLit i vi, by simp, htrue⟩
  · have hwi : wi = vi := by
      apply Classical.byContradiction
      intro hneq
      exact htrue (hiffi.mpr hneq)
    have hwj : wj = vi := by rw [← hwij, hwi]
    exact ⟨eqLit j vi, by simp, hiffj.mpr hwj⟩

theorem eqPropWith_prune_reason_entailed_j (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints)
    (vj : Value)
    (hgi : (init.getD i DomC.empty).mem vj = true)
    (hgj : (init.getD j DomC.empty).mem vj = true) :
    Entailed p [eqLit i vj, neLit j vj] := by
  intro b hb hacc
  obtain ⟨wi, wj, hbi, hbj, hwij, hmi, hmj⟩ :=
    eqSlot_accepts_data p init i j hinit hmem hb hacc
  have hiffi := eqLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
    (vi := vj) (w := wi) hgi hmi hbi
  have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
    (vi := vj) (w := wj) hgj hmj hbj
  by_cases htrue : (neLit j vj).eval b = some true
  · exact ⟨neLit j vj, by simp, htrue⟩
  · have hwj : wj = vj := by
      apply Classical.byContradiction
      intro hneq
      exact htrue (hiffj.mpr hneq)
    have hwi : wi = vj := hwij.trans hwj
    exact ⟨eqLit i vj, by simp, hiffi.mpr hwi⟩


/-- Facts about one emitted prune: its literal, exact decoded reason and
the entailedness of that reason. -/
def EqPruneFacts (p : CompiledProblem DomConstraint) (T : LitTable)
    (ps : Array (PLit × EClause p T)) (l : Literal) (ls : List Literal) : Prop :=
  ∀ q ∈ ps.toList, q.1.lit = l ∧
    T.decodeClause q.2.lits = ls ∧ Entailed p ls

theorem eqPruneFacts_singleton (p : CompiledProblem DomConstraint) (T : LitTable)
    (l : Literal) (ls : List Literal) (hent : Entailed p ls) :
    EqPruneFacts p T #[(pLit l, EClause.ofLiterals p T ls hent)] l ls := by
  intro q hq
  have hq' : q = (pLit l, EClause.ofLiterals p T ls hent) := by
    simpa using hq
  subst hq'
  exact ⟨rfl, LitTable.decodeClause_map_pLit T ls, hent⟩

/-- `x_i = x_j` propagator.  Fixed values decide equality (conflict on a
value clash, including a Boolean/integer clash), one fixed side prunes the
other to the fixed value, and two interval domains are intersected.  One
bound is emitted per run. -/
def eqPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) : PropV2 p T :=
  let hsem := eqSlot_sem p init i j hinit hmem
  { vars := (dcSlotsFull (DomConstraint.eqSlot i j)).toArray
    events := #[(i, .bounds), (j, .bounds), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      match di.fixedValue, dj.fixedValue with
      | some vi, some vj =>
          if _heq : vi == vj then .fix
          else if hgi : (init.getD i DomC.empty).mem vi = true then
            if hgj : (init.getD j DomC.empty).mem vj = true then
              .conflict (EClause.ofLiterals p T [neLit i vi, neLit j vj]
                (eqConflict_reason_entailed p init i j hinit hmem vi vj
                  (by intro h; subst h; simpa using _heq) hgi hgj))
            else .fix
          else .fix
      | some vi, none =>
          if _hdj : dj.mem vi = true then
            if hgi : (init.getD i DomC.empty).mem vi = true then
              if hgj : (init.getD j DomC.empty).mem vi = true then
                .prune #[(pLit (eqLit j vi), EClause.ofLiterals p T
                  [neLit i vi, eqLit j vi]
                  (eqPropWith_prune_reason_entailed_i p init i j hinit hmem vi hgi hgj))]
              else .fix
            else .fix
          else .fix
      | none, some vj =>
          if _hdi : di.mem vj = true then
            if hgi : (init.getD i DomC.empty).mem vj = true then
              if hgj : (init.getD j DomC.empty).mem vj = true then
                .prune #[(pLit (eqLit i vj), EClause.ofLiterals p T
                  [eqLit i vj, neLit j vj]
                  (eqPropWith_prune_reason_entailed_j p init i j hinit hmem vj hgi hgj))]
              else .fix
            else .fix
          else .fix
      | none, none =>
          match domBounds di, domBounds dj with
          | some (loi, hii), some (loj, hij) =>
              if _hdisj : hii < loj ∨ hij < loi then .fix
              else if _hiu : hii > hij then
                .prune #[(pLit (posLe i hij), EClause.ofLiterals p T
                  [posLe i hij, negLe j hij]
                  (eq_iUpper_reason_entailed hsem))]
              else if _hjl : loj < loi then
                .prune #[(pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  [negLe j (loi - 1), posLe i (loi - 1)]
                  (eq_jLower_reason_entailed hsem))]
              else if _hil : loi < loj then
                .prune #[(pLit (negLe i (loj - 1)), EClause.ofLiterals p T
                  [negLe i (loj - 1), posLe j (loj - 1)]
                  (eq_iLower_reason_entailed hsem))]
              else if _hju : hij > hii then
                .prune #[(pLit (posLe j hii), EClause.ofLiterals p T
                  [posLe j hii, negLe i hii]
                  (eq_jUpper_reason_entailed hsem))]
              else .fix
          | _, _ => .fix }

theorem eqPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (eqPropWith p T init i j hinit hmem).run view = .conflict ec) :
    ∃ vi vj,
      (view.doms.getD i DomC.empty).fixedValue = some vi ∧
      (view.doms.getD j DomC.empty).fixedValue = some vj ∧
      vi ≠ vj ∧
      (init.getD i DomC.empty).mem vi = true ∧
      (init.getD j DomC.empty).mem vj = true ∧
      T.decodeClause ec.lits = [neLit i vi, neLit j vj] ∧
      Entailed p [neLit i vi, neLit j vj] := by
  unfold eqPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 vi vj hfi hfj
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i hgi
        split at h
        · rename_i hgj
          injection h with hec
          subst hec
          refine ⟨vi, vj, hfi, hfj,
            (by intro hv; subst hv; simpa using hne), hgi, hgj, ?_,
            eqConflict_reason_entailed p init i j hinit hmem vi vj
              (by intro hv; subst hv; simpa using hne) hgi hgj⟩
          change T.decodeClause
            ([neLit i vi, neLit j vj].toArray.map pLit) =
            [neLit i vi, neLit j vj]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
      · cases h
  · split at h
    · rename_i _hdj
      split at h
      · rename_i _hgi
        split at h <;> cases h
      · cases h
    · cases h
  · split at h
    · rename_i _hdi
      split at h
      · rename_i _hgi
        split at h <;> cases h
      · cases h
    · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h <;> cases h
    · cases h

theorem eqPropWith_run_prune (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (eqPropWith p T init i j hinit hmem).run view = .prune ps) :
    (∃ vi,
      (view.doms.getD i DomC.empty).fixedValue = some vi ∧
      (view.doms.getD j DomC.empty).fixedValue = none ∧
      (view.doms.getD j DomC.empty).mem vi = true ∧
      (init.getD i DomC.empty).mem vi = true ∧
      (init.getD j DomC.empty).mem vi = true ∧
      EqPruneFacts p T ps (eqLit j vi) [neLit i vi, eqLit j vi]) ∨
    (∃ vj,
      (view.doms.getD i DomC.empty).fixedValue = none ∧
      (view.doms.getD j DomC.empty).fixedValue = some vj ∧
      (view.doms.getD i DomC.empty).mem vj = true ∧
      (init.getD i DomC.empty).mem vj = true ∧
      (init.getD j DomC.empty).mem vj = true ∧
      EqPruneFacts p T ps (eqLit i vj) [eqLit i vj, neLit j vj]) ∨
    (∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ (hii < loj ∨ hij < loi) ∧
      hii > hij ∧
      EqPruneFacts p T ps (posLe i hij) [posLe i hij, negLe j hij]) ∨
    (∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ (hii < loj ∨ hij < loi) ∧
      ¬ hii > hij ∧ loj < loi ∧
      EqPruneFacts p T ps (negLe j (loi - 1)) [negLe j (loi - 1), posLe i (loi - 1)]) ∨
    (∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ (hii < loj ∨ hij < loi) ∧
      ¬ hii > hij ∧ ¬ loj < loi ∧ loi < loj ∧
      EqPruneFacts p T ps (negLe i (loj - 1)) [negLe i (loj - 1), posLe j (loj - 1)]) ∨
    (∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      ¬ (hii < loj ∨ hij < loi) ∧
      ¬ hii > hij ∧ ¬ loj < loi ∧ ¬ loi < loj ∧ hij > hii ∧
      EqPruneFacts p T ps (posLe j hii) [posLe j hii, negLe i hii]) := by
  unfold eqPropWith at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · rename_i _hne
      split at h
      · rename_i _hgi
        split at h <;> cases h
      · cases h
  · rename_i _x1 _x2 vi hfi hfj
    split at h
    · rename_i hdj
      split at h
      · rename_i hgi
        split at h
        · rename_i hgj
          cases h
          exact Or.inl ⟨vi, hfi, hfj, hdj, hgi, hgj,
            eqPruneFacts_singleton p T (eqLit j vi) [neLit i vi, eqLit j vi]
              (eqPropWith_prune_reason_entailed_i p init i j hinit hmem vi hgi hgj)⟩
        · cases h
      · cases h
    · cases h
  · rename_i _x1 _x2 vj hfi hfj
    split at h
    · rename_i hdi
      split at h
      · rename_i hgi
        split at h
        · rename_i hgj
          cases h
          exact Or.inr (Or.inl ⟨vj, hfi, hfj, hdi, hgi, hgj,
            eqPruneFacts_singleton p T (eqLit i vj) [eqLit i vj, neLit j vj]
              (eqPropWith_prune_reason_entailed_j p init i j hinit hmem vj hgi hgj)⟩)
        · cases h
      · cases h
    · cases h
  · rename_i _x1 _x2 _hfi _hfj
    split at h
    · rename_i _x1' _x2' loi hii loj hij hbi hbj
      obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
      obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
      split at h
      · cases h
      · rename_i hndisj
        split at h
        · rename_i hiu
          cases h
          exact Or.inr (Or.inr (Or.inl ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            hndisj, hiu,
            eqPruneFacts_singleton p T (posLe i hij) [posLe i hij, negLe j hij]
              (eq_iUpper_reason_entailed (eqSlot_sem p init i j hinit hmem))⟩))
        · rename_i hiu
          split at h
          · rename_i hjl
            cases h
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨loi, hii, loj, hij,
              hloi, hhii, hloj, hhij, hndisj, hiu, hjl,
              eqPruneFacts_singleton p T (negLe j (loi - 1))
                [negLe j (loi - 1), posLe i (loi - 1)]
                (eq_jLower_reason_entailed (eqSlot_sem p init i j hinit hmem))⟩)))
          · rename_i hjl
            split at h
            · rename_i hil
              cases h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨loi, hii, loj, hij,
                hloi, hhii, hloj, hhij, hndisj, hiu, hjl, hil,
                eqPruneFacts_singleton p T (negLe i (loj - 1))
                  [negLe i (loj - 1), posLe j (loj - 1)]
                  (eq_iLower_reason_entailed (eqSlot_sem p init i j hinit hmem))⟩))))
            · rename_i hil
              split at h
              · rename_i hju
                cases h
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨loi, hii, loj, hij,
                  hloi, hhii, hloj, hhij, hndisj, hiu, hjl, hil, hju,
                  eqPruneFacts_singleton p T (posLe j hii) [posLe j hii, negLe i hii]
                    (eq_jUpper_reason_entailed (eqSlot_sem p init i j hinit hmem))⟩))))
              · cases h
    · cases h

theorem eqPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (eqPropWith p T init i j hinit hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, hdec, hent⟩ :=
    eqPropWith_run_conflict p init i j hinit hmem view h
  rwa [hdec]

theorem eqPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ec : EClause p T}
    (h : (eqPropWith p T init i j hinit hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨vi, vj, hfi, hfj, _hne, _hgi, _hgj, hdec, _hent⟩ :=
    eqPropWith_run_conflict p init i j hinit hmem view h
  rw [hdec]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · rw [atomSlot_neLit]
    exact DomC.evalLit_neLit_fixed_false hWFi hfi
  · rw [atomSlot_neLit]
    exact DomC.evalLit_neLit_fixed_false hWFj hfj

theorem eqPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (eqPropWith p T init i j hinit hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  rcases eqPropWith_run_prune p init i j hinit hmem view h with
    hA | hB | hC | hD | hE | hF
  · obtain ⟨_, _, _, _, _, _, hfacts⟩ := hA
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, hfacts⟩ := hB
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hfacts⟩ := hC
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfacts⟩ := hD
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hfacts⟩ := hE
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfacts⟩ := hF
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem eqPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (eqPropWith p T init i j hinit hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  rcases eqPropWith_run_prune p init i j hinit hmem view h with
    hA | hB | hC | hD | hE | hF
  · obtain ⟨vi, hfi, hfj, hdj, _hgi, _hgj, hfacts⟩ := hA
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eqLit]
      exact DomC.evalLit_eqLit_none_of_not_fixed hWFj hfj hdj
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · exact absurd hlit.symm hne
  · obtain ⟨vj, hfi, hfj, hdi, _hgi, _hgj, hfacts⟩ := hB
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eqLit]
      exact DomC.evalLit_eqLit_none_of_not_fixed hWFi hfi hdi
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
  · obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, _hndisj, hiu, hfacts⟩ := hC
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · have hlej : loj ≤ hij :=
          DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
        exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
  · obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, _hndisj, _hiu, hjl, hfacts⟩ := hD
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · have hlei : loi ≤ hii :=
          DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
        exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
  · obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, _hndisj, _hiu, _hjl, hil, hfacts⟩ := hE
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · have hlej : loj ≤ hij :=
          DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
        exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
  · obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, _hndisj, _hiu, _hjl, _hil, hju, hfacts⟩ := hF
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd hlit.symm hne
      · have hlei : loi ≤ hii :=
          DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
        exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)

theorem eqPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    (hfi : (view.doms.getD i DomC.empty).fixedValue = none)
    (hfj : (view.doms.getD j DomC.empty).fixedValue = none)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (eqPropWith p T init i j hinit hmem).run view = .fix := by
  unfold eqPropWith
  dsimp only
  rw [hfi, hfj, hi]

theorem eqPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.eqSlot i j ∈ p.constraints) (view : EngineView)
    (hfi : (view.doms.getD i DomC.empty).fixedValue = none)
    (hfj : (view.doms.getD j DomC.empty).fixedValue = none)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (eqPropWith p T init i j hinit hmem).run view = .fix := by
  unfold eqPropWith
  dsimp only
  rw [hfi, hfj, hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl


end LeanFzn.Engine
