/-
Purpose: Order propagators: reified definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Order.ReifiedReasons
DAG: LeanFzn.Engine.Props.Order.ReifiedReasons -> LeanFzn.Engine.Props.Order.Reified.
-/
import LeanFzn.Engine.Props.Order.ReifiedReasons

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ### Reified decisions at fixed operands -/

/-- `eqReif` at two fixed equal integers forces `r` true. -/
theorem eqReif_decide_true_reason_entailed (p : CompiledProblem DomConstraint)
    (i j r : Nat) (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints)
    {x y : Int} (hxy : x = y) :
    Entailed p [posBool r true, neLit i (.int x), neLit j (.int y)] := by
  intro a ha hacc
  have hdc : (DomConstraint.eqReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨p_, q_, rb, hbi, hbj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hsi : slotInt a i = some p_ := by simp [slotInt, hbi, Value.intView]
  have hsj : slotInt a j = some q_ := by simp [slotInt, hbj, Value.intView]
  by_cases hi : (neLit i (.int x)).eval a = some true
  · exact ⟨neLit i (.int x), by simp, hi⟩
  · by_cases hj : (neLit j (.int y)).eval a = some true
    · exact ⟨neLit j (.int y), by simp, hj⟩
    · have hp : p_ = x := by
        apply Classical.byContradiction
        intro hne'
        exact hi ((neLit_int_eval_true_iff hsi).mpr hne')
      have hq : q_ = y := by
        apply Classical.byContradiction
        intro hne'
        exact hj ((neLit_int_eval_true_iff hsj).mpr hne')
      have hpq : p_ = q_ := by rw [hp, hq, hxy]
      have hrb : rb = true := hiff.mpr hpq
      exact ⟨posBool r true, by simp,
        (eval_posBool_iff a r true).mpr (by rw [hr, hrb])⟩

/-- `eqReif` at two fixed distinct integers forces `r` false. -/
theorem eqReif_decide_false_reason_entailed (p : CompiledProblem DomConstraint)
    (i j r : Nat) (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints)
    {x y : Int} (hxy : x ≠ y) :
    Entailed p [posBool r false, neLit i (.int x), neLit j (.int y)] := by
  intro a ha hacc
  have hdc : (DomConstraint.eqReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨p_, q_, rb, hbi, hbj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hsi : slotInt a i = some p_ := by simp [slotInt, hbi, Value.intView]
  have hsj : slotInt a j = some q_ := by simp [slotInt, hbj, Value.intView]
  by_cases hi : (neLit i (.int x)).eval a = some true
  · exact ⟨neLit i (.int x), by simp, hi⟩
  · by_cases hj : (neLit j (.int y)).eval a = some true
    · exact ⟨neLit j (.int y), by simp, hj⟩
    · have hp : p_ = x := by
        apply Classical.byContradiction
        intro hne'
        exact hi ((neLit_int_eval_true_iff hsi).mpr hne')
      have hq : q_ = y := by
        apply Classical.byContradiction
        intro hne'
        exact hj ((neLit_int_eval_true_iff hsj).mpr hne')
      have hpqne : p_ ≠ q_ := by rw [hp, hq]; exact hxy
      have hrb : rb = false := by
        cases rb with
        | false => rfl
        | true => exact absurd (hiff.mp rfl) hpqne
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr, hrb])⟩

/-- `neReif` at two fixed equal integers forces `r` false. -/
theorem neReif_decide_false_reason_entailed (p : CompiledProblem DomConstraint)
    (i j r : Nat) (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints)
    {x y : Int} (hxy : x = y) :
    Entailed p [posBool r false, neLit i (.int x), neLit j (.int y)] := by
  intro a ha hacc
  have hdc : (DomConstraint.neReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨p_, q_, rb, hbi, hbj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hsi : slotInt a i = some p_ := by simp [slotInt, hbi, Value.intView]
  have hsj : slotInt a j = some q_ := by simp [slotInt, hbj, Value.intView]
  by_cases hi : (neLit i (.int x)).eval a = some true
  · exact ⟨neLit i (.int x), by simp, hi⟩
  · by_cases hj : (neLit j (.int y)).eval a = some true
    · exact ⟨neLit j (.int y), by simp, hj⟩
    · have hp : p_ = x := by
        apply Classical.byContradiction
        intro hne'
        exact hi ((neLit_int_eval_true_iff hsi).mpr hne')
      have hq : q_ = y := by
        apply Classical.byContradiction
        intro hne'
        exact hj ((neLit_int_eval_true_iff hsj).mpr hne')
      have hpq : p_ = q_ := by rw [hp, hq, hxy]
      have hrb : rb = false := by
        cases rb with
        | false => rfl
        | true => exact absurd hpq (hiff.mp rfl)
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr, hrb])⟩

/-- `neReif` at two fixed distinct integers forces `r` true. -/
theorem neReif_decide_true_reason_entailed (p : CompiledProblem DomConstraint)
    (i j r : Nat) (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints)
    {x y : Int} (hxy : x ≠ y) :
    Entailed p [posBool r true, neLit i (.int x), neLit j (.int y)] := by
  intro a ha hacc
  have hdc : (DomConstraint.neReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨p_, q_, rb, hbi, hbj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hsi : slotInt a i = some p_ := by simp [slotInt, hbi, Value.intView]
  have hsj : slotInt a j = some q_ := by simp [slotInt, hbj, Value.intView]
  by_cases hi : (neLit i (.int x)).eval a = some true
  · exact ⟨neLit i (.int x), by simp, hi⟩
  · by_cases hj : (neLit j (.int y)).eval a = some true
    · exact ⟨neLit j (.int y), by simp, hj⟩
    · have hp : p_ = x := by
        apply Classical.byContradiction
        intro hne'
        exact hi ((neLit_int_eval_true_iff hsi).mpr hne')
      have hq : q_ = y := by
        apply Classical.byContradiction
        intro hne'
        exact hj ((neLit_int_eval_true_iff hsj).mpr hne')
      have hpqne : p_ ≠ q_ := by rw [hp, hq]; exact hxy
      have hrb : rb = true := hiff.mpr hpqne
      exact ⟨posBool r true, by simp,
        (eval_posBool_iff a r true).mpr (by rw [hr, hrb])⟩

/-- Reified `x_i = x_j`: `r` true propagates equality, `r` false
propagates disequality, and an unfixed `r` is decided by fixed operands
or by disjoint intervals. -/
def eqReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j r : Nat) (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) :
    PropV2 p T :=
  let htrue := eqReif_true_sem p i j r hmem
  let hfalse := eqReif_false_sem p i j r hmem
  { vars := (dcSlotsFull (DomConstraint.eqReifSlot i j r)).toArray
    events := #[(i, .bounds), (j, .bounds), (r, .fix), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      let dr := view.doms.getD r DomC.empty
      match domBounds di, domBounds dj with
      | some (loi, hii), some (loj, hij) =>
          match dr.fixedValue with
          | some (.bool true) =>
              if hconf : hij < loi then
                .conflict (EClause.ofLiterals p T
                  ([posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)])
                  (eqReif_true_conflict_ij_reason_entailed htrue hconf))
              else if hconf : hii < loj then
                .conflict (EClause.ofLiterals p T
                  ([posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool true)])
                  (eqReif_true_conflict_ji_reason_entailed htrue hconf))
              else if _hiu : hii > hij then
                .prune #[(pLit (posLe i hij), EClause.ofLiterals p T
                  ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])
                  (eqReif_true_iUpper_reason_entailed htrue))]
              else if _hjl : loj < loi then
                .prune #[(pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)])
                  (eqReif_true_jLower_reason_entailed htrue))]
              else if _hil : loi < loj then
                .prune #[(pLit (negLe i (loj - 1)), EClause.ofLiterals p T
                  ([negLe i (loj - 1), posLe j (loj - 1)] ++ [neLit r (.bool true)])
                  (eqReif_true_iLower_reason_entailed htrue))]
              else if _hju : hij > hii then
                .prune #[(pLit (posLe j hii), EClause.ofLiterals p T
                  ([posLe j hii, negLe i hii] ++ [neLit r (.bool true)])
                  (eqReif_true_jUpper_reason_entailed htrue))]
              else .fix
          | some (.bool false) =>
              match di.fixedValue, dj.fixedValue with
              | some (.int x), some (.int y) =>
                  if hxy : x = y then
                    .conflict (EClause.ofLiterals p T
                      ([neLit i (.int x), neLit j (.int y)] ++
                        [neLit r (.bool false)])
                      (eqReif_false_conflict_reason_entailed hfalse hxy))
                  else .fix
              | some (.int x), none =>
                  if _hm : dj.mem (.int x) = true then
                    .prune #[(pLit (neLit j (.int x)), EClause.ofLiterals p T
                      ([neLit i (.int x), neLit j (.int x)] ++
                        [neLit r (.bool false)])
                      (eqReif_false_prune_j_reason_entailed hfalse))]
                  else .fix
              | none, some (.int y) =>
                  if _hm : di.mem (.int y) = true then
                    .prune #[(pLit (neLit i (.int y)), EClause.ofLiterals p T
                      ([neLit i (.int y), neLit j (.int y)] ++
                        [neLit r (.bool false)])
                      (eqReif_false_prune_i_reason_entailed hfalse))]
                  else .fix
              | _, _ => .fix
          | some (.int _) => .fix
          | some (.setOfInt _) => .fix
          | some (.array _) => .fix
          | none =>
              match di.fixedValue, dj.fixedValue with
              | some (.int x), some (.int y) =>
                  if hxy : x = y then
                    .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                      [posBool r true, neLit i (.int x), neLit j (.int y)]
                      (eqReif_decide_true_reason_entailed p i j r hmem hxy))]
                  else
                    .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                      [posBool r false, neLit i (.int x), neLit j (.int y)]
                      (eqReif_decide_false_reason_entailed p i j r hmem hxy))]
              | _, _ =>
                  if hconf : hii < loj then
                    .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                      [posBool r false, negLe i hii, posLe j (loj - 1)]
                      (eqReif_disjoint_ij_reason_entailed htrue hconf))]
                  else if hconf : hij < loi then
                    .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                      [posBool r false, negLe j hij, posLe i (loi - 1)]
                      (eqReif_disjoint_ji_reason_entailed htrue hconf))]
                  else .fix
      | _, _ => .fix }

/-- Reified `x_i ≠ x_j`: `r` true propagates disequality, `r` false
propagates equality, and an unfixed `r` is decided by fixed operands
or by disjoint intervals. -/
def neReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j r : Nat) (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) :
    PropV2 p T :=
  let htrue := neReif_true_sem p i j r hmem
  let hfalse := neReif_false_sem p i j r hmem
  { vars := (dcSlotsFull (DomConstraint.neReifSlot i j r)).toArray
    events := #[(i, .bounds), (j, .bounds), (r, .fix), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      let dr := view.doms.getD r DomC.empty
      match domBounds di, domBounds dj with
      | some (loi, hii), some (loj, hij) =>
          match dr.fixedValue with
          | some (.bool true) =>
              match di.fixedValue, dj.fixedValue with
              | some (.int x), some (.int y) =>
                  if hxy : x = y then
                    .conflict (EClause.ofLiterals p T
                      ([neLit i (.int x), neLit j (.int y)] ++
                        [neLit r (.bool true)])
                      (eqReif_false_conflict_reason_entailed htrue hxy))
                  else .fix
              | some (.int x), none =>
                  if _hm : dj.mem (.int x) = true then
                    .prune #[(pLit (neLit j (.int x)), EClause.ofLiterals p T
                      ([neLit i (.int x), neLit j (.int x)] ++
                        [neLit r (.bool true)])
                      (eqReif_false_prune_j_reason_entailed htrue))]
                  else .fix
              | none, some (.int y) =>
                  if _hm : di.mem (.int y) = true then
                    .prune #[(pLit (neLit i (.int y)), EClause.ofLiterals p T
                      ([neLit i (.int y), neLit j (.int y)] ++
                        [neLit r (.bool true)])
                      (eqReif_false_prune_i_reason_entailed htrue))]
                  else .fix
              | _, _ => .fix
          | some (.bool false) =>
              if hconf : hij < loi then
                .conflict (EClause.ofLiterals p T
                  ([posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool false)])
                  (eqReif_true_conflict_ij_reason_entailed hfalse hconf))
              else if hconf : hii < loj then
                .conflict (EClause.ofLiterals p T
                  ([posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)])
                  (eqReif_true_conflict_ji_reason_entailed hfalse hconf))
              else if _hiu : hii > hij then
                .prune #[(pLit (posLe i hij), EClause.ofLiterals p T
                  ([posLe i hij, negLe j hij] ++ [neLit r (.bool false)])
                  (eqReif_true_iUpper_reason_entailed hfalse))]
              else if _hjl : loj < loi then
                .prune #[(pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool false)])
                  (eqReif_true_jLower_reason_entailed hfalse))]
              else if _hil : loi < loj then
                .prune #[(pLit (negLe i (loj - 1)), EClause.ofLiterals p T
                  ([negLe i (loj - 1), posLe j (loj - 1)] ++ [neLit r (.bool false)])
                  (eqReif_true_iLower_reason_entailed hfalse))]
              else if _hju : hij > hii then
                .prune #[(pLit (posLe j hii), EClause.ofLiterals p T
                  ([posLe j hii, negLe i hii] ++ [neLit r (.bool false)])
                  (eqReif_true_jUpper_reason_entailed hfalse))]
              else .fix
          | some (.int _) => .fix
          | some (.setOfInt _) => .fix
          | some (.array _) => .fix
          | none =>
              match di.fixedValue, dj.fixedValue with
              | some (.int x), some (.int y) =>
                  if hxy : x = y then
                    .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                      [posBool r false, neLit i (.int x), neLit j (.int y)]
                      (neReif_decide_false_reason_entailed p i j r hmem hxy))]
                  else
                    .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                      [posBool r true, neLit i (.int x), neLit j (.int y)]
                      (neReif_decide_true_reason_entailed p i j r hmem hxy))]
              | _, _ =>
                  if hconf : hii < loj then
                    .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                      [posBool r true, negLe i hii, posLe j (loj - 1)]
                      (eqReif_disjoint_ij_reason_entailed hfalse hconf))]
                  else if hconf : hij < loi then
                    .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                      [posBool r true, negLe j hij, posLe i (loi - 1)]
                      (eqReif_disjoint_ji_reason_entailed hfalse hconf))]
                  else .fix
      | _, _ => .fix }

theorem eqReifPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (eqReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ((hij < loi ∧
              T.decodeClause ec.lits =
                [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)] ∧
              Entailed p ([posLe i (loi - 1), negLe j hij] ++
                [neLit r (.bool true)])) ∨
           (hii < loj ∧
              T.decodeClause ec.lits =
                [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool true)] ∧
              Entailed p ([posLe j (loj - 1), negLe i hii] ++
                [neLit r (.bool true)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          ∃ x y : Int,
            (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
            (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
            x = y ∧
            T.decodeClause ec.lits =
              [neLit i (.int x), neLit j (.int y)] ++ [neLit r (.bool false)] ∧
            Entailed p ([neLit i (.int x), neLit j (.int y)] ++
              [neLit r (.bool false)]))) := by
  unfold eqReifPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hrt
      by_cases hconf : hij < loi
      · rw [dif_pos hconf] at h
        injection h with hec
        subst hec
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
          Or.inl ⟨hrt, Or.inl ⟨hconf, ?_, ?_⟩⟩⟩
        · change T.decodeClause
            (([posLe i (loi - 1), negLe j hij] ++
              [neLit r (.bool true)]).toArray.map pLit) =
            [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)]
          exact LitTable.decodeClause_map_pLit T _
        · exact eqReif_true_conflict_ij_reason_entailed
            (eqReif_true_sem p i j r hmem) hconf
      · rw [dif_neg hconf] at h
        by_cases hconf2 : hii < loj
        · rw [dif_pos hconf2] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inl ⟨hrt, Or.inr ⟨hconf2, ?_, ?_⟩⟩⟩
          · change T.decodeClause
              (([posLe j (loj - 1), negLe i hii] ++
                [neLit r (.bool true)]).toArray.map pLit) =
              [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool true)]
            exact LitTable.decodeClause_map_pLit T _
          · exact eqReif_true_conflict_ji_reason_entailed
              (eqReif_true_sem p i j r hmem) hconf2
        · rw [dif_neg hconf2] at h
          by_cases hiu : hii > hij
          · rw [dif_pos hiu] at h; cases h
          · rw [dif_neg hiu] at h
            by_cases hjl : loj < loi
            · rw [dif_pos hjl] at h; cases h
            · rw [dif_neg hjl] at h
              by_cases hil : loi < loj
              · rw [dif_pos hil] at h; cases h
              · rw [dif_neg hil] at h
                by_cases hju : hij > hii
                · rw [dif_pos hju] at h; cases h
                · rw [dif_neg hju] at h; cases h
    · rename_i hrf
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr ⟨hrf, x, y, hfi, hfj, hxy, ?_, ?_⟩⟩
          · change T.decodeClause
              (([neLit i (.int x), neLit j (.int y)] ++
                [neLit r (.bool false)]).toArray.map pLit) =
              [neLit i (.int x), neLit j (.int y)] ++ [neLit r (.bool false)]
            exact LitTable.decodeClause_map_pLit T _
          · exact eqReif_false_conflict_reason_entailed
              (eqReif_false_sem p i j r hmem) hxy
        · rw [dif_neg hxy] at h; cases h
      · split at h <;> cases h
      · split at h <;> cases h
      · cases h
    · cases h
    · cases h
    · cases h
    · split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h; cases h
        · rw [dif_neg hxy] at h; cases h
      · by_cases h1 : hii < loj
        · rw [dif_pos h1] at h; cases h
        · rw [dif_neg h1] at h
          by_cases h2 : hij < loi
          · rw [dif_pos h2] at h; cases h
          · rw [dif_neg h2] at h; cases h
  · cases h

theorem eqReifPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (eqReifPropWith p T i j r hmem).run view = .prune ps) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ((¬ hij < loi ∧ ¬ hii < loj ∧ hii > hij ∧
              PruneFacts p T ps (posLe i hij)
              ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ loj < loi ∧
              PruneFacts p T ps (negLe j (loi - 1))
              ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ ¬ loj < loi ∧ loi < loj ∧
              PruneFacts p T ps (negLe i (loj - 1))
              ([negLe i (loj - 1), posLe j (loj - 1)] ++ [neLit r (.bool true)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ ¬ loj < loi ∧ ¬ loi < loj ∧
              hij > hii ∧
              PruneFacts p T ps (posLe j hii)
              ([posLe j hii, negLe i hii] ++ [neLit r (.bool true)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          ((∃ x : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = none ∧
              (view.doms.getD j DomC.empty).mem (.int x) = true ∧
              PruneFacts p T ps (neLit j (.int x))
                ([neLit i (.int x), neLit j (.int x)] ++ [neLit r (.bool false)])) ∨
           (∃ y : Int,
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              (view.doms.getD i DomC.empty).fixedValue = none ∧
              (view.doms.getD i DomC.empty).mem (.int y) = true ∧
              PruneFacts p T ps (neLit i (.int y))
                ([neLit i (.int y), neLit j (.int y)] ++ [neLit r (.bool false)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = none ∧
          ((∃ x y : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              x = y ∧
              PruneFacts p T ps (posBool r true)
                [posBool r true, neLit i (.int x), neLit j (.int y)]) ∨
           (∃ x y : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              x ≠ y ∧
              PruneFacts p T ps (posBool r false)
                [posBool r false, neLit i (.int x), neLit j (.int y)]) ∨
           (hii < loj ∧
              PruneFacts p T ps (posBool r false)
                [posBool r false, negLe i hii, posLe j (loj - 1)]) ∨
           (¬ hii < loj ∧ hij < loi ∧
              PruneFacts p T ps (posBool r false)
                [posBool r false, negLe j hij, posLe i (loi - 1)])))) := by
  unfold eqReifPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hrt
      by_cases hconf : hij < loi
      · rw [dif_pos hconf] at h; cases h
      · rw [dif_neg hconf] at h
        by_cases hconf2 : hii < loj
        · rw [dif_pos hconf2] at h; cases h
        · rw [dif_neg hconf2] at h
          by_cases hiu : hii > hij
          · rw [dif_pos hiu] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inl ⟨hrt, Or.inl ⟨hconf, hconf2, hiu, ?_⟩⟩⟩
            intro q hq
            have hq' : q = (pLit (posLe i hij), EClause.ofLiterals p T
                ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])
                (eqReif_true_iUpper_reason_entailed
                  (eqReif_true_sem p i j r hmem))) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              eqReif_true_iUpper_reason_entailed
                (eqReif_true_sem p i j r hmem)⟩
            change T.decodeClause
              (([posLe i hij, negLe j hij] ++
                [neLit r (.bool true)]).toArray.map pLit) =
              [posLe i hij, negLe j hij] ++ [neLit r (.bool true)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hiu] at h
            by_cases hjl : loj < loi
            · rw [dif_pos hjl] at h
              injection h with hec
              subst hec
              refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                Or.inl ⟨hrt, Or.inr (Or.inl ⟨hconf, hconf2, hiu, hjl, ?_⟩)⟩⟩
              intro q hq
              have hq' : q = (pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  ([negLe j (loi - 1), posLe i (loi - 1)] ++
                    [neLit r (.bool true)])
                  (eqReif_true_jLower_reason_entailed
                    (eqReif_true_sem p i j r hmem))) := by
                simpa using hq
              subst hq'
              refine ⟨rfl, ?_,
                eqReif_true_jLower_reason_entailed
                  (eqReif_true_sem p i j r hmem)⟩
              change T.decodeClause
                (([negLe j (loi - 1), posLe i (loi - 1)] ++
                  [neLit r (.bool true)]).toArray.map pLit) =
                [negLe j (loi - 1), posLe i (loi - 1)] ++
                  [neLit r (.bool true)]
              exact LitTable.decodeClause_map_pLit T _
            · rw [dif_neg hjl] at h
              by_cases hil : loi < loj
              · rw [dif_pos hil] at h
                injection h with hec
                subst hec
                refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                  Or.inl ⟨hrt, Or.inr (Or.inr (Or.inl ⟨hconf, hconf2, hiu, hjl, hil, ?_⟩))⟩⟩
                intro q hq
                have hq' : q = (pLit (negLe i (loj - 1)), EClause.ofLiterals p T
                    ([negLe i (loj - 1), posLe j (loj - 1)] ++
                      [neLit r (.bool true)])
                    (eqReif_true_iLower_reason_entailed
                      (eqReif_true_sem p i j r hmem))) := by
                  simpa using hq
                subst hq'
                refine ⟨rfl, ?_,
                  eqReif_true_iLower_reason_entailed
                    (eqReif_true_sem p i j r hmem)⟩
                change T.decodeClause
                  (([negLe i (loj - 1), posLe j (loj - 1)] ++
                    [neLit r (.bool true)]).toArray.map pLit) =
                  [negLe i (loj - 1), posLe j (loj - 1)] ++
                    [neLit r (.bool true)]
                exact LitTable.decodeClause_map_pLit T _
              · rw [dif_neg hil] at h
                by_cases hju : hij > hii
                · rw [dif_pos hju] at h
                  injection h with hec
                  subst hec
                  refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                    Or.inl ⟨hrt, Or.inr (Or.inr (Or.inr ⟨hconf, hconf2, hiu, hjl, hil, hju, ?_⟩))⟩⟩
                  intro q hq
                  have hq' : q = (pLit (posLe j hii), EClause.ofLiterals p T
                      ([posLe j hii, negLe i hii] ++ [neLit r (.bool true)])
                      (eqReif_true_jUpper_reason_entailed
                        (eqReif_true_sem p i j r hmem))) := by
                    simpa using hq
                  subst hq'
                  refine ⟨rfl, ?_,
                    eqReif_true_jUpper_reason_entailed
                      (eqReif_true_sem p i j r hmem)⟩
                  change T.decodeClause
                    (([posLe j hii, negLe i hii] ++
                      [neLit r (.bool true)]).toArray.map pLit) =
                    [posLe j hii, negLe i hii] ++ [neLit r (.bool true)]
                  exact LitTable.decodeClause_map_pLit T _
                · rw [dif_neg hju] at h; cases h
    · rename_i hrf
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h; cases h
        · rw [dif_neg hxy] at h; cases h
      · split at h
        · rename_i x hfi hfj hm
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inl ⟨hrf, Or.inl ⟨x, hfi, hfj, hm, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (neLit j (.int x)), EClause.ofLiterals p T
              ([neLit i (.int x), neLit j (.int x)] ++
                [neLit r (.bool false)])
              (eqReif_false_prune_j_reason_entailed
                (eqReif_false_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_false_prune_j_reason_entailed
              (eqReif_false_sem p i j r hmem)⟩
          change T.decodeClause
            (([neLit i (.int x), neLit j (.int x)] ++
              [neLit r (.bool false)]).toArray.map pLit) =
            [neLit i (.int x), neLit j (.int x)] ++ [neLit r (.bool false)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
      · split at h
        · rename_i y hfi hfj hm
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inl ⟨hrf, Or.inr ⟨y, hfj, hfi, hm, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (neLit i (.int y)), EClause.ofLiterals p T
              ([neLit i (.int y), neLit j (.int y)] ++
                [neLit r (.bool false)])
              (eqReif_false_prune_i_reason_entailed
                (eqReif_false_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_false_prune_i_reason_entailed
              (eqReif_false_sem p i j r hmem)⟩
          change T.decodeClause
            (([neLit i (.int y), neLit j (.int y)] ++
              [neLit r (.bool false)]).toArray.map pLit) =
            [neLit i (.int y), neLit j (.int y)] ++ [neLit r (.bool false)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
      · cases h
    · cases h
    · cases h
    · cases h
    · rename_i hnone
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inl ⟨x, y, hfi, hfj, hxy, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
              [posBool r true, neLit i (.int x), neLit j (.int y)]
              (eqReif_decide_true_reason_entailed p i j r hmem hxy)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_decide_true_reason_entailed p i j r hmem hxy⟩
          change T.decodeClause
            ([posBool r true, neLit i (.int x), neLit j (.int y)].toArray.map pLit) =
            [posBool r true, neLit i (.int x), neLit j (.int y)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inr (Or.inl ⟨x, y, hfi, hfj, hxy, ?_⟩)⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
              [posBool r false, neLit i (.int x), neLit j (.int y)]
              (eqReif_decide_false_reason_entailed p i j r hmem hxy)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_decide_false_reason_entailed p i j r hmem hxy⟩
          change T.decodeClause
            ([posBool r false, neLit i (.int x), neLit j (.int y)].toArray.map pLit) =
            [posBool r false, neLit i (.int x), neLit j (.int y)]
          exact LitTable.decodeClause_map_pLit T _
      · by_cases h1 : hii < loj
        · rw [dif_pos h1] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inr (Or.inr (Or.inl ⟨h1, ?_⟩))⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
              [posBool r false, negLe i hii, posLe j (loj - 1)]
              (eqReif_disjoint_ij_reason_entailed
                (eqReif_true_sem p i j r hmem) h1)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_disjoint_ij_reason_entailed
              (eqReif_true_sem p i j r hmem) h1⟩
          change T.decodeClause
            ([posBool r false, negLe i hii, posLe j (loj - 1)].toArray.map pLit) =
            [posBool r false, negLe i hii, posLe j (loj - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg h1] at h
          by_cases h2 : hij < loi
          · rw [dif_pos h2] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inr (Or.inr ⟨hnone, Or.inr (Or.inr (Or.inr ⟨h1, h2, ?_⟩))⟩)⟩
            intro q hq
            have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
                [posBool r false, negLe j hij, posLe i (loi - 1)]
                (eqReif_disjoint_ji_reason_entailed
                  (eqReif_true_sem p i j r hmem) h2)) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              eqReif_disjoint_ji_reason_entailed
                (eqReif_true_sem p i j r hmem) h2⟩
            change T.decodeClause
              ([posBool r false, negLe j hij, posLe i (loi - 1)].toArray.map pLit) =
              [posBool r false, negLe j hij, posLe i (loi - 1)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg h2] at h; cases h
  · cases h

theorem eqReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (eqReifPropWith p T i j r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    eqReifPropWith_run_conflict p T i j r hmem view h
  rcases hbranch with ⟨_, hbody⟩ | ⟨_, x, y, _, _, _, hdec, hent⟩
  · rcases hbody with hA | hB
    · obtain ⟨_, hdec, hent⟩ := hA
      rwa [hdec]
    · obtain ⟨_, hdec, hent⟩ := hB
      rwa [hdec]
  · rwa [hdec]

theorem eqReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ec : EClause p T}
    (h : (eqReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    eqReifPropWith_run_conflict p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hrt, hbody⟩ | ⟨hrf, x, y, hfi, hfj, hxy, hdec, _hent⟩
  · rcases hbody with hA | hB
    · obtain ⟨_, hdec, _hent⟩ := hA
      rw [hdec]
      intro l hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl) | rfl
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
    · obtain ⟨_, hdec, _hent⟩ := hB
      rw [hdec]
      intro l hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl) | rfl
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · rw [hdec]
    intro l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl) | rfl
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFi hfi
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFj hfj
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFr hrf

theorem eqReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (eqReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    eqReifPropWith_run_prune p T i j r hmem view h
  rcases hbranch with
    ⟨_, hA | hB | hC | hD⟩ | ⟨_, hE | hF⟩ | ⟨_, hG | hH | hI | hJ⟩
  · obtain ⟨_, _, _, hfacts⟩ := hA
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, hfacts⟩ := hB
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hC
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, hfacts⟩ := hD
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, hfacts⟩ := hE
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, hfacts⟩ := hF
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hG
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hH
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hfacts⟩ := hI
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, hfacts⟩ := hJ
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem eqReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (eqReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    eqReifPropWith_run_prune p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with
    ⟨hrt, hA | hB | hC | hD⟩ | ⟨hrf, hE | hF⟩ | ⟨hnone, hG | hH | hI | hJ⟩
  · obtain ⟨hconf, hconf2, hiu, hfacts⟩ := hA
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨hconf, hconf2, hiu, hjl, hfacts⟩ := hB
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨hconf, hconf2, hiu, hjl, hil, hfacts⟩ := hC
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨hconf, hconf2, hiu, hjl, hil, hju, hfacts⟩ := hD
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨x, hfi, hfj, hm, hfacts⟩ := hE
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_neLit]
      exact DomC.evalLit_posNe_none_of_mem hfj
        (DomC.memIntView_eq_mem_int hm)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨y, hfj, hfi, hm, hfacts⟩ := hF
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_neLit]
      exact DomC.evalLit_posNe_none_of_mem hfi
        (DomC.memIntView_eq_mem_int hm)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨x, y, hfi, hfj, hxy, hfacts⟩ := hG
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
  · obtain ⟨x, y, hfi, hfj, hxy, hfacts⟩ := hH
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
  · obtain ⟨h1, hfacts⟩ := hI
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
  · obtain ⟨h1, h2, hfacts⟩ := hJ
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)

theorem eqReifPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (eqReifPropWith p T i j r hmem).run view = .fix := by
  unfold eqReifPropWith
  dsimp only
  rw [hi]

theorem eqReifPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (eqReifPropWith p T i j r hmem).run view = .fix := by
  unfold eqReifPropWith
  dsimp only
  rw [hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl

theorem neReifPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (neReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ∃ x y : Int,
            (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
            (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
            x = y ∧
            T.decodeClause ec.lits =
              [neLit i (.int x), neLit j (.int y)] ++ [neLit r (.bool true)] ∧
            Entailed p ([neLit i (.int x), neLit j (.int y)] ++
              [neLit r (.bool true)])) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          ((hij < loi ∧
              T.decodeClause ec.lits =
                [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool false)] ∧
              Entailed p ([posLe i (loi - 1), negLe j hij] ++
                [neLit r (.bool false)])) ∨
           (hii < loj ∧
              T.decodeClause ec.lits =
                [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)] ∧
              Entailed p ([posLe j (loj - 1), negLe i hii] ++
                [neLit r (.bool false)]))))) := by
  unfold neReifPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hrt
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inl ⟨hrt, x, y, hfi, hfj, hxy, ?_, ?_⟩⟩
          · change T.decodeClause
              (([neLit i (.int x), neLit j (.int y)] ++
                [neLit r (.bool true)]).toArray.map pLit) =
              [neLit i (.int x), neLit j (.int y)] ++ [neLit r (.bool true)]
            exact LitTable.decodeClause_map_pLit T _
          · exact eqReif_false_conflict_reason_entailed
              (neReif_true_sem p i j r hmem) hxy
        · rw [dif_neg hxy] at h; cases h
      · split at h <;> cases h
      · split at h <;> cases h
      · cases h
    · rename_i hrf
      by_cases hconf : hij < loi
      · rw [dif_pos hconf] at h
        injection h with hec
        subst hec
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
          Or.inr ⟨hrf, Or.inl ⟨hconf, ?_, ?_⟩⟩⟩
        · change T.decodeClause
            (([posLe i (loi - 1), negLe j hij] ++
              [neLit r (.bool false)]).toArray.map pLit) =
            [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool false)]
          exact LitTable.decodeClause_map_pLit T _
        · exact eqReif_true_conflict_ij_reason_entailed
            (neReif_false_sem p i j r hmem) hconf
      · rw [dif_neg hconf] at h
        by_cases hconf2 : hii < loj
        · rw [dif_pos hconf2] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr ⟨hrf, Or.inr ⟨hconf2, ?_, ?_⟩⟩⟩
          · change T.decodeClause
              (([posLe j (loj - 1), negLe i hii] ++
                [neLit r (.bool false)]).toArray.map pLit) =
              [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)]
            exact LitTable.decodeClause_map_pLit T _
          · exact eqReif_true_conflict_ji_reason_entailed
              (neReif_false_sem p i j r hmem) hconf2
        · rw [dif_neg hconf2] at h
          by_cases hiu : hii > hij
          · rw [dif_pos hiu] at h; cases h
          · rw [dif_neg hiu] at h
            by_cases hjl : loj < loi
            · rw [dif_pos hjl] at h; cases h
            · rw [dif_neg hjl] at h
              by_cases hil : loi < loj
              · rw [dif_pos hil] at h; cases h
              · rw [dif_neg hil] at h
                by_cases hju : hij > hii
                · rw [dif_pos hju] at h; cases h
                · rw [dif_neg hju] at h; cases h
    · cases h
    · cases h
    · cases h
    · split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h; cases h
        · rw [dif_neg hxy] at h; cases h
      · by_cases h1 : hii < loj
        · rw [dif_pos h1] at h; cases h
        · rw [dif_neg h1] at h
          by_cases h2 : hij < loi
          · rw [dif_pos h2] at h; cases h
          · rw [dif_neg h2] at h; cases h
  · cases h

theorem neReifPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (neReifPropWith p T i j r hmem).run view = .prune ps) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ((∃ x : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = none ∧
              (view.doms.getD j DomC.empty).mem (.int x) = true ∧
              PruneFacts p T ps (neLit j (.int x))
                ([neLit i (.int x), neLit j (.int x)] ++ [neLit r (.bool true)])) ∨
           (∃ y : Int,
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              (view.doms.getD i DomC.empty).fixedValue = none ∧
              (view.doms.getD i DomC.empty).mem (.int y) = true ∧
              PruneFacts p T ps (neLit i (.int y))
                ([neLit i (.int y), neLit j (.int y)] ++ [neLit r (.bool true)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          ((¬ hij < loi ∧ ¬ hii < loj ∧ hii > hij ∧
              PruneFacts p T ps (posLe i hij)
              ([posLe i hij, negLe j hij] ++ [neLit r (.bool false)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ loj < loi ∧
              PruneFacts p T ps (negLe j (loi - 1))
              ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool false)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ ¬ loj < loi ∧ loi < loj ∧
              PruneFacts p T ps (negLe i (loj - 1))
              ([negLe i (loj - 1), posLe j (loj - 1)] ++ [neLit r (.bool false)])) ∨
           (¬ hij < loi ∧ ¬ hii < loj ∧ ¬ hii > hij ∧ ¬ loj < loi ∧ ¬ loi < loj ∧
              hij > hii ∧
              PruneFacts p T ps (posLe j hii)
              ([posLe j hii, negLe i hii] ++ [neLit r (.bool false)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = none ∧
          ((∃ x y : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              x = y ∧
              PruneFacts p T ps (posBool r false)
                [posBool r false, neLit i (.int x), neLit j (.int y)]) ∨
           (∃ x y : Int,
              (view.doms.getD i DomC.empty).fixedValue = some (.int x) ∧
              (view.doms.getD j DomC.empty).fixedValue = some (.int y) ∧
              x ≠ y ∧
              PruneFacts p T ps (posBool r true)
                [posBool r true, neLit i (.int x), neLit j (.int y)]) ∨
           (hii < loj ∧
              PruneFacts p T ps (posBool r true)
                [posBool r true, negLe i hii, posLe j (loj - 1)]) ∨
           (¬ hii < loj ∧ hij < loi ∧
              PruneFacts p T ps (posBool r true)
                [posBool r true, negLe j hij, posLe i (loi - 1)])))) := by
  unfold neReifPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hrt
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h; cases h
        · rw [dif_neg hxy] at h; cases h
      · split at h
        · rename_i x hfi hfj hm
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inl ⟨hrt, Or.inl ⟨x, hfi, hfj, hm, ?_⟩⟩⟩
          intro q hq
          have hq' : q = (pLit (neLit j (.int x)), EClause.ofLiterals p T
              ([neLit i (.int x), neLit j (.int x)] ++
                [neLit r (.bool true)])
              (eqReif_false_prune_j_reason_entailed
                (neReif_true_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_false_prune_j_reason_entailed
              (neReif_true_sem p i j r hmem)⟩
          change T.decodeClause
            (([neLit i (.int x), neLit j (.int x)] ++
              [neLit r (.bool true)]).toArray.map pLit) =
            [neLit i (.int x), neLit j (.int x)] ++ [neLit r (.bool true)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
      · split at h
        · rename_i y hfi hfj hm
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inl ⟨hrt, Or.inr ⟨y, hfj, hfi, hm, ?_⟩⟩⟩
          intro q hq
          have hq' : q = (pLit (neLit i (.int y)), EClause.ofLiterals p T
              ([neLit i (.int y), neLit j (.int y)] ++
                [neLit r (.bool true)])
              (eqReif_false_prune_i_reason_entailed
                (neReif_true_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_false_prune_i_reason_entailed
              (neReif_true_sem p i j r hmem)⟩
          change T.decodeClause
            (([neLit i (.int y), neLit j (.int y)] ++
              [neLit r (.bool true)]).toArray.map pLit) =
            [neLit i (.int y), neLit j (.int y)] ++ [neLit r (.bool true)]
          exact LitTable.decodeClause_map_pLit T _
        · cases h
      · cases h
    · rename_i hrf
      by_cases hconf : hij < loi
      · rw [dif_pos hconf] at h; cases h
      · rw [dif_neg hconf] at h
        by_cases hconf2 : hii < loj
        · rw [dif_pos hconf2] at h; cases h
        · rw [dif_neg hconf2] at h
          by_cases hiu : hii > hij
          · rw [dif_pos hiu] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inr (Or.inl ⟨hrf, Or.inl ⟨hconf, hconf2, hiu, ?_⟩⟩)⟩
            intro q hq
            have hq' : q = (pLit (posLe i hij), EClause.ofLiterals p T
                ([posLe i hij, negLe j hij] ++ [neLit r (.bool false)])
                (eqReif_true_iUpper_reason_entailed
                  (neReif_false_sem p i j r hmem))) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              eqReif_true_iUpper_reason_entailed
                (neReif_false_sem p i j r hmem)⟩
            change T.decodeClause
              (([posLe i hij, negLe j hij] ++
                [neLit r (.bool false)]).toArray.map pLit) =
              [posLe i hij, negLe j hij] ++ [neLit r (.bool false)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hiu] at h
            by_cases hjl : loj < loi
            · rw [dif_pos hjl] at h
              injection h with hec
              subst hec
              refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                Or.inr (Or.inl ⟨hrf, Or.inr (Or.inl
                  ⟨hconf, hconf2, hiu, hjl, ?_⟩)⟩)⟩
              intro q hq
              have hq' : q = (pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  ([negLe j (loi - 1), posLe i (loi - 1)] ++
                    [neLit r (.bool false)])
                  (eqReif_true_jLower_reason_entailed
                    (neReif_false_sem p i j r hmem))) := by
                simpa using hq
              subst hq'
              refine ⟨rfl, ?_,
                eqReif_true_jLower_reason_entailed
                  (neReif_false_sem p i j r hmem)⟩
              change T.decodeClause
                (([negLe j (loi - 1), posLe i (loi - 1)] ++
                  [neLit r (.bool false)]).toArray.map pLit) =
                [negLe j (loi - 1), posLe i (loi - 1)] ++
                  [neLit r (.bool false)]
              exact LitTable.decodeClause_map_pLit T _
            · rw [dif_neg hjl] at h
              by_cases hil : loi < loj
              · rw [dif_pos hil] at h
                injection h with hec
                subst hec
                refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                  Or.inr (Or.inl ⟨hrf, Or.inr (Or.inr (Or.inl
                    ⟨hconf, hconf2, hiu, hjl, hil, ?_⟩))⟩)⟩
                intro q hq
                have hq' : q = (pLit (negLe i (loj - 1)), EClause.ofLiterals p T
                    ([negLe i (loj - 1), posLe j (loj - 1)] ++
                      [neLit r (.bool false)])
                    (eqReif_true_iLower_reason_entailed
                      (neReif_false_sem p i j r hmem))) := by
                  simpa using hq
                subst hq'
                refine ⟨rfl, ?_,
                  eqReif_true_iLower_reason_entailed
                    (neReif_false_sem p i j r hmem)⟩
                change T.decodeClause
                  (([negLe i (loj - 1), posLe j (loj - 1)] ++
                    [neLit r (.bool false)]).toArray.map pLit) =
                  [negLe i (loj - 1), posLe j (loj - 1)] ++
                    [neLit r (.bool false)]
                exact LitTable.decodeClause_map_pLit T _
              · rw [dif_neg hil] at h
                by_cases hju : hij > hii
                · rw [dif_pos hju] at h
                  injection h with hec
                  subst hec
                  refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
                    Or.inr (Or.inl ⟨hrf, Or.inr (Or.inr (Or.inr
                      ⟨hconf, hconf2, hiu, hjl, hil, hju, ?_⟩))⟩)⟩
                  intro q hq
                  have hq' : q = (pLit (posLe j hii), EClause.ofLiterals p T
                      ([posLe j hii, negLe i hii] ++ [neLit r (.bool false)])
                      (eqReif_true_jUpper_reason_entailed
                        (neReif_false_sem p i j r hmem))) := by
                    simpa using hq
                  subst hq'
                  refine ⟨rfl, ?_,
                    eqReif_true_jUpper_reason_entailed
                      (neReif_false_sem p i j r hmem)⟩
                  change T.decodeClause
                    (([posLe j hii, negLe i hii] ++
                      [neLit r (.bool false)]).toArray.map pLit) =
                    [posLe j hii, negLe i hii] ++ [neLit r (.bool false)]
                  exact LitTable.decodeClause_map_pLit T _
                · rw [dif_neg hju] at h; cases h
    · cases h
    · cases h
    · cases h
    · rename_i hnone
      split at h
      · rename_i x y hfi hfj
        by_cases hxy : x = y
        · rw [dif_pos hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inl ⟨x, y, hfi, hfj, hxy, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
              [posBool r false, neLit i (.int x), neLit j (.int y)]
              (neReif_decide_false_reason_entailed p i j r hmem hxy)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            neReif_decide_false_reason_entailed p i j r hmem hxy⟩
          change T.decodeClause
            ([posBool r false, neLit i (.int x), neLit j (.int y)].toArray.map pLit) =
            [posBool r false, neLit i (.int x), neLit j (.int y)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hxy] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inr (Or.inl
              ⟨x, y, hfi, hfj, hxy, ?_⟩)⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
              [posBool r true, neLit i (.int x), neLit j (.int y)]
              (neReif_decide_true_reason_entailed p i j r hmem hxy)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            neReif_decide_true_reason_entailed p i j r hmem hxy⟩
          change T.decodeClause
            ([posBool r true, neLit i (.int x), neLit j (.int y)].toArray.map pLit) =
            [posBool r true, neLit i (.int x), neLit j (.int y)]
          exact LitTable.decodeClause_map_pLit T _
      · by_cases h1 : hii < loj
        · rw [dif_pos h1] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inr (Or.inr (Or.inl ⟨h1, ?_⟩))⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
              [posBool r true, negLe i hii, posLe j (loj - 1)]
              (eqReif_disjoint_ij_reason_entailed
                (neReif_false_sem p i j r hmem) h1)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            eqReif_disjoint_ij_reason_entailed
              (neReif_false_sem p i j r hmem) h1⟩
          change T.decodeClause
            ([posBool r true, negLe i hii, posLe j (loj - 1)].toArray.map pLit) =
            [posBool r true, negLe i hii, posLe j (loj - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg h1] at h
          by_cases h2 : hij < loi
          · rw [dif_pos h2] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inr (Or.inr ⟨hnone, Or.inr (Or.inr (Or.inr ⟨h1, h2, ?_⟩))⟩)⟩
            intro q hq
            have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
                [posBool r true, negLe j hij, posLe i (loi - 1)]
                (eqReif_disjoint_ji_reason_entailed
                  (neReif_false_sem p i j r hmem) h2)) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              eqReif_disjoint_ji_reason_entailed
                (neReif_false_sem p i j r hmem) h2⟩
            change T.decodeClause
              ([posBool r true, negLe j hij, posLe i (loi - 1)].toArray.map pLit) =
              [posBool r true, negLe j hij, posLe i (loi - 1)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg h2] at h; cases h
  · cases h

theorem neReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (neReifPropWith p T i j r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    neReifPropWith_run_conflict p T i j r hmem view h
  rcases hbranch with ⟨_, x, y, _, _, _, hdec, hent⟩ | ⟨_, hbody⟩
  · rwa [hdec]
  · rcases hbody with hA | hB
    · obtain ⟨_, hdec, hent⟩ := hA
      rwa [hdec]
    · obtain ⟨_, hdec, hent⟩ := hB
      rwa [hdec]

theorem neReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ec : EClause p T}
    (h : (neReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    neReifPropWith_run_conflict p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hrt, x, y, hfi, hfj, hxy, hdec, _hent⟩ | ⟨hrf, hbody⟩
  · rw [hdec]
    intro l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl) | rfl
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFi hfi
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFj hfj
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · rcases hbody with hA | hB
    · obtain ⟨_, hdec, _hent⟩ := hA
      rw [hdec]
      intro l hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl) | rfl
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
    · obtain ⟨_, hdec, _hent⟩ := hB
      rw [hdec]
      intro l hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl) | rfl
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf

theorem neReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (neReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    neReifPropWith_run_prune p T i j r hmem view h
  rcases hbranch with
    ⟨_, hE | hF⟩ | ⟨_, hA | hB | hC | hD⟩ | ⟨_, hG | hH | hI | hJ⟩
  · obtain ⟨_, _, _, _, hfacts⟩ := hE
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, hfacts⟩ := hF
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, hfacts⟩ := hA
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, hfacts⟩ := hB
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hC
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, _, hfacts⟩ := hD
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hG
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, _, _, hfacts⟩ := hH
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hfacts⟩ := hI
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, hfacts⟩ := hJ
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem neReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (neReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    neReifPropWith_run_prune p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with
    ⟨hrt, hE | hF⟩ | ⟨hrf, hA | hB | hC | hD⟩ | ⟨hnone, hG | hH | hI | hJ⟩
  · obtain ⟨x, hfi, hfj, hm, hfacts⟩ := hE
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_neLit]
      exact DomC.evalLit_posNe_none_of_mem hfj
        (DomC.memIntView_eq_mem_int hm)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨y, hfj, hfi, hm, hfacts⟩ := hF
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_neLit]
      exact DomC.evalLit_posNe_none_of_mem hfi
        (DomC.memIntView_eq_mem_int hm)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · obtain ⟨hconf, hconf2, hiu, hfacts⟩ := hA
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨hconf, hconf2, hiu, hjl, hfacts⟩ := hB
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨hconf, hconf2, hiu, hjl, hil, hfacts⟩ := hC
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_negLe_none hloi hhii (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨hconf, hconf2, hiu, hjl, hil, hju, hfacts⟩ := hD
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact evalLit_posLe_none hloj hhij (by omega) (by omega)
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with (rfl | rfl) | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFr hrf
  · obtain ⟨x, y, hfi, hfj, hxy, hfacts⟩ := hG
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
  · obtain ⟨x, y, hfi, hfj, hxy, hfacts⟩ := hH
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFj hfj
  · obtain ⟨h1, hfacts⟩ := hI
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
      · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
  · obtain ⟨h1, h2, hfacts⟩ := hJ
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)

theorem neReifPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (neReifPropWith p T i j r hmem).run view = .fix := by
  unfold neReifPropWith
  dsimp only
  rw [hi]

theorem neReifPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (neReifPropWith p T i j r hmem).run view = .fix := by
  unfold neReifPropWith
  dsimp only
  rw [hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl


end LeanFzn.Engine
