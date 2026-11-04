/-
Purpose: Order propagators: reifiedreasons definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Order.Bridge
DAG: LeanFzn.Engine.Props.Order.Bridge -> LeanFzn.Engine.Props.Order.ReifiedReasons.
-/
import LeanFzn.Engine.Props.Order.Bridge

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Reified comparisons -/

/-- Semantic content of a reified relation under the guard literal `g`:
every accepted assignment on which `g` is not true reads integer slots
`i`, `j` in the relation.  The guard is the literal that is false in the
view when the reification variable is fixed to the value that activates
the relation. -/
def GuardSem (p : CompiledProblem DomConstraint) (g : Literal)
    (rel : Int → Int → Prop) (i j : Nat) : Prop :=
  ∀ a, a ∈ allAssigns p.domains → accepts p a = true → g.eval a ≠ some true →
    ∃ xi xj, slotInt a i = some xi ∧ slotInt a j = some xj ∧ rel xi xj

/-- `neLit` for a Boolean is true exactly when the slot carries the
opposite Boolean. -/
theorem neLit_bool_eval_true_iff {a : Assignment} {s : Nat} {rb b : Bool}
    (ha : a[s]? = some (.bool rb)) :
    (neLit s (.bool b)).eval a = some true ↔ rb = !b := by
  cases rb <;> cases b <;> simp [neLit, posBool, Literal.eval, Atom.eval, ha]

/-- `neLit` for an integer at an integer slot reading `x`. -/
theorem neLit_int_eval_true_iff {a : Assignment} {s : Nat} {c x : Int}
    (hx : slotInt a s = some x) :
    (neLit s (.int c)).eval a = some true ↔ x ≠ c := by
  rw [show neLit s (.int c) = posNe s c from rfl, eval_posNe_iff]
  constructor
  · rintro ⟨y, hy, hyc⟩ hxc
    have hxy : y = x := (Option.some.inj (by rw [hx] at hy; exact hy)).symm
    exact hyc (hxy.trans hxc)
  · intro hne
    exact ⟨x, hx, hne⟩

/-- `eqLit` for an integer at an integer slot reading `x`. -/
theorem eqLit_int_eval_true_iff {a : Assignment} {s : Nat} {c x : Int}
    (hx : slotInt a s = some x) :
    (eqLit s (.int c)).eval a = some true ↔ x = c := by
  change (negNe s c).eval a = some true ↔ x = c
  rw [eval_negNe_iff]
  constructor
  · rintro ⟨y, hy, hyc⟩
    have hxy : y = x := (Option.some.inj (by rw [hx] at hy; exact hy)).symm
    exact hxy.symm.trans hyc
  · intro hxc
    exact ⟨x, hx, hxc⟩

/-- The `neLit` Boolean guard is true exactly when the reification slot
carries the opposite of its target Boolean. -/
theorem leReif_true_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool true)) (fun a b => a ≤ b) i j := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.leReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = true := by
    cases rb with
    | false =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := true) hr).mpr rfl
    | true => rfl
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hiff.mp hrb⟩

theorem leReif_false_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool false)) (fun a b => a < b) j i := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.leReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = false := by
    cases rb with
    | false => rfl
    | true =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := false) hr).mpr rfl
  have hnot : ¬ xi ≤ xj := by
    intro hle
    have htrue : rb = true := hiff.mpr hle
    rw [hrb] at htrue
    cases htrue
  exact ⟨xj, xi, by simp [slotInt, hxj, Value.intView],
    by simp [slotInt, hxi, Value.intView], by omega⟩

theorem eqReif_true_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool true)) (fun a b => a = b) i j := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.eqReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = true := by
    cases rb with
    | false =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := true) hr).mpr rfl
    | true => rfl
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hiff.mp hrb⟩

theorem eqReif_false_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.eqReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool false)) (fun a b => a ≠ b) i j := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.eqReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = false := by
    cases rb with
    | false => rfl
    | true =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := false) hr).mpr rfl
  have hnot : ¬ xi = xj := by
    intro heq
    have htrue : rb = true := hiff.mpr heq
    rw [hrb] at htrue
    cases htrue
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hnot⟩

theorem neReif_true_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool true)) (fun a b => a ≠ b) i j := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.neReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = true := by
    cases rb with
    | false =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := true) hr).mpr rfl
    | true => rfl
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], hiff.mp hrb⟩

theorem neReif_false_sem (p : CompiledProblem DomConstraint) (i j r : Nat)
    (hmem : DomConstraint.neReifSlot i j r ∈ p.constraints) :
    GuardSem p (neLit r (.bool false)) (fun a b => a = b) i j := by
  intro a _ha hacc hg
  have hdc : (DomConstraint.neReifSlot i j r).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨xi, xj, rb, hxi, hxj, hr, hiff⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hdc
  have hrb : rb = false := by
    cases rb with
    | false => rfl
    | true =>
        exfalso
        apply hg
        exact (neLit_bool_eval_true_iff (b := false) hr).mpr rfl
  have hnot : ¬ xi ≠ xj := by
    intro hne
    have htrue : rb = true := hiff.mpr hne
    rw [hrb] at htrue
    cases htrue
  exact ⟨xi, xj, by simp [slotInt, hxi, Value.intView],
    by simp [slotInt, hxj, Value.intView], Classical.not_not.mp hnot⟩

/-! ### Guarded reason clauses for `leReif` -/

theorem leReif_true_conflict_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loi hij : Int}
    (hsem : GuardSem p g (fun a b => a ≤ b) i j) (hconf : hij < loi) :
    Entailed p ([posLe i (loi - 1), negLe j hij] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ loi - 1
    · exact ⟨posLe i (loi - 1), by simp,
        (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

theorem leReif_true_iUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hij : Int}
    (hsem : GuardSem p g (fun a b => a ≤ b) i j) :
    Entailed p ([posLe i hij, negLe j hij] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ hij
    · exact ⟨posLe i hij, by simp,
        (eval_posLe_iff a i hij).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

theorem leReif_true_jLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loi : Int}
    (hsem : GuardSem p g (fun a b => a ≤ b) i j) :
    Entailed p ([negLe j (loi - 1), posLe i (loi - 1)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a ha hacc hg
    by_cases h : loi - 1 < xj
    · exact ⟨negLe j (loi - 1), by simp,
        (eval_negLe_iff a j (loi - 1)).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨posLe i (loi - 1), by simp,
        (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, by omega⟩⟩

theorem leReif_false_conflict_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loj hii : Int}
    (hsem : GuardSem p g (fun a b => a < b) j i) (hconf : hii ≤ loj) :
    Entailed p ([posLe j (loj - 1), negLe i hii] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xj, xi, hxj, hxi, hlt⟩ := hsem a ha hacc hg
    by_cases h : xj ≤ loj - 1
    · exact ⟨posLe j (loj - 1), by simp,
        (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

theorem leReif_false_jUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hii : Int}
    (hsem : GuardSem p g (fun a b => a < b) j i) :
    Entailed p ([posLe j (hii - 1), negLe i hii] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xj, xi, hxj, hxi, hlt⟩ := hsem a ha hacc hg
    by_cases h : xj ≤ hii - 1
    · exact ⟨posLe j (hii - 1), by simp,
        (eval_posLe_iff a j (hii - 1)).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

theorem leReif_false_iLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loj : Int}
    (hsem : GuardSem p g (fun a b => a < b) j i) :
    Entailed p ([negLe i loj, posLe j (loj - 1)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xj, xi, hxj, hxi, hlt⟩ := hsem a ha hacc hg
    by_cases h : loj < xi
    · exact ⟨negLe i loj, by simp,
        (eval_negLe_iff a i loj).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨posLe j (loj - 1), by simp,
        (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, by omega⟩⟩

theorem leReif_rTrue_reason_entailed {p : CompiledProblem DomConstraint}
    {i j r : Nat} {hii : Int}
    (hsem : GuardSem p (neLit r (.bool false)) (fun a b => a < b) j i) :
    Entailed p [posBool r true, negLe i hii, posLe j (hii - 1)] := by
  intro a ha hacc
  by_cases hg : (posBool r true).eval a = some true
  · exact ⟨posBool r true, by simp, hg⟩
  · obtain ⟨xj, xi, hxj, hxi, hlt⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ hii
    · exact ⟨posLe j (hii - 1), by simp,
        (eval_posLe_iff a j (hii - 1)).mpr ⟨xj, hxj, by omega⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

theorem leReif_rFalse_reason_entailed {p : CompiledProblem DomConstraint}
    {i j r : Nat} {hij : Int}
    (hsem : GuardSem p (neLit r (.bool true)) (fun a b => a ≤ b) i j) :
    Entailed p [posBool r false, posLe i hij, negLe j hij] := by
  intro a ha hacc
  by_cases hg : (posBool r false).eval a = some true
  · exact ⟨posBool r false, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hle⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ hij
    · exact ⟨posLe i hij, by simp,
        (eval_posLe_iff a i hij).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

/-- Reified `x_i ≤ x_j`: when `r` is true propagate `le`, when false
propagate `x_j < x_i`, and when the intervals decide the relation prune
`r` accordingly. -/
def leReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i j r : Nat) (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) :
    PropV2 p T :=
  let htrue := leReif_true_sem p i j r hmem
  let hfalse := leReif_false_sem p i j r hmem
  { vars := (dcSlotsFull (DomConstraint.leReifSlot i j r)).toArray
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
                  (leReif_true_conflict_reason_entailed htrue hconf))
              else if _hiu : hii > hij then
                .prune #[(pLit (posLe i hij), EClause.ofLiterals p T
                  ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])
                  (leReif_true_iUpper_reason_entailed htrue))]
              else if _hjl : loj < loi then
                .prune #[(pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                  ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)])
                  (leReif_true_jLower_reason_entailed htrue))]
              else .fix
          | some (.bool false) =>
              if hconf : hii ≤ loj then
                .conflict (EClause.ofLiterals p T
                  ([posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)])
                  (leReif_false_conflict_reason_entailed hfalse hconf))
              else if _hju : hij ≥ hii then
                .prune #[(pLit (posLe j (hii - 1)), EClause.ofLiterals p T
                  ([posLe j (hii - 1), negLe i hii] ++ [neLit r (.bool false)])
                  (leReif_false_jUpper_reason_entailed hfalse))]
              else if _hil : loi ≤ loj then
                .prune #[(pLit (negLe i loj), EClause.ofLiterals p T
                  ([negLe i loj, posLe j (loj - 1)] ++ [neLit r (.bool false)])
                  (leReif_false_iLower_reason_entailed hfalse))]
              else .fix
          | some (.int _) => .fix
          | some (.setOfInt _) => .fix
          | some (.array _) => .fix
          | none =>
              if hle : hii ≤ loj then
                .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                  [posBool r true, negLe i hii, posLe j (hii - 1)]
                  (leReif_rTrue_reason_entailed hfalse))]
              else if hconf : hij < loi then
                .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                  [posBool r false, posLe i hij, negLe j hij]
                  (leReif_rFalse_reason_entailed htrue))]
              else .fix
      | _, _ => .fix }

theorem leReifPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          hij < loi ∧
          T.decodeClause ec.lits =
            [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)] ∧
          Entailed p ([posLe i (loi - 1), negLe j hij] ++
            [neLit r (.bool true)])) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          hii ≤ loj ∧
          T.decodeClause ec.lits =
            [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)] ∧
          Entailed p ([posLe j (loj - 1), negLe i hii] ++
            [neLit r (.bool false)]))) := by
  unfold leReifPropWith at h
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
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, Or.inl
          ⟨hrt, hconf, ?_, leReif_true_conflict_reason_entailed
            (leReif_true_sem p i j r hmem) hconf⟩⟩
        change T.decodeClause
          (([posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)]).toArray.map pLit) =
          [posLe i (loi - 1), negLe j hij] ++ [neLit r (.bool true)]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hconf] at h
        by_cases hiu : hii > hij
        · rw [dif_pos hiu] at h
          cases h
        · rw [dif_neg hiu] at h
          by_cases hjl : loj < loi
          · rw [dif_pos hjl] at h
            cases h
          · rw [dif_neg hjl] at h
            cases h
    · rename_i hrf
      by_cases hconf : hii ≤ loj
      · rw [dif_pos hconf] at h
        injection h with hec
        subst hec
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, Or.inr
          ⟨hrf, hconf, ?_, leReif_false_conflict_reason_entailed
            (leReif_false_sem p i j r hmem) hconf⟩⟩
        change T.decodeClause
          (([posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)]).toArray.map pLit) =
          [posLe j (loj - 1), negLe i hii] ++ [neLit r (.bool false)]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hconf] at h
        by_cases hju : hij ≥ hii
        · rw [dif_pos hju] at h
          cases h
        · rw [dif_neg hju] at h
          by_cases hil : loi ≤ loj
          · rw [dif_pos hil] at h
            cases h
          · rw [dif_neg hil] at h
            cases h
    · cases h
    · cases h
    · cases h
    · by_cases hle : hii ≤ loj
      · rw [dif_pos hle] at h
        cases h
      · rw [dif_neg hle] at h
        by_cases hconf : hij < loi
        · rw [dif_pos hconf] at h
          cases h
        · rw [dif_neg hconf] at h
          cases h
  · cases h

/-- A batch consists of one literal with a fixed reason clause. -/
def PruneFacts (p : CompiledProblem DomConstraint) (T : LitTable)
    (ps : Array (PLit × EClause p T)) (lit : Literal) (reason : List Literal) : Prop :=
  ∀ q ∈ ps.toList,
    q.1.lit = lit ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason

theorem leReifPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leReifPropWith p T i j r hmem).run view = .prune ps) :
    ∃ loi hii loj hij,
      (view.doms.getD i DomC.empty).lo? = some loi ∧
      (view.doms.getD i DomC.empty).hi? = some hii ∧
      (view.doms.getD j DomC.empty).lo? = some loj ∧
      (view.doms.getD j DomC.empty).hi? = some hij ∧
      (((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ((¬ hij < loi ∧ hii > hij ∧ PruneFacts p T ps (posLe i hij)
              ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])) ∨
            (¬ hij < loi ∧ ¬ hii > hij ∧ loj < loi ∧
              PruneFacts p T ps (negLe j (loi - 1))
              ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          ((¬ hii ≤ loj ∧ hij ≥ hii ∧ PruneFacts p T ps (posLe j (hii - 1))
              ([posLe j (hii - 1), negLe i hii] ++ [neLit r (.bool false)])) ∨
            (¬ hii ≤ loj ∧ ¬ hij ≥ hii ∧ loi ≤ loj ∧
              PruneFacts p T ps (negLe i loj)
              ([negLe i loj, posLe j (loj - 1)] ++ [neLit r (.bool false)])))) ∨
        ((view.doms.getD r DomC.empty).fixedValue = none ∧
          ((hii ≤ loj ∧ PruneFacts p T ps (posBool r true)
              [posBool r true, negLe i hii, posLe j (hii - 1)]) ∨
            (¬ hii ≤ loj ∧ hij < loi ∧ PruneFacts p T ps (posBool r false)
              [posBool r false, posLe i hij, negLe j hij])))) := by
  unfold leReifPropWith at h
  dsimp only at h
  split at h
  · rename_i _x1 _x2 loi hii loj hij hbi hbj
    obtain ⟨hloi, hhii⟩ := domBounds_spec hbi
    obtain ⟨hloj, hhij⟩ := domBounds_spec hbj
    split at h
    · rename_i hrt
      by_cases hconf : hij < loi
      · rw [dif_pos hconf] at h
        cases h
      · rw [dif_neg hconf] at h
        by_cases hiu : hii > hij
        · rw [dif_pos hiu] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inl ⟨hrt, Or.inl ⟨hconf, hiu, ?_⟩⟩⟩
          intro q hq
          have hq' : q = (pLit (posLe i hij), EClause.ofLiterals p T
              ([posLe i hij, negLe j hij] ++ [neLit r (.bool true)])
              (leReif_true_iUpper_reason_entailed (leReif_true_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            leReif_true_iUpper_reason_entailed (leReif_true_sem p i j r hmem)⟩
          change T.decodeClause
            (([posLe i hij, negLe j hij] ++ [neLit r (.bool true)]).toArray.map pLit) =
            [posLe i hij, negLe j hij] ++ [neLit r (.bool true)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hiu] at h
          by_cases hjl : loj < loi
          · rw [dif_pos hjl] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inl ⟨hrt, Or.inr ⟨hconf, hiu, hjl, ?_⟩⟩⟩
            intro q hq
            have hq' : q = (pLit (negLe j (loi - 1)), EClause.ofLiterals p T
                ([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)])
                (leReif_true_jLower_reason_entailed (leReif_true_sem p i j r hmem))) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              leReif_true_jLower_reason_entailed (leReif_true_sem p i j r hmem)⟩
            change T.decodeClause
              (([negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)]).toArray.map pLit) =
              [negLe j (loi - 1), posLe i (loi - 1)] ++ [neLit r (.bool true)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hjl] at h
            cases h
    · rename_i hrf
      by_cases hconf : hii ≤ loj
      · rw [dif_pos hconf] at h
        cases h
      · rw [dif_neg hconf] at h
        by_cases hju : hij ≥ hii
        · rw [dif_pos hju] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inl ⟨hrf, Or.inl ⟨hconf, hju, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (posLe j (hii - 1)), EClause.ofLiterals p T
              ([posLe j (hii - 1), negLe i hii] ++ [neLit r (.bool false)])
              (leReif_false_jUpper_reason_entailed (leReif_false_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            leReif_false_jUpper_reason_entailed (leReif_false_sem p i j r hmem)⟩
          change T.decodeClause
            (([posLe j (hii - 1), negLe i hii] ++ [neLit r (.bool false)]).toArray.map pLit) =
            [posLe j (hii - 1), negLe i hii] ++ [neLit r (.bool false)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hju] at h
          by_cases hil : loi ≤ loj
          · rw [dif_pos hil] at h
            injection h with hec
            subst hec
            refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
              Or.inr (Or.inl ⟨hrf, Or.inr ⟨hconf, hju, hil, ?_⟩⟩)⟩
            intro q hq
            have hq' : q = (pLit (negLe i loj), EClause.ofLiterals p T
                ([negLe i loj, posLe j (loj - 1)] ++ [neLit r (.bool false)])
                (leReif_false_iLower_reason_entailed (leReif_false_sem p i j r hmem))) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_,
              leReif_false_iLower_reason_entailed (leReif_false_sem p i j r hmem)⟩
            change T.decodeClause
              (([negLe i loj, posLe j (loj - 1)] ++ [neLit r (.bool false)]).toArray.map pLit) =
              [negLe i loj, posLe j (loj - 1)] ++ [neLit r (.bool false)]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hil] at h
            cases h
    · cases h
    · cases h
    · cases h
    · rename_i hnone
      by_cases hle : hii ≤ loj
      · rw [dif_pos hle] at h
        injection h with hec
        subst hec
        refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
          Or.inr (Or.inr ⟨hnone, Or.inl ⟨hle, ?_⟩⟩)⟩
        intro q hq
        have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
            [posBool r true, negLe i hii, posLe j (hii - 1)]
            (leReif_rTrue_reason_entailed (leReif_false_sem p i j r hmem))) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_,
          leReif_rTrue_reason_entailed (leReif_false_sem p i j r hmem)⟩
        change T.decodeClause
          ([posBool r true, negLe i hii, posLe j (hii - 1)].toArray.map pLit) =
          [posBool r true, negLe i hii, posLe j (hii - 1)]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hle] at h
        by_cases hconf : hij < loi
        · rw [dif_pos hconf] at h
          injection h with hec
          subst hec
          refine ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij,
            Or.inr (Or.inr ⟨hnone, Or.inr ⟨hle, hconf, ?_⟩⟩)⟩
          intro q hq
          have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
              [posBool r false, posLe i hij, negLe j hij]
              (leReif_rFalse_reason_entailed (leReif_true_sem p i j r hmem))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            leReif_rFalse_reason_entailed (leReif_true_sem p i j r hmem)⟩
          change T.decodeClause
            ([posBool r false, posLe i hij, negLe j hij].toArray.map pLit) =
            [posBool r false, posLe i hij, negLe j hij]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hconf] at h
          cases h
  · cases h

theorem leReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (leReifPropWith p T i j r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    leReifPropWith_run_conflict p T i j r hmem view h
  rcases hbranch with ⟨_, _, hdec, hent⟩ | ⟨_, _, hdec, hent⟩
  · rwa [hdec]
  · rwa [hdec]

theorem leReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ec : EClause p T}
    (h : (leReifPropWith p T i j r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    leReifPropWith_run_conflict p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hrt, hconf, hdec, _hent⟩ | ⟨hrf, hconf, hdec, _hent⟩
  · rw [hdec]
    intro l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl) | rfl
    · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
    · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFr hrt
  · rw [hdec]
    intro l hl
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl) | rfl
    · exact evalLit_posLe_false_of_lo_gt hloj hhij (by omega) (by omega)
    · exact evalLit_negLe_false_of_hi_le hloi hhii (by omega) (by omega)
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFr hrf

theorem leReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (leReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, _, _, _, _, _, hbranch⟩ :=
    leReifPropWith_run_prune p T i j r hmem view h
  rcases hbranch with ⟨_, hA | hB⟩ | ⟨_, hC | hD⟩ | ⟨_, hE | hF⟩
  · obtain ⟨_, _, hfacts⟩ := hA
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, hfacts⟩ := hB
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, hfacts⟩ := hC
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, _, hfacts⟩ := hD
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hfacts⟩ := hE
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, _, hfacts⟩ := hF
    obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem leReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (leReifPropWith p T i j r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨loi, hii, loj, hij, hloi, hhii, hloj, hhij, hbranch⟩ :=
    leReifPropWith_run_prune p T i j r hmem view h
  have hlei : loi ≤ hii :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hloi hhii
  have hlej : loj ≤ hij :=
    DomC.lo?_le_hi? (view.doms.getD j DomC.empty) hWFj hloj hhij
  rcases hbranch with ⟨hrt, hA | hB⟩ | ⟨hrf, hC | hD⟩ | ⟨hnone, hE | hF⟩
  · obtain ⟨hconf, hiu, hfacts⟩ := hA
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
  · obtain ⟨hconf, hiu, hjl, hfacts⟩ := hB
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
  · obtain ⟨hconf, hju, hfacts⟩ := hC
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
  · obtain ⟨hconf, hju, hil, hfacts⟩ := hD
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
  · obtain ⟨hle, hfacts⟩ := hE
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
  · obtain ⟨hle, hconf, hfacts⟩ := hF
    obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit]
      exact DomC.evalLit_posBool_none_of_not_fixed hnone
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd hlit.symm hne
      · exact evalLit_posLe_false_of_lo_gt hloi hhii (by omega) (by omega)
      · exact evalLit_negLe_false_of_hi_le hloj hhij (by omega) (by omega)

theorem leReifPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (leReifPropWith p T i j r hmem).run view = .fix := by
  unfold leReifPropWith
  dsimp only
  rw [hi]

theorem leReifPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i j r : Nat)
    (hmem : DomConstraint.leReifSlot i j r ∈ p.constraints) (view : EngineView)
    (hj : domBounds (view.doms.getD j DomC.empty) = none) :
    (leReifPropWith p T i j r hmem).run view = .fix := by
  unfold leReifPropWith
  dsimp only
  rw [hj]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl

/-! ### Reified equality: semantic reason clauses -/

/-- Decompose an integer view into the carried value. -/
theorem slotInt_eq_some_exists {a : Assignment} {s : Nat} {x : Int}
    (h : slotInt a s = some x) :
    ∃ w, a[s]? = some w ∧ Value.intView w = some x := by
  unfold slotInt at h
  cases hs : a[s]? with
  | none => simp [hs] at h
  | some w =>
      simp only [hs, Option.bind_some] at h
      exact ⟨w, rfl, h⟩

/-- A negative integer disequality evaluates to `false` exactly on the
removed integer. -/
theorem neLit_int_eval_false_iff {a : Assignment} {s : Nat} {c x : Int}
    (hx : slotInt a s = some x) :
    (neLit s (.int c)).eval a = some false ↔ x = c := by
  rw [show neLit s (.int c) = posNe s c from rfl, eval_posNe, hx]
  simp only [Option.map_some, Option.some.injEq]
  rw [decide_eq_false_iff_not]
  exact Classical.not_not

/-- The equality-guarded conflict clause for disjoint intervals, lower
side. -/
theorem eqReif_true_conflict_ij_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loi hij : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) (hconf : hij < loi) :
    Entailed p ([posLe i (loi - 1), negLe j hij] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ loi - 1
    · exact ⟨posLe i (loi - 1), by simp,
        (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

/-- The equality-guarded conflict clause for disjoint intervals, upper
side. -/
theorem eqReif_true_conflict_ji_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loj hii : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) (hconf : hii < loj) :
    Entailed p ([posLe j (loj - 1), negLe i hii] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xj ≤ loj - 1
    · exact ⟨posLe j (loj - 1), by simp,
        (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

/-- Equality-guarded upper bound on the left slot. -/
theorem eqReif_true_iUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hij : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) :
    Entailed p ([posLe i hij, negLe j hij] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ hij
    · exact ⟨posLe i hij, by simp,
        (eval_posLe_iff a i hij).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

/-- Equality-guarded lower bound on the right slot. -/
theorem eqReif_true_jLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loi : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) :
    Entailed p ([negLe j (loi - 1), posLe i (loi - 1)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : loi - 1 < xj
    · exact ⟨negLe j (loi - 1), by simp,
        (eval_negLe_iff a j (loi - 1)).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨posLe i (loi - 1), by simp,
        (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, by omega⟩⟩

/-- Equality-guarded lower bound on the left slot. -/
theorem eqReif_true_iLower_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {loj : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) :
    Entailed p ([negLe i (loj - 1), posLe j (loj - 1)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : loj - 1 < xi
    · exact ⟨negLe i (loj - 1), by simp,
        (eval_negLe_iff a i (loj - 1)).mpr ⟨xi, hxi, h⟩⟩
    · exact ⟨posLe j (loj - 1), by simp,
        (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, by omega⟩⟩

/-- Equality-guarded upper bound on the right slot. -/
theorem eqReif_true_jUpper_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hii : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) :
    Entailed p ([posLe j hii, negLe i hii] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xj ≤ hii
    · exact ⟨posLe j hii, by simp,
        (eval_posLe_iff a j hii).mpr ⟨xj, hxj, h⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

/-- Equality-guarded disjointness: the intervals force `x_i < x_j`. -/
theorem eqReif_disjoint_ij_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hii loj : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) (hconf : hii < loj) :
    Entailed p [g, negLe i hii, posLe j (loj - 1)] := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xi ≤ hii
    · exact ⟨posLe j (loj - 1), by simp,
        (eval_posLe_iff a j (loj - 1)).mpr ⟨xj, hxj, by omega⟩⟩
    · exact ⟨negLe i hii, by simp,
        (eval_negLe_iff a i hii).mpr ⟨xi, hxi, by omega⟩⟩

/-- Equality-guarded disjointness: the intervals force `x_j < x_i`. -/
theorem eqReif_disjoint_ji_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {hij loi : Int}
    (hsem : GuardSem p g (fun a b => a = b) i j) (hconf : hij < loi) :
    Entailed p [g, negLe j hij, posLe i (loi - 1)] := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, heq⟩ := hsem a ha hacc hg
    by_cases h : xj ≤ hij
    · exact ⟨posLe i (loi - 1), by simp,
        (eval_posLe_iff a i (loi - 1)).mpr ⟨xi, hxi, by omega⟩⟩
    · exact ⟨negLe j hij, by simp,
        (eval_negLe_iff a j hij).mpr ⟨xj, hxj, by omega⟩⟩

/-! ### Reified disequality: semantic reason clauses -/

/-- Disequality-guarded conflict at two fixed equal integers. -/
theorem eqReif_false_conflict_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {x y : Int}
    (hsem : GuardSem p g (fun a b => a ≠ b) i j) (hxy : x = y) :
    Entailed p ([neLit i (.int x), neLit j (.int y)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hne⟩ := hsem a ha hacc hg
    by_cases hi : (neLit i (.int x)).eval a = some true
    · exact ⟨neLit i (.int x), by simp, hi⟩
    · by_cases hj : (neLit j (.int y)).eval a = some true
      · exact ⟨neLit j (.int y), by simp, hj⟩
      · exfalso
        have hxi' : xi = x := by
          apply Classical.byContradiction
          intro hne'
          exact hi ((neLit_int_eval_true_iff hxi).mpr hne')
        have hxj' : xj = y := by
          apply Classical.byContradiction
          intro hne'
          exact hj ((neLit_int_eval_true_iff hxj).mpr hne')
        exact hne (by rw [hxi', hxj', hxy])

/-- Disequality-guarded prune of the right slot at a fixed left value. -/
theorem eqReif_false_prune_j_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {x : Int}
    (hsem : GuardSem p g (fun a b => a ≠ b) i j) :
    Entailed p ([neLit i (.int x), neLit j (.int x)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hne⟩ := hsem a ha hacc hg
    by_cases hi : (neLit i (.int x)).eval a = some true
    · exact ⟨neLit i (.int x), by simp, hi⟩
    · by_cases hj : (neLit j (.int x)).eval a = some true
      · exact ⟨neLit j (.int x), by simp, hj⟩
      · exfalso
        have hxi' : xi = x := by
          apply Classical.byContradiction
          intro hne'
          exact hi ((neLit_int_eval_true_iff hxi).mpr hne')
        have hxj' : xj = x := by
          apply Classical.byContradiction
          intro hne'
          exact hj ((neLit_int_eval_true_iff hxj).mpr hne')
        exact hne (by rw [hxi', hxj'])

/-- Disequality-guarded prune of the left slot at a fixed right value. -/
theorem eqReif_false_prune_i_reason_entailed {p : CompiledProblem DomConstraint}
    {i j : Nat} {g : Literal} {y : Int}
    (hsem : GuardSem p g (fun a b => a ≠ b) i j) :
    Entailed p ([neLit i (.int y), neLit j (.int y)] ++ [g]) := by
  intro a ha hacc
  by_cases hg : g.eval a = some true
  · exact ⟨g, by simp, hg⟩
  · obtain ⟨xi, xj, hxi, hxj, hne⟩ := hsem a ha hacc hg
    by_cases hi : (neLit i (.int y)).eval a = some true
    · exact ⟨neLit i (.int y), by simp, hi⟩
    · by_cases hj : (neLit j (.int y)).eval a = some true
      · exact ⟨neLit j (.int y), by simp, hj⟩
      · exfalso
        have hxi' : xi = y := by
          apply Classical.byContradiction
          intro hne'
          exact hi ((neLit_int_eval_true_iff hxi).mpr hne')
        have hxj' : xj = y := by
          apply Classical.byContradiction
          intro hne'
          exact hj ((neLit_int_eval_true_iff hxj).mpr hne')
        exact hne (by rw [hxi', hxj'])


end LeanFzn.Engine
