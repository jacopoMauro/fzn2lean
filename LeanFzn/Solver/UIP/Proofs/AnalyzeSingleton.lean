/-
File: LeanFzn/Solver/UIP/Proofs/AnalyzeSingleton.lean
analysis has no below-level tail)

Purpose: the N1 analyzer fact. A UNIT conflict clause analyzed by
`analyzeAtAllowance` can only mark a falfisier at the CURRENT level: the
root-level and below-level `markLit` outcomes leave the mark set empty,
and `nextPivot` on the empty mark set returns `none`, so those runs die
before producing a result. Consequently the analyzed `below` list is
ALWAYS empty for a singleton input — the learned analysis clause is
exactly `[uip.negate]`, the shape N1's unit profile needs (together with
`supported_conflict_clause_unit`, which supplies the singleton clause).

  §1 `nextPivot_nil` / the empty-state helpers;
  §2 `markLit_empty_marks_case` — the inversion of `markLit` at the empty
     state that survives a `some` result;
  §3 `analyzeAtAllowance_singleton_below` — the main theorem, with the
     Boolean regression example.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.AnalyzeSingleton` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.Propagation.AnalysisInvariants
import LeanFzn.Solver.Propagation.AnalysisCompletion
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Empty-state helpers -/

/-- `nextPivot` on the empty mark set finds nothing. -/
theorem nextPivot_nil (trail : List TrailEntry) : nextPivot trail [] = none := by
  unfold nextPivot
  simp

/-- The empty worklist with no marks cannot produce a result (any learnt
list). -/
theorem analyzeStep_emptyMarks_none (trail : List TrailEntry) (lvl : Nat) :
    ∀ (fuel : Nat) (l : List (Literal × Nat)),
      analyzeStep trail lvl fuel [] none [] l = none := by
  intro fuel
  cases fuel with
  | zero => intro l; rfl
  | succ k => intro l; simp only [analyzeStep, nextPivot_nil]

/-- The empty singleton clause `[[]]` with no marks cannot produce a result
(any learnt list): the empty clause drops and the empty worklist dies
through `nextPivot_nil`. -/
theorem analyzeStep_singletonNil_emptyMarks_none (trail : List TrailEntry)
    (lvl : Nat) :
    ∀ (fuel : Nat) (l : List (Literal × Nat)),
      analyzeStep trail lvl fuel [[]] none [] l = none := by
  intro fuel
  cases fuel with
  | zero => intro l; rfl
  | succ k =>
      intro l
      cases k with
      | zero => rfl
      | succ k' => simp only [analyzeStep, nextPivot_nil]

/-! ## §2 The `markLit` outcome inversion at the empty state -/

/-- **THE MARKING INVERSION**: a `markLit` call at the empty state whose
mark set is NONEMPTY can only have taken the current-level branch — the
mark is the single entry it found, its level is the analysis level, and
the learnt list stayed empty. (The root-level, below-level and shortcut
outcomes all leave `marks = []`.) -/
theorem markLit_empty_marks_case {trail : List TrailEntry} {lvl : Nat}
    {q0 : Literal} {m : List TrailEntry} {l : List (Literal × Nat)}
    (hm : markLit trail lvl [] [] q0 = some (m, l)) (hne : m ≠ []) :
    ∃ e : TrailEntry, m = [e] ∧ e.level = lvl ∧ l = [] := by
  have h1 : ([].any fun (m : TrailEntry) =>
      litEqB m.literal (q0.norm).negate.norm) = false := rfl
  have h2 : ([].any fun (p : Literal × Nat) => litEqB p.1 (q0.norm)) = false :=
    rfl
  have hm' : markLit trail lvl [] [] q0.norm = some (m, l) := by
    unfold markLit at hm ⊢
    simp only [norm_norm] at hm ⊢
    exact hm
  cases hf : findEntryOf trail (q0.norm).negate with
  | some e =>
      rw [markLit_eq_of_lookup h1 h2 hf] at hm'
      split at hm'
      · rename_i hb
        obtain ⟨hm1, -⟩ := Prod.mk.inj (Option.some.inj hm')
        exact absurd hm1.symm hne
      · split at hm'
        · rename_i hb
          obtain ⟨hm1, hm2⟩ := Prod.mk.inj (Option.some.inj hm')
          exact ⟨e, hm1.symm, beq_iff_eq.mp hb, hm2.symm⟩
        · rename_i hb
          obtain ⟨hm1, -⟩ := Prod.mk.inj (Option.some.inj hm')
          exact absurd hm1.symm hne
  | none =>
      unfold markLit at hm
      simp only [h1, h2, hf, Bool.false_eq_true, if_false] at hm
      cases hf₂ : findEntryOf trail (orderUpgrade trail (q0.norm)).negate with
      | none =>
          simp only [hf₂] at hm
          cases hm
      | some e =>
          simp only [hf₂] at hm
          split at hm
          · rename_i hb
            obtain ⟨hm1, -⟩ := Prod.mk.inj (Option.some.inj hm)
            exact absurd hm1.symm hne
          · split at hm
            · rename_i hb
              obtain ⟨hm1, hm2⟩ := Prod.mk.inj (Option.some.inj hm)
              exact ⟨e, hm1.symm, beq_iff_eq.mp hb, hm2.symm⟩
            · rename_i hb
              obtain ⟨hm1, -⟩ := Prod.mk.inj (Option.some.inj hm)
              exact absurd hm1.symm hne

/-! ## §3 The main theorem -/

/-- **N1 `analyzeAtAllowance_singleton_below`**: a singleton conflict
clause's analysis never records a below-level falsifier — the allowance
list is empty. The mark survives only in the current-level branch, where
the final filter empties it and the learnt list is returned unchanged. -/
theorem analyzeAtAllowance_singleton_below {trail : List TrailEntry}
    {lvl : Nat} {q : Literal} {below : List (Literal × Nat)} {uip : Literal}
    (h : analyzeAtAllowance trail lvl [q] = some (below, uip)) : below = [] := by
  unfold analyzeAtAllowance at h
  suffices hgen : ∀ fuel, analyzeStep trail lvl fuel [[q]] none [] [] =
      some (below, uip) → below = [] from hgen _ h
  intro fuel
  cases fuel with
  | zero =>
      intro h
      simp only [analyzeStep] at h
      exact absurd h (by simp)
  | succ f₁ =>
      cases f₁ with
      | zero =>
          intro h
          simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
          cases hm0 : markLit trail lvl [] [] q.norm <;> simp_all
      | succ f₂ =>
          cases f₂ with
          | zero =>
              intro h
              simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
              cases hm0 : markLit trail lvl [] [] q.norm <;> simp_all
          | succ f₃ =>
              intro h
              simp only [analyzeStep, skipEq, Bool.false_eq_true, if_false] at h
              cases hm : markLit trail lvl [] [] q.norm with
              | none =>
                  simp only [hm] at h
                  cases h
              | some p =>
                  obtain ⟨m₁, l₁⟩ := p
                  simp only [hm] at h
                  change analyzeStep trail lvl (Nat.succ f₃) [] none m₁ l₁ =
                    some (below, uip) at h
                  cases m₁ with
                  | nil =>
                      exact absurd h (by
                        rw [analyzeStep_emptyMarks_none trail lvl (Nat.succ f₃)
                          l₁]
                        simp)
                  | cons e rest =>
                      have hne : (e :: rest) ≠ [] := by simp
                      obtain ⟨e₁, heq, -, hl₁⟩ :=
                        markLit_empty_marks_case hm hne
                      injection heq with hee hrest
                      subst hrest
                      rw [hee] at h
                      rw [hl₁] at h
                      simp only [analyzeStep] at h
                      cases hnp : nextPivot trail [e₁] with
                      | none =>
                          simp only [hnp] at h
                          cases h
                      | some e₂ =>
                          obtain ⟨m, hm_mem, hm_lit⟩ :=
                            nextPivot_mark trail [e₁] e₂ hnp
                          have hme : m = e₁ := by simpa using hm_mem
                          subst hme
                          have hliteq : litEqB m.literal e₂.literal = true := by
                            rw [hm_lit]
                            exact litEqB_self e₂.literal
                          simp only [hnp, List.filter_cons, List.filter_nil,
                            hliteq, Bool.not_true, Bool.false_eq_true, if_false,
                            if_true, List.isEmpty_nil] at h
                          exact (Prod.mk.inj (Option.some.inj h)).1.symm

/-- The Boolean regression instance: a `boolEq` conflict's singleton
analysis returns the empty below-list. -/
example :
    analyzeAtAllowance
      [{ literal := posBool 0 true, level := 1, reason := none }] 1
      [posBool 0 false] = some ([], posBool 0 true) := rfl

end LeanFzn.Solver.UIP
