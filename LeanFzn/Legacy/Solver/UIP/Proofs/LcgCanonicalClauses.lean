/-
Purpose: canonical literal/clauses and preservation through propagator clamping.
Dependencies: ClampPool proves that clamping commutes with literal normalization;
LiteralClamp supplies the exact runtime result/propagator wrappers.
DAG: literal normalization -> canonical emissions -> learned database run invariant.
LcgCanonicalFamilies supplies family emissions; scheduler database preservation is next.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.ClampPool
import LeanFzn.Legacy.Solver.UIP.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEmissionTyped

namespace LeanFzn.Solver.UIP.LcgCanonicalClauses
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP.LcgEmissionTyped
open LeanFzn.Solver.Propagation.DomainFiltering

def ClauseCanonical (c : Clause) : Prop := ∀ q ∈ c, q.norm = q
def DatabaseCanonical (db : List Clause) : Prop := ∀ c ∈ db, ClauseCanonical c

def ResCanonical : PropagationResult → Prop
  | .stable => True
  | .implied l r => l.norm = l ∧ ClauseCanonical r.clause
  | .conflict c => ClauseCanonical c

/-- A syntactic property of raw emissions, independent of assignment correctness. -/
def EmissionCanonical (props : List Propagator) : Prop :=
  ∀ p ∈ props, ∀ st, ResCanonical (p.run st)

theorem clauseCanonical_nil : ClauseCanonical [] := by
  intro q hq
  cases hq

theorem databaseCanonical_nil : DatabaseCanonical [] := by
  intro c hc
  cases hc

theorem clauseCanonical_cons {q : Literal} {c : Clause}
    (hq : q.norm = q) (hc : ClauseCanonical c) : ClauseCanonical (q :: c) := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact hq
  · exact hc l hl

theorem clauseCanonical_append {c d : Clause} (hc : ClauseCanonical c)
    (hd : ClauseCanonical d) : ClauseCanonical (c ++ d) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hc q hq
  · exact hd q hq

theorem databaseCanonical_cons {c : Clause} {db : List Clause}
    (hc : ClauseCanonical c) (hd : DatabaseCanonical db) : DatabaseCanonical (c :: db) := by
  intro d hd'
  rcases List.mem_cons.mp hd' with rfl | hd'
  · exact hc
  · exact hd d hd'

theorem databaseCanonical_append {db db' : List Clause}
    (h : DatabaseCanonical db) (h' : DatabaseCanonical db') : DatabaseCanonical (db ++ db') := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h c hc
  · exact h' c hc

theorem clauseCanonical_map_norm (c : Clause) : ClauseCanonical (c.map Literal.norm) := by
  intro q hq
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
  exact Literal.norm_idem _

theorem snapLit_canonical (orig : List Domain) {l : Literal} (h : l.norm = l) :
    (snapLit orig l).norm = snapLit orig l := by
  rw [snapLit_norm, h]

theorem snapClause_canonical (orig : List Domain) {c : Clause}
    (h : ClauseCanonical c) : ClauseCanonical (snapClause orig c) := by
  intro q hq
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
  exact snapLit_canonical orig (h l hl)

theorem snapResult_canonical (orig : List Domain) {r : PropagationResult}
    (h : ResCanonical r) : ResCanonical (snapResult orig r) := by
  cases r with
  | stable => trivial
  | implied l r => exact ⟨snapLit_canonical orig h.1, snapClause_canonical orig h.2⟩
  | conflict c => exact snapClause_canonical orig h

theorem clampProps_canonical (orig : List Domain) {raw : List Propagator}
    (h : EmissionCanonical raw) : EmissionCanonical (clampProps orig raw) := by
  intro p hp st
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  exact snapResult_canonical orig (h p0 hp0 st)

/-- Every stored normalized analysis clause has canonical literals. -/
theorem normalizedAnalysis_canonical (an : ConflictAnalysis) :
    ClauseCanonical an.normalized.learned := clauseCanonical_map_norm an.learned

/-- The actual recording site produces canonical learned clauses even after
its repeat guard filters the analysis result. -/
theorem recordedAnalysis_canonical {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {c : Clause} {an : ConflictAnalysis} (h : recordedAnalysis cfg c = some an) :
    ClauseCanonical an.learned := by
  unfold recordedAnalysis at h
  have hm := (Option.filter_eq_some_iff.mp h).1
  obtain ⟨p, _, heq⟩ := Option.map_eq_some_iff.mp hm
  subst an
  exact normalizedAnalysis_canonical _

theorem firstEvent_canonical (rs : List PropagationResult)
    (h : ∀ r ∈ rs, ResCanonical r) : ResCanonical (firstEvent rs) := by
  rcases firstEvent_mem rs _ rfl with hs | hm
  · rw [hs]
    trivial
  · exact h _ hm

theorem narrowHi_canonical (st : State) {s : Nat} {hi : Int} {ng : Clause}
    (h : ClauseCanonical ng) : ResCanonical (narrowHi st s hi ng) := by
  cases hr : narrowHi st s hi ng with
  | stable => trivial
  | implied l r =>
      obtain ⟨rfl, rfl⟩ := narrowHi_implied_inv hr
      exact ⟨rfl, h⟩
  | conflict c =>
      obtain ⟨_, _, _, _, _, rfl⟩ := narrowHi_conflict_inv hr
      exact h

theorem narrowLo_canonical (st : State) {s : Nat} {lo : Int} {ng : Clause}
    (h : ClauseCanonical ng) : ResCanonical (narrowLo st s lo ng) := by
  cases hr : narrowLo st s lo ng with
  | stable => trivial
  | implied l r =>
      obtain ⟨rfl, rfl⟩ := narrowLo_implied_inv hr
      exact ⟨rfl, h⟩
  | conflict c =>
      obtain ⟨_, _, _, _, _, rfl⟩ := narrowLo_conflict_inv hr
      exact h

/-- Boolean implications use a positive Boolean pivot, already canonical. -/
theorem implyBool_canonical (st : State) {s : Nat} {b : Bool} {ng : Clause}
    (h : ClauseCanonical ng) : ResCanonical (implyBool st s b ng) := by
  cases hr : implyBool st s b ng with
  | stable => trivial
  | implied l r =>
      obtain ⟨rfl, rfl⟩ := implyBool_implied_inv hr
      exact ⟨rfl, h⟩
  | conflict c =>
      obtain ⟨rfl, _⟩ := implyBool_conflict_inv hr
      exact h

theorem leConstHi_canonical (st : State) (s : Nat) (k : Int) :
    ResCanonical (propLeConstHi st s k) :=
  narrowHi_canonical st (by intro q hq; cases List.mem_singleton.mp hq; rfl)

theorem leConstLo_canonical (st : State) (s : Nat) (k : Int) :
    ResCanonical (propLeConstLo st s k) :=
  narrowLo_canonical st (by intro q hq; cases List.mem_singleton.mp hq; rfl)

theorem ltConstHi_canonical (st : State) (s : Nat) (k : Int) :
    ResCanonical (propLtConstHi st s k) :=
  narrowHi_canonical st (by intro q hq; cases List.mem_singleton.mp hq; rfl)

theorem ltConstLo_canonical (st : State) (s : Nat) (k : Int) :
    ResCanonical (propLtConstLo st s k) :=
  narrowLo_canonical st (by intro q hq; cases List.mem_singleton.mp hq; rfl)

/-- Normalize explicit reason templates composed of positive Boolean and integer atoms. -/
macro "canonical_clause" : tactic =>
  `(tactic| simp [ClauseCanonical, Literal.norm, posBool, posLe, negLe, posNe, negNe])

theorem boolNot_canonical (st : State) (i j : Nat) :
    ResCanonical (propBoolNot st i j) := by
  rcases propBoolNot_emit (res := propBoolNot st i j) rfl with
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [h]; trivial

theorem boolAnd_canonical (st : State) (i j k : Nat) :
    ResCanonical (propBoolAnd st i j k) := by
  rcases propBoolAnd_emit (res := propBoolAnd st i j k) rfl with
    ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [h]; trivial

theorem boolOr_canonical (st : State) (i j k : Nat) :
    ResCanonical (propBoolOr st i j k) := by
  rcases propBoolOr_emit (res := propBoolOr st i j k) rfl with
    ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [← h]; exact implyBool_canonical st (by canonical_clause)
  · rw [h]; trivial

end LeanFzn.Solver.UIP.LcgCanonicalClauses
