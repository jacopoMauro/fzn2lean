/-
Purpose: Queue soundness lemmas, separated from executable propagation.
Dependencies: LeanFzn.Engine.Proofs.Queue.Bookkeeping
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Proofs.Queue.Bookkeeping

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

set_option maxHeartbeats 4000000

theorem pushPropPrunes_reasons_entailed {st : EngineState p T}
    (h : ∀ c, c ∈ st.reasons.toList → Entailed p (T.decodeClause c.lits))
    (pending : Array Pending) (ps : Array (PLit × EClause p T)) :
    ∀ c, c ∈ (pushPropPrunes st pending ps).1.reasons.toList →
      Entailed p (T.decodeClause c.lits) := by
  unfold pushPropPrunes
  rw [← Array.foldl_toList]
  induction ps.toList generalizing st pending with
  | nil => intro c hc; exact h c (by simpa using hc)
  | cons pe rest ih =>
      rw [List.foldl_cons]
      dsimp only
      simp only [Bool.false_eq_true, if_false]
      apply ih
      intro c hc
      rw [canonClause_reasons, canonLit_reasons, Array.toList_push] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h c hc
      · simp only [List.mem_singleton] at hc
        subst hc
        exact (canonClause (canonLit st pe.1).2 pe.2).1.ent

theorem insertPending_reasons_entailed {st : EngineState p T} (item : Pending)
    (h : ∀ c, c ∈ st.reasons.toList → Entailed p (T.decodeClause c.lits)) :
    ∀ c, c ∈ (insertPending st item).1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
  intro c hc
  rw [insertPending_reasons] at hc
  exact h c hc

theorem drain_reasons_entailed {st : EngineState p T}
    (h : ∀ c, c ∈ st.reasons.toList → Entailed p (T.decodeClause c.lits))
    (pending : Array Pending) (f : Nat) :
    ∀ c, c ∈ (drain p T st pending f).st.reasons.toList →
      Entailed p (T.decodeClause c.lits) := by
  revert h
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      intro h
      simpa [drain] using h
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      simpa [drain, hback, hins] using h1
  | case3 st pending f item hback st1 neg hins =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      simpa [drain, hback, hins] using h1
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      have := ih h1
      simpa [drain, hback, hins, hf, pending1] using this
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      have h2 : ∀ c, c ∈ ({ st1 with db := db } : EngineState p T).reasons.toList →
          Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact h1 c (by simpa using hc)
      have := ih h2
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using this
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      have hrs3 : st3.reasons = st1.reasons := by
        have h := congrArg (fun x : EClause p T × EngineState p T => x.2.reasons) hcanon
        have hc2 := canonClause_reasons st2 ec1
        exact h.symm.trans (hc2.trans (by show st2.reasons = st1.reasons; rfl))
      have h3 : ∀ c, c ∈ st3.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h1 c
        rwa [hrs3] at hc
      simpa [drain, hback, hins, hprop, hcanon, hf, st2] using h3
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro h
      have hrs : st1.reasons = st.reasons := by
        simpa [hins] using insertPending_reasons (st := st) item
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        rwa [hrs] at hc
      have h2 : ∀ c, c ∈ ({ st1 with db := db } : EngineState p T).reasons.toList →
          Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact h1 c (by simpa using hc)
      have := ih h2
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using this
  | case8 st pending f hback hq id st1 hprops ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have := ih h1
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hprops, st1, id] using this
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have := ih h1
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hprops, hrun, st1, id] using this
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have hrs2 : st2.reasons = st1.reasons := by
        have h := congrArg (fun x : EClause p T × EngineState p T => x.2.reasons) hcanon
        exact h.symm.trans (canonClause_reasons st1 ec1)
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h1 c
        rwa [hrs2] at hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hprops, hrun, hcanon, st1, id] using h2
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact pushPropPrunes_reasons_entailed h1 pending ps c (by
          simpa [hpush] using hc)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, st1, id] using h2
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact pushPropPrunes_reasons_entailed h1 pending ps c (by
          simpa [hpush] using hc)
      have := ih h2
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using this
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have := ih h1
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hql, hprops, st1, id] using this
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have := ih h1
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using this
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have hrs2 : st2.reasons = st1.reasons := by
        have h := congrArg (fun x : EClause p T × EngineState p T => x.2.reasons) hcanon
        exact h.symm.trans (canonClause_reasons st1 ec1)
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h1 c
        rwa [hrs2] at hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] using h2
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact pushPropPrunes_reasons_entailed h1 pending ps c (by
          simpa [hpush] using hc)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] using h2
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : ∀ c, c ∈ st1.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        apply h c
        simpa [st1, id, setInQueue_reasons] using hc
      have h2 : ∀ c, c ∈ st2.reasons.toList → Entailed p (T.decodeClause c.lits) := by
        intro c hc
        exact pushPropPrunes_reasons_entailed h1 pending ps c (by
          simpa [hpush] using hc)
      have := ih h2
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using this
  | case18 st pending f hback hq hql =>
      intro h
      simpa [drain, hback, hq, hql] using h

theorem propagate_reasons_entailed {st : EngineState p T}
    (h : ∀ c, c ∈ st.reasons.toList → Entailed p (T.decodeClause c.lits)) (f : Nat) :
    ∀ c, c ∈ (propagate p T st f).st.reasons.toList →
      Entailed p (T.decodeClause c.lits) :=
  drain_reasons_entailed h #[] f

theorem propagate_trail {st : EngineState p T} (f : Nat) :
    st.trail.toList <+: (propagate p T st f).st.trail.toList :=
  (drain_frame st #[] f (Frame.refl st)).trail_pre

theorem propagate_db {st : EngineState p T} (f : Nat) :
    (∀ (id : Nat), (st.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) =
      ((propagate p T st f).st.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e)) ∧
    st.db.clauses.size = (propagate p T st f).st.db.clauses.size :=
  let h := drain_frame st #[] f (Frame.refl st)
  ⟨fun id => h.db_e id, h.db_size⟩

theorem drain_failed {st : EngineState p T} (pending : Array Pending) (f : Nat) :
    (drain p T st pending f).failed = true → (drain p T st pending f).conflict = none := by
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      intro h; simp [drain] at h
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro h; simp [drain, hback, hins] at h
  | case3 st pending f item hback st1 neg hins =>
      intro _; simp [drain, hback, hins]
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro h
      have h' : (drain p T st1 pending1 f).failed = true := by
        simpa [drain, hback, hins, hf, pending1] using h
      simpa [drain, hback, hins, hf, pending1] using ih h'
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro h
      have h' : (drain p T { st1 with db := db } pending1 f).failed = true := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using h
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h'
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro h; simp [drain, hback, hins, hprop, hcanon, hf, st2] at h
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro h
      have h' : (drain p T { st1 with db := db } (pushClausePrunes pending1 ps) f).failed = true := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using h
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h'
  | case8 st pending f hback hq id st1 hprops ih =>
      intro h
      have h' : (drain p T st1 pending f).failed = true := by
        simpa [drain, hback, hq, hprops, st1, id] using h
      simpa [drain, hback, hq, hprops, st1, id] using ih h'
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro h
      have h' : (drain p T st1 pending f).failed = true := by
        simpa [drain, hback, hq, hprops, hrun, st1, id] using h
      simpa [drain, hback, hq, hprops, hrun, st1, id] using ih h'
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h; simp [drain, hback, hq, hprops, hrun, hcanon, st1, id] at h
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro _; simp [drain, hback, hq, hprops, hrun, hpush, st1, id]
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h' : (drain p T st2 pend f).failed = true := by
        simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using h
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using ih h'
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro h
      have h' : (drain p T st1 pending f).failed = true := by
        simpa [drain, hback, hq, hql, hprops, st1, id] using h
      simpa [drain, hback, hq, hql, hprops, st1, id] using ih h'
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro h
      have h' : (drain p T st1 pending f).failed = true := by
        simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using h
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using ih h'
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h; simp [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] at h
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro _; simp [drain, hback, hq, hql, hprops, hrun, hpush, st1, id]
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h' : (drain p T st2 pend f).failed = true := by
        simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using h
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using ih h'
  | case18 st pending f hback hq hql =>
      intro h; simp [drain, hback, hq, hql] at h

theorem propagate_failed {st : EngineState p T} (f : Nat) :
    (propagate p T st f).failed = true → (propagate p T st f).conflict = none :=
  drain_failed #[] f

theorem drain_conflict_entailed {st : EngineState p T} (pending : Array Pending) (f : Nat)
    {c : EClause p T} (_h : (drain p T st pending f).conflict = some c) :
    Entailed p (T.decodeClause c.lits) := c.ent

theorem propagate_conflict {st : EngineState p T} (f : Nat) {c : EClause p T}
    (_h : (propagate p T st f).conflict = some c) :
    Entailed p (T.decodeClause c.lits) := c.ent

theorem pushClausePrunes_reason_resolves (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × Nat)) {item : Pending}
    (h : item ∈ (pushClausePrunes pending ps).toList)
    (hpre : item ∈ pending.toList → ∃ c, reasonClause? st item.reason = some c)
    (hdb : ∀ (l : PLit) (id : Nat), (l, id) ∈ ps.toList →
      ∃ sc : StoredClause p T, st.db.clauses[id]? = some sc) :
    ∃ c, reasonClause? st item.reason = some c := by
  rcases pushClausePrunes_mem pending ps h with hmem | ⟨l, id, hin, rfl⟩
  · exact hpre hmem
  · obtain ⟨sc, hsc⟩ := hdb l id hin
    exact ⟨sc.e, by rw [reasonClause?_learned, hsc]; rfl⟩

end LeanFzn.Engine
