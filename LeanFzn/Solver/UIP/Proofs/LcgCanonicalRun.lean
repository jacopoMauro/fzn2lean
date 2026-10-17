/-
Purpose: canonical learned-database preservation through productive propagation.
Dependencies: LcgCanonicalFamilies supplies concrete emission producers;
ExtendedPoolProducers supplies exact deduction/event provenance and runtime field laws.
DAG: canonical families -> propagation database preservation -> scheduler syntax invariant.
No semantic run invariant or chronological reachability premise is assumed.
-/
import LeanFzn.Solver.UIP.Proofs.LcgCanonicalFamilies
import LeanFzn.Solver.UIP.Proofs.ExtendedPoolProducers

namespace LeanFzn.Solver.UIP.LcgCanonicalRun
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgCanonicalClauses

theorem nextPruningEvent_reason_canonical {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    (hp : EmissionCanonical props) (hdb : DatabaseCanonical bs.learned)
    {l : Literal} {c : Clause} {lr fl : Bool}
    (h : nextPruningEvent original props bs.frame bs.learned = .implied l c lr fl) :
    ClauseCanonical c := by
  rcases nextPruningEvent_implied_cases h with hsrc | ⟨_, _, hprop⟩
  · obtain ⟨hc, _, _⟩ := scanDatabase_implied_facts hsrc
    exact hdb c hc
  · obtain ⟨p, hpm, r, hrun, hcl, _, _⟩ := scanPropagators_implied_facts hprop
    have hh := hp p hpm (frameState bs.frame)
    rw [hrun] at hh
    rw [hcl]
    exact hh.2

theorem deduction_learned_canonical {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs} (hp : EmissionCanonical props)
    (hdb : DatabaseCanonical bs.learned)
    (hd : explainedDeduction original props bs = some d) : DatabaseCanonical d.learned := by
  obtain ⟨c, lr, fl, hev, _, hlearned⟩ := explainedDeduction_learned_shape hd
  have hc := nextPruningEvent_reason_canonical hp hdb hev
  rw [hlearned]
  split
  · exact databaseCanonical_cons hc databaseCanonical_nil
  · exact databaseCanonical_nil

theorem stepNarrowSync_canonical {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    {d : ProductiveDeduction leaf bs} (hp : EmissionCanonical props)
    (hdb : DatabaseCanonical bs.learned)
    (hd : explainedDeduction original props bs = some d) :
    DatabaseCanonical (stepNarrowSync orig bs d).learned := by
  rw [stepNarrowSync_learned]
  exact databaseCanonical_append (deduction_learned_canonical hp hdb hd) hdb

/-- The actual fuel-free propagation closure keeps its learned database canonical. -/
theorem closure_canonical {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator) (hp : EmissionCanonical props) :
    ∀ bs : BranchState leaf, DatabaseCanonical bs.learned →
      DatabaseCanonical (explainedClosure orig original props bs).learned := by
  suffices h : ∀ (fuel : Nat) (bs : BranchState leaf), Frame.mass bs.frame ≤ fuel →
      DatabaseCanonical bs.learned →
      DatabaseCanonical (explainedClosure orig original props bs).learned from
    fun bs => h (Frame.mass bs.frame) bs (Nat.le_refl _)
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hdb
      rw [explainedClosure]
      split
      · exact hdb
      · rename_i d _
        have := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hdb
      rw [explainedClosure]
      split
      · exact hdb
      · rename_i d hd
        have hmass : Frame.mass (stepNarrowSync orig bs d).frame ≤ fuel := by
          rw [stepNarrowSync_frame]
          have := d.decreases
          omega
        exact ih _ hmass (stepNarrowSync_canonical hp hdb hd)

theorem databaseCanonical_filter {db : List Clause} (h : DatabaseCanonical db)
    (p : Clause → Bool) : DatabaseCanonical (db.filter p) := by
  intro c hc
  exact h c (List.mem_filter.mp hc).1

theorem nextPruningEvent_conflict_canonical {leaf : Assignment → Bool}
    {original : List Clause} {props : List Propagator} {bs : BranchState leaf}
    (hp : EmissionCanonical props) (hdb : DatabaseCanonical bs.learned) {cs : List Clause}
    (h : nextPruningEvent original props bs.frame bs.learned = .conflict cs) :
    DatabaseCanonical cs := by
  rcases nextPruningEvent_conflict_cases h with hsrc | ⟨_, _, hprop⟩
  · obtain ⟨c, hc, _, rfl⟩ := scanDatabase_conflict_facts hsrc
    exact databaseCanonical_cons (hdb c hc) databaseCanonical_nil
  · obtain ⟨p, hpm, c, hrun, rfl⟩ := scanPropagators_conflict_facts hprop
    have hh := hp p hpm (frameState bs.frame)
    rw [hrun] at hh
    split
    · exact databaseCanonical_nil
    · exact databaseCanonical_cons hh databaseCanonical_nil

/-- Terminal conflict payloads are canonical whether they arise from a
stored conflict, a propagator, a rejected filter, or an empty-domain wipeout. -/
theorem terminalResult_payload_canonical {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs bs' : BranchState leaf} {cs learned : List Clause}
    (hp : EmissionCanonical props) (hdb : DatabaseCanonical bs.learned)
    (ht : terminalResult orig original props bs = .conflict bs' cs learned) :
    DatabaseCanonical learned := by
  unfold terminalResult at ht
  cases he : nextPruningEvent original props bs.frame bs.learned with
  | stable =>
      rw [he] at ht
      cases hw : wipeoutClause orig bs.trail bs.frame with
      | none => rw [hw] at ht; cases ht
      | some w => rw [hw] at ht; cases ht; exact databaseCanonical_nil
  | conflict clauses =>
      rw [he] at ht
      cases ht
      exact databaseCanonical_filter (nextPruningEvent_conflict_canonical hp hdb he) _
  | implied l c lr fl =>
      rw [he] at ht
      simp only at ht
      cases hf : filterFrame l bs.frame with
      | some g => rw [hf] at ht; cases ht
      | none =>
          rw [hf] at ht
          cases ht
          split
          · exact databaseCanonical_cons (nextPruningEvent_reason_canonical hp hdb he)
              databaseCanonical_nil
          · exact databaseCanonical_nil

/-- A restored branch keeps the current database plus the plan's globally
learned clause; checkpoint restoration does not discard global clauses. -/
theorem restoreNarrow_canonical {leaf : Assignment → Bool} {p : BackjumpPlan leaf}
    {bs restored : BranchState leaf} (hdb : DatabaseCanonical bs.learned)
    (hc : ClauseCanonical p.learned) (hr : p.restoreNarrow bs = some restored) :
    DatabaseCanonical restored.learned := by
  unfold BackjumpPlan.restoreNarrow at hr
  split at hr
  · cases hr
  · cases hr
    change DatabaseCanonical (p.learned :: bs.learned)
    exact databaseCanonical_cons hc hdb

theorem perform_canonical {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator} {p : BackjumpPlan leaf}
    {bs restored : BranchState leaf} (hp : EmissionCanonical props)
    (hdb : DatabaseCanonical bs.learned) (hc : ClauseCanonical p.learned)
    (hr : p.perform bs orig original props = some restored) :
    DatabaseCanonical restored.learned := by
  unfold BackjumpPlan.perform at hr
  obtain ⟨s, hs, hres⟩ := Option.map_eq_some_iff.mp hr
  subst hres
  apply closure_canonical orig original props hp
  rw [syncAll_learned]
  exact restoreNarrow_canonical hdb hc hs

end LeanFzn.Solver.UIP.LcgCanonicalRun
