/-
Purpose: Core-only certified linear optimization with explicit incomplete runs.
Dependencies: Engine.Search, shared generic optimization and compiler correctness.
DAG: Core search -> partial certified oracle -> generic branch-and-bound -> public driver.
The legacy solver and its unconditional completion contract are not imported.
-/
import LeanFzn.Engine.Search
import LeanFzn.Integration.Optimization.Partial
import LeanFzn.Integration.Public.Preprocess

namespace LeanFzn.Core

private theorem coreStats_est_bind_assoc {ε σ α β γ : Type} (x : EST ε σ α)
    (f : α → EST ε σ β) (g : β → EST ε σ γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g := by
  funext s
  dsimp only [Bind.bind, EST.bind]
  cases h : x s <;> rfl

private theorem coreStats_io_bind_assoc {α β γ : Type} (x : IO α) (f : α → IO β)
    (g : β → IO γ) :
    (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  coreStats_est_bind_assoc x f g

private theorem coreStats_io_pure_bind {α β : Type} (a : α) (f : α → IO β) :
    (pure a >>= f) = f a := rfl

open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

/-- A Core give-up is an incomplete optimization round. No fallback is run. -/
def coreVerdictWith (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) : CertVerdict :=
  match coreSolvePre p (roundConfig o prev) prev fuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp => .fail

theorem coreVerdictWith_sat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : coreVerdictWith prev p o fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreVerdictWith at h
  cases hc : coreSolvePre p (roundConfig o prev) prev fuel with
  | sat a' => simp [hc] at h; cases h; exact coreSolvePre_sat hc
  | unsat => simp [hc] at h
  | gaveUp => simp [hc] at h

theorem coreVerdictWith_unsat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    (h : coreVerdictWith prev p o fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreVerdictWith at h
  cases hc : coreSolvePre p (roundConfig o prev) prev fuel with
  | sat a => simp [hc] at h
  | unsat => exact coreSolvePre_unsat hc
  | gaveUp => simp [hc] at h

/-- Core verdict together with the counters of that exact run.  The verdict
is the same as `coreVerdictWith`; the stats are diagnostic only. -/
def coreSolveStatsWith (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) : CertVerdict × EngineStats :=
  match coreSolveFullPre p (roundConfig o prev) prev fuel with
  | (.sat a, st) => (.sat a, st)
  | (.unsat, st) => (.unsat, st)
  | (.gaveUp, st) => (.fail, st)

theorem coreSolveStatsWith_fst {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat} :
    (coreSolveStatsWith prev p o fuel).1 = coreVerdictWith prev p o fuel := by
  unfold coreSolveStatsWith coreVerdictWith coreSolvePre
  cases h : coreSolveFullPre p (roundConfig o prev) prev fuel with
  | mk r st =>
      cases r <;> rfl

theorem coreSolveStatsWith_sat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    {a : List Value} {st : EngineStats}
    (h : coreSolveStatsWith prev p o fuel = (.sat a, st)) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolveStatsWith at h
  cases hf : coreSolveFullPre p (roundConfig o prev) prev fuel with
  | mk r st' =>
      cases r with
      | sat a' =>
          rw [hf] at h
          cases h
          exact coreSolveFullPre_sat hf
      | unsat => simp [hf] at h
      | gaveUp => simp [hf] at h

theorem coreSolveStatsWith_unsat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    {st : EngineStats}
    (h : coreSolveStatsWith prev p o fuel = (.unsat, st)) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolveStatsWith at h
  cases hf : coreSolveFullPre p (roundConfig o prev) prev fuel with
  | mk r st' =>
      cases r with
      | sat a' => simp [hf] at h
      | unsat => exact coreSolveFullPre_unsat hf
      | gaveUp => simp [hf] at h

/-- Stats-aware round with an already converted domain array for the
preprocessed round problem. -/
def coreSolveStatsWithPrepared (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) (doms : Array DomC)
    (hconv : convertDomains (presolveProblem (roundConfig o prev) p).domains = some doms) :
    CertVerdict × EngineStats :=
  match coreSolveFullPrePrepared p (roundConfig o prev) prev fuel doms hconv with
  | (.sat a, st) => (.sat a, st)
  | (.unsat, st) => (.unsat, st)
  | (.gaveUp, st) => (.fail, st)

theorem coreSolveStatsWithPrepared_eq {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    {doms : Array DomC}
    (hconv : convertDomains (presolveProblem (roundConfig o prev) p).domains = some doms) :
    coreSolveStatsWithPrepared prev p o fuel doms hconv =
      coreSolveStatsWith prev p o fuel := by
  unfold coreSolveStatsWithPrepared coreSolveStatsWith
  rw [coreSolveFullPrePrepared_eq]

theorem coreSolveStatsWithPrepared_sat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    {doms : Array DomC}
    {hconv : convertDomains (presolveProblem (roundConfig o prev) p).domains = some doms}
    {a : List Value} {st : EngineStats}
    (h : coreSolveStatsWithPrepared prev p o fuel doms hconv = (.sat a, st)) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  rw [coreSolveStatsWithPrepared_eq] at h
  exact coreSolveStatsWith_sat h

theorem coreSolveStatsWithPrepared_unsat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    {doms : Array DomC}
    {hconv : convertDomains (presolveProblem (roundConfig o prev) p).domains = some doms}
    {st : EngineStats}
    (h : coreSolveStatsWithPrepared prev p o fuel doms hconv = (.unsat, st)) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  rw [coreSolveStatsWithPrepared_eq] at h
  exact coreSolveStatsWith_unsat h

/-- Every round problem has the same domains as the initial problem, so one
conversion result is valid for every round. -/
theorem convertDomains_presolve_round (o : SearchConfig)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (bo : Option Int) (prev : Option (List Value)) (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms) :
    convertDomains (presolveProblem (roundConfig o prev) (curP p0 spec bo)).domains =
      some doms := by
  rw [presolveProblem_domains, curP_domains]
  rwa [presolveProblem_domains] at h0

/-- The partial Core oracle, optionally bounded for development/regression checks. -/
def corePartialSolver (o : SearchConfig := {}) (fuel : Nat := coreFuel) : PartialCertSolver where
  solveWith prev p := coreVerdictWith prev p o fuel
  sat_sound := fun _ _ _ h => coreVerdictWith_sat h
  unsat_sound := fun _ _ h => coreVerdictWith_unsat h

/-- Generic B&B adapter. Its completeness gate is deliberately false. -/
def coreSolver (o : SearchConfig := {}) (fuel : Nat := coreFuel) : CertSolver :=
  (corePartialSolver o fuel).asCertSolver

theorem coreSolver_solveWith (o : SearchConfig) (fuel : Nat)
    (prev : Option (List Value)) (p : CompiledProblem DomConstraint) :
    (coreSolver o fuel).solveWith prev p = coreVerdictWith prev p o fuel := rfl

/-- Core branch and bound carrying the aggregated engine counters.  Its first
component is the same `OptRun` as `optLoop (coreSolver o fuel)`; the stats
are diagnostics only. -/
def optLoopCoreStatsWith (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (prev : Option (List Value)) (bo : Option Int) : OptRun × EngineStats :=
  match hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
  | (.unsat, st) => (⟨[], true, bo⟩, st)
  | (.fail, st) => (⟨[], false, bo⟩, st)
  | (.sat a, st) =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          let r := optLoopCoreStatsWith o fuel p0 spec (some a) (some v)
          (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩, st.add r.2)
      | _ => (⟨[], false, bo⟩, st)
termination_by meas p0 spec bo
decreasing_by
  have hsat := coreSolveStatsWith_sat hs
  rw [curP_domains] at hsat
  exact meas_decr hsat.1 hsat.2 hv

/-- Core branch and bound whose converted domains are supplied once and reused
by every round.  All other round state is rebuilt exactly as in
`optLoopCoreStatsWith`. -/
def optLoopCoreStatsWithPrepared (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms)
    (prev : Option (List Value)) (bo : Option Int) : OptRun × EngineStats :=
  match hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) with
  | (.unsat, st) => (⟨[], true, bo⟩, st)
  | (.fail, st) => (⟨[], false, bo⟩, st)
  | (.sat a, st) =>
      match hv : a[spec.slot]? with
      | some (.int v) =>
          let r := optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 (some a) (some v)
          (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩, st.add r.2)
      | _ => (⟨[], false, bo⟩, st)
termination_by meas p0 spec bo
decreasing_by
  have hsat := coreSolveStatsWithPrepared_sat hs
  rw [curP_domains] at hsat
  exact meas_decr hsat.1 hsat.2 hv

private theorem optLoopCoreStatsWith_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {st : EngineStats}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.unsat, st)) :
    optLoopCoreStatsWith o fuel p0 spec prev bo = (⟨[], true, bo⟩, st) := by
  rw [optLoopCoreStatsWith, hs]

private theorem optLoopCoreStatsWith_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {st : EngineStats}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.fail, st)) :
    optLoopCoreStatsWith o fuel p0 spec prev bo = (⟨[], false, bo⟩, st) := by
  rw [optLoopCoreStatsWith, hs]

private theorem optLoopCoreStatsWith_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int} {st : EngineStats}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.sat a, st))
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopCoreStatsWith o fuel p0 spec prev bo =
      (⟨(a, v) :: (optLoopCoreStatsWith o fuel p0 spec (some a) (some v)).1.sols,
          (optLoopCoreStatsWith o fuel p0 spec (some a) (some v)).1.complete,
          (optLoopCoreStatsWith o fuel p0 spec (some a) (some v)).1.lastBound⟩,
        st.add (optLoopCoreStatsWith o fuel p0 spec (some a) (some v)).2) := by
  conv => lhs; rw [optLoopCoreStatsWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopCoreStatsWith_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {st : EngineStats}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.sat a, st))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopCoreStatsWith o fuel p0 spec prev bo = (⟨[], false, bo⟩, st) := by
  conv => lhs; rw [optLoopCoreStatsWith]
  rw [hs]
  simp only []

private theorem optLoopCoreStatsWithPrepared_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {st : EngineStats}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.unsat, st)) :
    optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo = (⟨[], true, bo⟩, st) := by
  rw [optLoopCoreStatsWithPrepared, hs]

private theorem optLoopCoreStatsWithPrepared_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {st : EngineStats}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.fail, st)) :
    optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo = (⟨[], false, bo⟩, st) := by
  rw [optLoopCoreStatsWithPrepared, hs]

private theorem optLoopCoreStatsWithPrepared_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {a : List Value} {v : Int} {st : EngineStats}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st))
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo =
      (⟨(a, v) :: (optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 (some a) (some v)).1.sols,
          (optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 (some a) (some v)).1.complete,
          (optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 (some a) (some v)).1.lastBound⟩,
        st.add (optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 (some a) (some v)).2) := by
  conv => lhs; rw [optLoopCoreStatsWithPrepared]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopCoreStatsWithPrepared_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {a : List Value} {st : EngineStats}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo =
      (⟨[], false, bo⟩, st) := by
  conv => lhs; rw [optLoopCoreStatsWithPrepared]
  rw [hs]
  simp only []


private theorem optLoopWith_core_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .unsat) :
    optLoopWith (coreSolver o fuel) p0 spec prev bo = ⟨[], true, bo⟩ := by
  rw [optLoopWith, hs]

private theorem optLoopWith_core_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .fail) :
    optLoopWith (coreSolver o fuel) p0 spec prev bo = ⟨[], false, bo⟩ := by
  rw [optLoopWith, hs]

private theorem optLoopWith_core_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a)
    (hv : a[spec.slot]? = some (.int v)) :
    optLoopWith (coreSolver o fuel) p0 spec prev bo =
      ⟨(a, v) :: (optLoopWith (coreSolver o fuel) p0 spec (some a) (some v)).sols,
        (optLoopWith (coreSolver o fuel) p0 spec (some a) (some v)).complete,
        (optLoopWith (coreSolver o fuel) p0 spec (some a) (some v)).lastBound⟩ := by
  conv => lhs; rw [optLoopWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optLoopWith_core_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a)
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optLoopWith (coreSolver o fuel) p0 spec prev bo = ⟨[], false, bo⟩ := by
  conv => lhs; rw [optLoopWith]
  rw [hs]
  simp only []

/-- Stats collection does not change the certified optimization run: the
first component is the ordinary `optLoop` result. -/
theorem optLoopCoreStatsWith_fst (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec) :
    ∀ n prev bo, meas p0 spec bo = n →
      (optLoopCoreStatsWith o fuel p0 spec prev bo).1 =
        optLoopWith (coreSolver o fuel) p0 spec prev bo := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro prev bo hn
      have hwire := coreSolveStatsWith_fst (prev := prev)
        (p := curP p0 spec bo) (o := o) (fuel := fuel)
      cases hc : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
      | mk r st =>
          cases r with
          | unsat =>
              have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .unsat := by
                rw [coreSolver_solveWith, ← hwire]
                rw [hc]
              rw [optLoopCoreStatsWith_unsat_eq hc, optLoopWith_core_unsat_eq hcv]
          | fail =>
              have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .fail := by
                rw [coreSolver_solveWith, ← hwire]
                rw [hc]
              rw [optLoopCoreStatsWith_fail_eq hc, optLoopWith_core_fail_eq hcv]
          | sat a =>
              cases hv : a[spec.slot]? with
              | none =>
                  have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                    intro i hi
                    rw [hv] at hi
                    cases hi
                  have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                    rw [coreSolver_solveWith, ← hwire]
                    rw [hc]
                  rw [optLoopCoreStatsWith_sat_none_eq hc hn',
                    optLoopWith_core_sat_none_eq hcv hn']
              | some w =>
                  cases w with
                  | int v =>
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      have hsat := coreSolveStatsWith_sat hc
                      rw [curP_domains] at hsat
                      have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
                      rw [optLoopCoreStatsWith_sat_int_eq hc hv,
                        optLoopWith_core_sat_int_eq hcv hv]
                      simp only [IH]
                  | bool b =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optLoopCoreStatsWith_sat_none_eq hc hn',
                        optLoopWith_core_sat_none_eq hcv hn']
                  | setOfInt s =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optLoopCoreStatsWith_sat_none_eq hc hn',
                        optLoopWith_core_sat_none_eq hcv hn']
                  | array arr =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optLoopCoreStatsWith_sat_none_eq hc hn',
                        optLoopWith_core_sat_none_eq hcv hn']

/-- Reusing one converted domain array across rounds does not change the
stats loop: every round's problem has the same domains, and the prepared
entry is pointwise the ordinary one. -/
theorem optLoopCoreStatsWithPrepared_eq (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms) :
    ∀ prev bo,
      optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo =
        optLoopCoreStatsWith o fuel p0 spec prev bo := by
  intro prev bo
  suffices h : ∀ n prev bo, meas p0 spec bo = n →
      optLoopCoreStatsWithPrepared o fuel p0 spec doms h0 prev bo =
        optLoopCoreStatsWith o fuel p0 spec prev bo from h _ prev bo rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro prev bo hn
      cases hc : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
      | mk r st =>
          cases r with
          | unsat =>
              have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                  (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.unsat, st) := by
                rw [coreSolveStatsWithPrepared_eq, hc]
              rw [optLoopCoreStatsWithPrepared_unsat_eq hcp,
                optLoopCoreStatsWith_unsat_eq hc]
          | fail =>
              have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                  (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.fail, st) := by
                rw [coreSolveStatsWithPrepared_eq, hc]
              rw [optLoopCoreStatsWithPrepared_fail_eq hcp,
                optLoopCoreStatsWith_fail_eq hc]
          | sat a =>
              cases hv : a[spec.slot]? with
              | none =>
                  have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                    intro i hi
                    rw [hv] at hi
                    cases hi
                  have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                    rw [coreSolveStatsWithPrepared_eq, hc]
                  rw [optLoopCoreStatsWithPrepared_sat_none_eq hcp hn',
                    optLoopCoreStatsWith_sat_none_eq hc hn']
              | some w =>
                  cases w with
                  | int v =>
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      have hsat := coreSolveStatsWithPrepared_sat hcp
                      rw [curP_domains] at hsat
                      have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
                      rw [optLoopCoreStatsWithPrepared_sat_int_eq hcp hv,
                        optLoopCoreStatsWith_sat_int_eq hc hv, IH]
                  | bool b =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optLoopCoreStatsWithPrepared_sat_none_eq hcp hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']
                  | setOfInt s =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optLoopCoreStatsWithPrepared_sat_none_eq hcp hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']
                  | array arr =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optLoopCoreStatsWithPrepared_sat_none_eq hcp hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']


/-- Core-only linear branch-and-bound. `complete = false` retains valid incumbents. -/
def optimizeCore (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) :=
  optimizeCertified (coreSolver o fuel) m

/-- Streaming Core branch and bound that also aggregates the per-round
`EngineStats`.  It follows the same recursion as `optimizeStreamLoop`, so the
emitted solutions and the certified run are unchanged. -/
def optimizeStreamCoreStatsLoop {α : Type} (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (f : List Value → α) (emit : α → IO Unit) :
    Option (List Value) → Option Int → IO (OptRun × List α × EngineStats)
  | prev, bo =>
      match hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
      | (.unsat, st) => pure (⟨[], true, bo⟩, [], st)
      | (.fail, st) => pure (⟨[], false, bo⟩, [], st)
      | (.sat a, st) =>
          match hv : a[spec.slot]? with
          | some (.int v) =>
              emit (f a) >>= fun _ =>
                optimizeStreamCoreStatsLoop o fuel p0 spec f emit (some a) (some v) >>= fun r =>
                  pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                    f a :: r.2.1, st.add r.2.2)
          | _ => pure (⟨[], false, bo⟩, [], st)
termination_by prev bo => meas p0 spec bo
decreasing_by
  have hsat := coreSolveStatsWith_sat hs
  rw [curP_domains] at hsat
  exact meas_decr hsat.1 hsat.2 hv

/-- Streaming stats loop with one converted domain array reused by every
round.  The recursion, emissions and counters are those of
`optimizeStreamCoreStatsLoop`. -/
def optimizeStreamCoreStatsLoopPrepared {α : Type} (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms)
    (f : List Value → α) (emit : α → IO Unit) :
    Option (List Value) → Option Int → IO (OptRun × List α × EngineStats)
  | prev, bo =>
      match hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
          (convertDomains_presolve_round o p0 spec bo prev doms h0) with
      | (.unsat, st) => pure (⟨[], true, bo⟩, [], st)
      | (.fail, st) => pure (⟨[], false, bo⟩, [], st)
      | (.sat a, st) =>
          match hv : a[spec.slot]? with
          | some (.int v) =>
              emit (f a) >>= fun _ =>
                optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit (some a) (some v) >>= fun r =>
                  pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
                    f a :: r.2.1, st.add r.2.2)
          | _ => pure (⟨[], false, bo⟩, [], st)
termination_by prev bo => meas p0 spec bo
decreasing_by
  have hsat := coreSolveStatsWithPrepared_sat hs
  rw [curP_domains] at hsat
  exact meas_decr hsat.1 hsat.2 hv

private theorem optimizeStreamCoreStatsLoop_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.unsat, st)) :
    optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
      pure (⟨[], true, bo⟩, [], st) := by
  rw [optimizeStreamCoreStatsLoop, hs]

private theorem optimizeStreamCoreStatsLoop_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.fail, st)) :
    optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
      pure (⟨[], false, bo⟩, [], st) := by
  rw [optimizeStreamCoreStatsLoop, hs]

private theorem optimizeStreamCoreStatsLoop_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.sat a, st))
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
      (emit (f a) >>= fun _ =>
        optimizeStreamCoreStatsLoop o fuel p0 spec f emit (some a) (some v) >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            f a :: r.2.1, st.add r.2.2)) := by
  conv => lhs; rw [optimizeStreamCoreStatsLoop]
  rw [hs]
  simp only []
  rw [hv]

private theorem optimizeStreamCoreStatsLoop_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWith prev (curP p0 spec bo) o fuel = (.sat a, st))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
      pure (⟨[], false, bo⟩, [], st) := by
  conv => lhs; rw [optimizeStreamCoreStatsLoop]
  rw [hs]
  simp only []

private theorem optimizeStreamCoreStatsLoopPrepared_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.unsat, st)) :
    optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
      pure (⟨[], true, bo⟩, [], st) := by
  rw [optimizeStreamCoreStatsLoopPrepared, hs]

private theorem optimizeStreamCoreStatsLoopPrepared_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.fail, st)) :
    optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
      pure (⟨[], false, bo⟩, [], st) := by
  rw [optimizeStreamCoreStatsLoopPrepared, hs]

private theorem optimizeStreamCoreStatsLoopPrepared_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {a : List Value} {v : Int} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st))
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
      (emit (f a) >>= fun _ =>
        optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit (some a) (some v) >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            f a :: r.2.1, st.add r.2.2)) := by
  conv => lhs; rw [optimizeStreamCoreStatsLoopPrepared]
  rw [hs]
  simp only []
  rw [hv]

private theorem optimizeStreamCoreStatsLoopPrepared_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {doms : Array DomC}
    {h0 : convertDomains (presolveProblem o p0).domains = some doms}
    {prev : Option (List Value)} {a : List Value} {st : EngineStats}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st))
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
      pure (⟨[], false, bo⟩, [], st) := by
  conv => lhs; rw [optimizeStreamCoreStatsLoopPrepared]
  rw [hs]
  simp only []

private theorem optimizeStreamLoopWith_core_unsat_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .unsat) :
    optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo =
      pure (⟨[], true, bo⟩, []) := by
  rw [optimizeStreamLoopWith, hs]

private theorem optimizeStreamLoopWith_core_fail_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .fail) :
    optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo =
      pure (⟨[], false, bo⟩, []) := by
  rw [optimizeStreamLoopWith, hs]

private theorem optimizeStreamLoopWith_core_sat_int_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value} {v : Int}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a)
    (hv : a[spec.slot]? = some (.int v)) :
    optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo =
      (emit (f a) >>= fun _ =>
        optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit (some a) (some v) >>= fun r =>
          pure (⟨(a, v) :: r.1.sols, r.1.complete, r.1.lastBound⟩,
            f a :: r.2)) := by
  conv => lhs; rw [optimizeStreamLoopWith]
  rw [hs]
  simp only []
  rw [hv]

private theorem optimizeStreamLoopWith_core_sat_none_eq {o : SearchConfig} {fuel : Nat}
    {p0 : CompiledProblem DomConstraint} {spec : ObjectiveSpec} {bo : Option Int}
    {prev : Option (List Value)} {a : List Value}
    {α : Type} {f : List Value → α} {emit : α → IO Unit}
    (hs : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a)
    (hn : ∀ i : Int, a[spec.slot]? ≠ some (.int i)) :
    optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo =
      pure (⟨[], false, bo⟩, []) := by
  conv => lhs; rw [optimizeStreamLoopWith]
  rw [hs]
  simp only []

/-- The stats-aware streaming loop has exactly the run and emissions of the
ordinary streaming loop, and its stats are the pure stats loop's counters. -/
theorem optimizeStreamCoreStatsLoop_eq (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    {α : Type} (f : List Value → α) (emit : α → IO Unit) :
    ∀ prev bo,
      optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
        (optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo >>= fun r =>
          pure (r.1, r.2, (optLoopCoreStatsWith o fuel p0 spec prev bo).2)) := by
  intro prev bo
  suffices h : ∀ n prev bo, meas p0 spec bo = n →
      optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo =
        (optimizeStreamLoopWith (coreSolver o fuel) p0 spec f emit prev bo >>= fun r =>
          pure (r.1, r.2, (optLoopCoreStatsWith o fuel p0 spec prev bo).2)) from
    h _ prev bo rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro prev bo hn
      have hwire := coreSolveStatsWith_fst (prev := prev)
        (p := curP p0 spec bo) (o := o) (fuel := fuel)
      cases hc : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
      | mk r st =>
          cases r with
          | unsat =>
              have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .unsat := by
                rw [coreSolver_solveWith, ← hwire]
                rw [hc]
              rw [optimizeStreamCoreStatsLoop_unsat_eq hc,
                optimizeStreamLoopWith_core_unsat_eq hcv,
                optLoopCoreStatsWith_unsat_eq hc]
              simp only [coreStats_io_pure_bind]
          | fail =>
              have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .fail := by
                rw [coreSolver_solveWith, ← hwire]
                rw [hc]
              rw [optimizeStreamCoreStatsLoop_fail_eq hc,
                optimizeStreamLoopWith_core_fail_eq hcv,
                optLoopCoreStatsWith_fail_eq hc]
              simp only [coreStats_io_pure_bind]
          | sat a =>
              cases hv : a[spec.slot]? with
              | none =>
                  have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                    intro i hi
                    rw [hv] at hi
                    cases hi
                  have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                    rw [coreSolver_solveWith, ← hwire]
                    rw [hc]
                  rw [optimizeStreamCoreStatsLoop_sat_none_eq hc hn',
                    optimizeStreamLoopWith_core_sat_none_eq hcv hn',
                    optLoopCoreStatsWith_sat_none_eq hc hn']
                  simp only [coreStats_io_pure_bind]
              | some w =>
                  cases w with
                  | int v =>
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      have hsat := coreSolveStatsWith_sat hc
                      rw [curP_domains] at hsat
                      have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
                      rw [optimizeStreamCoreStatsLoop_sat_int_eq hc hv,
                        optimizeStreamLoopWith_core_sat_int_eq hcv hv,
                        optLoopCoreStatsWith_sat_int_eq hc hv, IH]
                      simp only [coreStats_io_bind_assoc, coreStats_io_pure_bind]
                  | bool b =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optimizeStreamCoreStatsLoop_sat_none_eq hc hn',
                        optimizeStreamLoopWith_core_sat_none_eq hcv hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']
                      simp only [coreStats_io_pure_bind]
                  | setOfInt s =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optimizeStreamCoreStatsLoop_sat_none_eq hc hn',
                        optimizeStreamLoopWith_core_sat_none_eq hcv hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']
                      simp only [coreStats_io_pure_bind]
                  | array arr =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcv : (coreSolver o fuel).solveWith prev (curP p0 spec bo) = .sat a := by
                        rw [coreSolver_solveWith, ← hwire]
                        rw [hc]
                      rw [optimizeStreamCoreStatsLoop_sat_none_eq hc hn',
                        optimizeStreamLoopWith_core_sat_none_eq hcv hn',
                        optLoopCoreStatsWith_sat_none_eq hc hn']
                      simp only [coreStats_io_pure_bind]

/-- The prepared streaming loop is exactly the ordinary stats loop: only the
per-round domain conversion is shared, and it is the same conversion. -/
theorem optimizeStreamCoreStatsLoopPrepared_eq (o : SearchConfig) (fuel : Nat)
    (p0 : CompiledProblem DomConstraint) (spec : ObjectiveSpec)
    (doms : Array DomC)
    (h0 : convertDomains (presolveProblem o p0).domains = some doms)
    {α : Type} (f : List Value → α) (emit : α → IO Unit) :
    ∀ prev bo,
      optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
        optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo := by
  intro prev bo
  suffices h : ∀ n prev bo, meas p0 spec bo = n →
      optimizeStreamCoreStatsLoopPrepared o fuel p0 spec doms h0 f emit prev bo =
        optimizeStreamCoreStatsLoop o fuel p0 spec f emit prev bo from h _ prev bo rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro prev bo hn
      cases hc : coreSolveStatsWith prev (curP p0 spec bo) o fuel with
      | mk r st =>
          cases r with
          | unsat =>
              have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                  (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.unsat, st) := by
                rw [coreSolveStatsWithPrepared_eq, hc]
              rw [optimizeStreamCoreStatsLoopPrepared_unsat_eq hcp,
                optimizeStreamCoreStatsLoop_unsat_eq hc]
          | fail =>
              have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                  (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.fail, st) := by
                rw [coreSolveStatsWithPrepared_eq, hc]
              rw [optimizeStreamCoreStatsLoopPrepared_fail_eq hcp,
                optimizeStreamCoreStatsLoop_fail_eq hc]
          | sat a =>
              cases hv : a[spec.slot]? with
              | none =>
                  have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                    intro i hi
                    rw [hv] at hi
                    cases hi
                  have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                      (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                    rw [coreSolveStatsWithPrepared_eq, hc]
                  rw [optimizeStreamCoreStatsLoopPrepared_sat_none_eq hcp hn',
                    optimizeStreamCoreStatsLoop_sat_none_eq hc hn']
              | some w =>
                  cases w with
                  | int v =>
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      have hsat := coreSolveStatsWithPrepared_sat hcp
                      rw [curP_domains] at hsat
                      have IH := ih _ (hn ▸ meas_decr hsat.1 hsat.2 hv) (some a) (some v) rfl
                      rw [optimizeStreamCoreStatsLoopPrepared_sat_int_eq hcp hv,
                        optimizeStreamCoreStatsLoop_sat_int_eq hc hv, IH]
                  | bool b =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optimizeStreamCoreStatsLoopPrepared_sat_none_eq hcp hn',
                        optimizeStreamCoreStatsLoop_sat_none_eq hc hn']
                  | setOfInt s =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optimizeStreamCoreStatsLoopPrepared_sat_none_eq hcp hn',
                        optimizeStreamCoreStatsLoop_sat_none_eq hc hn']
                  | array arr =>
                      have hn' : ∀ i : Int, a[spec.slot]? ≠ some (.int i) := by
                        intro i hi
                        rw [hv] at hi
                        cases hi
                      have hcp : coreSolveStatsWithPrepared prev (curP p0 spec bo) o fuel doms
                          (convertDomains_presolve_round o p0 spec bo prev doms h0) = (.sat a, st) := by
                        rw [coreSolveStatsWithPrepared_eq, hc]
                      rw [optimizeStreamCoreStatsLoopPrepared_sat_none_eq hcp hn',
                        optimizeStreamCoreStatsLoop_sat_none_eq hc hn']

/-- Streaming Core optimization entry with stats. -/
def optimizeStreamCoreStats (o : SearchConfig) (m : Model) (emit : Store → IO Unit) :
    IO (Except String (OptSummary × EngineStats)) := do
  let t0 ← IO.monoMsNow
  match compileModelOpt m with
  | .error e => pure (.error e)
  | .ok (p, spec) =>
      let t1 ← IO.monoMsNow
      let r ←
        match hdoms : convertDomains (presolveProblem o p).domains with
        | some doms =>
            optimizeStreamCoreStatsLoopPrepared o coreFuel p spec doms hdoms
              (fun a => p.toStore a) emit none none
        | none =>
            optimizeStreamCoreStatsLoop o coreFuel p spec (fun a => p.toStore a) emit none none
      let t2 ← IO.monoMsNow
      if o.stats then
        IO.eprintln s!"leanfzn: timing: compile_ms={t1 - t0} search_ms={t2 - t1}"
      pure (.ok (⟨p, r.1, r.2.1⟩, r.2.2))

theorem optimizeCore_solution_sound {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    {s : List Value × Int} (hs : s ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore s.1) ∧ LeanFzn.Semantics.ParamHonest m (p.toStore s.1) ∧
      m.solve.objective (p.toStore s.1) = some s.2 :=
  optimizeCertified_solution_sound h hwf hs

theorem optimizeCore_improving {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) :
    ∃ spec : ObjectiveSpec, run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) :=
  optimizeCertified_improving h

theorem optimizeCore_optimal {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) :=
  optimizeCertified_optimal h hwf hcomp hlast

theorem optimizeCore_unsat {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧ LeanFzn.Semantics.ParamHonest m store :=
  optimizeCertified_unsat h hwf hcomp hnil

end LeanFzn.Core
