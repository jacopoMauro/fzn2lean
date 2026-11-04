/-
File: LeanFzn/Integration/Optimization/Core.lean

N11a: certified branch-and-bound on the Core engine.  `CertSolver` (from
`Integration/Optimize.lean`) requires SAT soundness, UNSAT completeness, a
gate stable under adding the objective bound, and totality.  This file
instantiates it from the N9 seam `solveSearchConfigCore` for the no-previous
incumbent verdict and from the N10 `coreSolve`/kernel-fallback pair for the
incumbent-threaded verdict.

Mirroring `Integration/LcgOptimize.lean`:
* `coreVerdict` maps `solveSearchConfigCore` (Core with its proved kernel
  fallback on `gaveUp`) to a `CertVerdict`.
* `coreVerdictWith` runs the raw `coreSolve p o coreFuel`; a `gaveUp` is
  decided by the proved phase-aware kernel entry `solveSearchConfigWith p o
  prev`.  It keeps the historical phase-ignoring Core attempt and its
  theorem statements.
* `coreVerdictSeeded` is the incumbent-guided Core attempt used by
  `coreSolver.solveWith`: Core runs with the previous round's incumbent
  seeding the saved phases (`coreSolveWith`), and a `gaveUp` is still
  decided by the certified kernel fallback.
* `coreSolver` packages the verdicts as a `CertSolver`.  Its gate is
  unconditionally `true`: the `solveWith` fallback is certified for every
  compiled problem (`solveSearchConfigWith_verdict`), so no fragment
  restriction is needed at this layer.
* `optimizeCore` is `optimizeCertified (coreSolver o)`, and
  `optimizeCore_solution_sound`/`_optimal`/`_unsat`/`_total` are the
  `optimizeCertified_*` corollaries specialized to Core.

DAG: CoreSolve + Optimize -> CoreOptimize -> CLI/StrategyDriver.
-/
import LeanFzn.Legacy.Integration.Solve.Core
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Optimization.Chronological

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine

/-! ## Verdicts -/

/-- Map the Core seam (Core with its kernel fallback on `gaveUp`) into the
    generic optimization interface. -/
def coreVerdict (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    CertVerdict :=
  match solveSearchConfigCore p o with
  | .sat a => .sat a
  | .unsat => .unsat
  | .unknown => .fail

/-- The phase-aware variant: the raw Core run is tried first (it ignores the
    previous incumbent, since Core has no incumbent-guided value heuristic
    yet); a Core `gaveUp` is decided by the phase-aware kernel entry with the
    previous round's incumbent. -/
def coreVerdictWith (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    CertVerdict :=
  match coreSolve p o coreFuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp =>
      match solveSearchConfigWith p o prev with
      | .sat a => .sat a
      | .unsat => .unsat
      | .unknown => .fail

/-- The incumbent-guided Core attempt: the raw Core run with the previous
    round's incumbent seeding the saved phases, and the certified kernel
    fallback on a Core give-up.  This is the `solveWith` behaviour of
    `coreSolver`. -/
def coreVerdictSeeded (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    CertVerdict :=
  match coreSolveWith p o prev coreFuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp =>
      match solveSearchConfigWith p o prev with
      | .sat a => .sat a
      | .unsat => .unsat
      | .unknown => .fail

/-! ## Verdict characterisations -/

/-- A Core SAT verdict is a box member accepted by the compiled problem. -/
theorem coreVerdict_sat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {a : List Value} (h : coreVerdict p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  cases hc : solveSearchConfigCore p o with
  | sat a' =>
      have h' : CertVerdict.sat a' = CertVerdict.sat a := by
        simpa [coreVerdict, hc] using h
      cases h'
      exact solveSearchConfigCore_sat hc
  | unsat => simp [coreVerdict, hc] at h
  | unknown => simp [coreVerdict, hc] at h

/-- A Core UNSAT verdict excludes every box member. -/
theorem coreVerdict_unsat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    (h : coreVerdict p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  cases hc : solveSearchConfigCore p o with
  | sat a' => simp [coreVerdict, hc] at h
  | unsat => exact solveSearchConfigCore_unsat hc
  | unknown => simp [coreVerdict, hc] at h

/-- The Core verdict is total: `solveSearchConfigCore_total` rules out the
    kernel fallback's `unknown`, hence the `fail` constructor. -/
theorem coreVerdict_ne_fail (p : CompiledProblem DomConstraint)
    (o : SearchConfig := {}) : coreVerdict p o ≠ .fail := by
  cases hc : solveSearchConfigCore p o with
  | sat a' => simp [coreVerdict, hc]
  | unsat => simp [coreVerdict, hc]
  | unknown => exact absurd hc (solveSearchConfigCore_total p o)

/-- The Core verdict is SAT exactly when the N9 seam is SAT. -/
theorem coreVerdict_eq_sat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {a : List Value} :
    coreVerdict p o = .sat a ↔ solveSearchConfigCore p o = .sat a := by
  cases h : solveSearchConfigCore p o <;> simp [coreVerdict, h]

/-- The Core verdict is UNSAT exactly when the N9 seam is UNSAT. -/
theorem coreVerdict_eq_unsat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} :
    coreVerdict p o = .unsat ↔ solveSearchConfigCore p o = .unsat := by
  cases h : solveSearchConfigCore p o <;> simp [coreVerdict, h]

/-- A phase-aware Core SAT verdict is a box member accepted by the compiled
    problem (raw Core SAT, or the kernel fallback on a Core give-up). -/
theorem coreVerdictWith_sat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {prev : Option (List Value)} {a : List Value}
    (h : coreVerdictWith prev p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  cases hc : coreSolve p o coreFuel with
  | sat a' =>
      have h' : CertVerdict.sat a' = CertVerdict.sat a := by
        simpa [coreVerdictWith, hc] using h
      cases h'
      exact coreSolve_sat hc
  | unsat => simp [coreVerdictWith, hc] at h
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' =>
          have h' : CertVerdict.sat a' = CertVerdict.sat a := by
            simpa [coreVerdictWith, hc, hs] using h
          cases h'
          exact solveSearchConfigWith_sat hs
      | unsat => simp [coreVerdictWith, hc, hs] at h
      | unknown => simp [coreVerdictWith, hc, hs] at h

/-- A phase-aware Core UNSAT verdict excludes every box member. -/
theorem coreVerdictWith_unsat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {prev : Option (List Value)}
    (h : coreVerdictWith prev p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [coreVerdictWith, hc] at h
  | unsat => exact coreSolve_unsat hc
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictWith, hc, hs] at h
      | unsat => exact solveSearchConfigWith_unsat hs
      | unknown => simp [coreVerdictWith, hc, hs] at h

/-- The phase-aware Core verdict is total, including the kernel fallback on a
    Core give-up (`solveSearchConfigWith_verdict`). -/
theorem coreVerdictWith_ne_fail (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    coreVerdictWith prev p o ≠ .fail := by
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [coreVerdictWith, hc]
  | unsat => simp [coreVerdictWith, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictWith, hc, hs]
      | unsat => simp [coreVerdictWith, hc, hs]
      | unknown => exact absurd hs (solveSearchConfigWith_verdict p o prev)

/-- On a Core give-up the phase-aware verdict is exactly the kernel fallback. -/
theorem coreVerdictWith_eq_fallback {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    (h : coreSolve p o coreFuel = .gaveUp) :
    coreVerdictWith prev p o =
      (match solveSearchConfigWith p o prev with
       | .sat a => .sat a
       | .unsat => .unsat
       | .unknown => .fail) := by
  simp [coreVerdictWith, h]

/-- While Core decides a problem, the phase-aware verdict is the plain Core
    verdict (the incumbent is only consulted on a Core give-up). -/
theorem coreVerdictWith_eq_coreVerdict_of_not_gaveUp {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    (h : coreSolve p o coreFuel ≠ .gaveUp) :
    coreVerdictWith prev p o = coreVerdict p o := by
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [coreVerdictWith, coreVerdict, solveSearchConfigCore, hc]
  | unsat => simp [coreVerdictWith, coreVerdict, solveSearchConfigCore, hc]
  | gaveUp => exact absurd hc h

/-- The phase-aware Core verdict is SAT exactly when Core is SAT or Core gave
    up and the kernel fallback is SAT. -/
theorem coreVerdictWith_eq_sat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    {a : List Value} :
    coreVerdictWith prev p o = .sat a ↔
      coreSolve p o coreFuel = .sat a ∨
        (coreSolve p o coreFuel = .gaveUp ∧
          solveSearchConfigWith p o prev = .sat a) := by
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [coreVerdictWith, hc]
  | unsat => simp [coreVerdictWith, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictWith, hc, hs]
      | unsat => simp [coreVerdictWith, hc, hs]
      | unknown => simp [coreVerdictWith, hc, hs]

/-- The phase-aware Core verdict is UNSAT exactly when Core is UNSAT or Core
    gave up and the kernel fallback is UNSAT. -/
theorem coreVerdictWith_eq_unsat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)} :
    coreVerdictWith prev p o = .unsat ↔
      coreSolve p o coreFuel = .unsat ∨
        (coreSolve p o coreFuel = .gaveUp ∧
          solveSearchConfigWith p o prev = .unsat) := by
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [coreVerdictWith, hc]
  | unsat => simp [coreVerdictWith, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictWith, hc, hs]
      | unsat => simp [coreVerdictWith, hc, hs]
      | unknown => simp [coreVerdictWith, hc, hs]

/-- An incumbent-guided Core SAT verdict is a box member accepted by the
compiled problem (Core SAT with seeded phases, or the kernel fallback on a
Core give-up). -/
theorem coreVerdictSeeded_sat {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    {a : List Value} (h : coreVerdictSeeded prev p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  cases hc : coreSolveWith p o prev coreFuel with
  | sat a' =>
      have h' : CertVerdict.sat a' = CertVerdict.sat a := by
        simpa [coreVerdictSeeded, hc] using h
      cases h'
      exact coreSolveWith_sat hc
  | unsat => simp [coreVerdictSeeded, hc] at h
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' =>
          have h' : CertVerdict.sat a' = CertVerdict.sat a := by
            simpa [coreVerdictSeeded, hc, hs] using h
          cases h'
          exact solveSearchConfigWith_sat hs
      | unsat => simp [coreVerdictSeeded, hc, hs] at h
      | unknown => simp [coreVerdictSeeded, hc, hs] at h

/-- An incumbent-guided Core UNSAT verdict excludes every box member. -/
theorem coreVerdictSeeded_unsat {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    (h : coreVerdictSeeded prev p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  cases hc : coreSolveWith p o prev coreFuel with
  | sat a' => simp [coreVerdictSeeded, hc] at h
  | unsat => exact coreSolveWith_unsat hc
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictSeeded, hc, hs] at h
      | unsat => exact solveSearchConfigWith_unsat hs
      | unknown => simp [coreVerdictSeeded, hc, hs] at h

/-- The incumbent-guided Core verdict is total, including the kernel fallback
on a seeded Core give-up (`solveSearchConfigWith_verdict`). -/
theorem coreVerdictSeeded_ne_fail (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    coreVerdictSeeded prev p o ≠ .fail := by
  cases hc : coreSolveWith p o prev coreFuel with
  | sat a' => simp [coreVerdictSeeded, hc]
  | unsat => simp [coreVerdictSeeded, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictSeeded, hc, hs]
      | unsat => simp [coreVerdictSeeded, hc, hs]
      | unknown => exact absurd hs (solveSearchConfigWith_verdict p o prev)

/-- On a seeded Core give-up the incumbent-guided verdict is exactly the
kernel fallback. -/
theorem coreVerdictSeeded_eq_fallback {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    (h : coreSolveWith p o prev coreFuel = .gaveUp) :
    coreVerdictSeeded prev p o =
      (match solveSearchConfigWith p o prev with
       | .sat a => .sat a
       | .unsat => .unsat
       | .unknown => .fail) := by
  simp [coreVerdictSeeded, h]

/-- The incumbent-guided Core verdict is SAT exactly when the seeded Core run
is SAT or it gave up and the kernel fallback is SAT. -/
theorem coreVerdictSeeded_eq_sat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)}
    {a : List Value} :
    coreVerdictSeeded prev p o = .sat a ↔
      coreSolveWith p o prev coreFuel = .sat a ∨
        (coreSolveWith p o prev coreFuel = .gaveUp ∧
          solveSearchConfigWith p o prev = .sat a) := by
  cases hc : coreSolveWith p o prev coreFuel with
  | sat a' => simp [coreVerdictSeeded, hc]
  | unsat => simp [coreVerdictSeeded, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictSeeded, hc, hs]
      | unsat => simp [coreVerdictSeeded, hc, hs]
      | unknown => simp [coreVerdictSeeded, hc, hs]

/-- The incumbent-guided Core verdict is UNSAT exactly when the seeded Core
run is UNSAT or it gave up and the kernel fallback is UNSAT. -/
theorem coreVerdictSeeded_eq_unsat_iff {o : SearchConfig}
    {p : CompiledProblem DomConstraint} {prev : Option (List Value)} :
    coreVerdictSeeded prev p o = .unsat ↔
      coreSolveWith p o prev coreFuel = .unsat ∨
        (coreSolveWith p o prev coreFuel = .gaveUp ∧
          solveSearchConfigWith p o prev = .unsat) := by
  cases hc : coreSolveWith p o prev coreFuel with
  | sat a' => simp [coreVerdictSeeded, hc]
  | unsat => simp [coreVerdictSeeded, hc]
  | gaveUp =>
      cases hs : solveSearchConfigWith p o prev with
      | sat a' => simp [coreVerdictSeeded, hc, hs]
      | unsat => simp [coreVerdictSeeded, hc, hs]
      | unknown => simp [coreVerdictSeeded, hc, hs]

/-! ## The Core `CertSolver` instance -/

/-- Core with its certified kernel fallback implements the certified
    optimizer's solver interface, for any options `o`.  `solveWith` seeds the
    saved phases with the previous round's incumbent; `solve` is the
    incumbent-free entry.  The gate is unconditionally `true`:
    `coreVerdictSeeded` never fails (`coreVerdictSeeded_ne_fail`), because
    the fallback `solveSearchConfigWith` is total by
    `solveSearchConfigWith_verdict`. -/
def coreSolver (o : SearchConfig := {}) : CertSolver where
  solve p := coreVerdict p o
  solveWith prev p := coreVerdictSeeded prev p o
  gate _ := true
  sat_sound := fun _ _ h => coreVerdict_sat h
  solveWith_sat := fun _ _ _ h => coreVerdictSeeded_sat h
  unsat_complete := fun _ h => coreVerdict_unsat h
  solveWith_unsat := fun _ _ h => coreVerdictSeeded_unsat h
  gate_add := fun _ _ => rfl
  total := fun p _ => coreVerdict_ne_fail p o
  solveWith_total := fun p prev _ => coreVerdictSeeded_ne_fail prev p o

/-- The Core solver's gate is unconditionally open (the fallback is
    certified for every compiled problem). -/
theorem coreSolver_gate (o : SearchConfig := {}) :
    ∀ p : CompiledProblem DomConstraint, (coreSolver o).gate p = true :=
  fun _ => rfl

/-! ## The Core optimizer -/

/-- Core-backed certified branch and bound. -/
def optimizeCore (m : LeanFzn.Model) (o : SearchConfig := {}) :
    Except String (CompiledProblem DomConstraint × OptRun) :=
  optimizeCertified (coreSolver o) m

/-- Every emitted Core incumbent is a source-model solution with the reported
    objective value. -/
theorem optimizeCore_solution_sound {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o = .ok (p, run)) (hwf : WellFormed fullSig m)
    {s : List Value × Int} (hs : s ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore s.1) ∧
    LeanFzn.Semantics.ParamHonest m (p.toStore s.1) ∧
    m.solve.objective (p.toStore s.1) = some s.2 :=
  optimizeCertified_solution_sound (S := coreSolver o) h hwf hs

/-- The objective strictly improves along the emitted Core incumbents. -/
theorem optimizeCore_improving {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o = .ok (p, run)) :
    ∃ spec : ObjectiveSpec,
      run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) :=
  optimizeCertified_improving (S := coreSolver o) h

/-- A completed Core run's last incumbent is an optimal source solution. -/
theorem optimizeCore_optimal {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) :=
  optimizeCertified_optimal (S := coreSolver o) h hwf hcomp hlast

/-- A completed Core run without incumbents proves the source model has no
    parameter-honest satisfying store. -/
theorem optimizeCore_unsat {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store :=
  optimizeCertified_unsat (S := coreSolver o) h hwf hcomp hnil

/-- The Core run always completes: its gate is `true` and the fallback is
    certified. -/
theorem optimizeCore_total {o : SearchConfig} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o = .ok (p, run)) (hwf : WellFormed fullSig m) :
    run.complete = true :=
  optimizeCertified_total (S := coreSolver o) h hwf (coreSolver_gate o p)

end LeanFzn.Integration
