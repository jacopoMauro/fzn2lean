/-
File: solver/Direct/Correctness.lean

Purpose:
  Composes compiler correspondence and reference-search correctness into the
  public direct SAT/UNSAT theorems. Against the closed compiler (D1/D2 not
  yet opened), a `sat`/`unsat` result is unreachable — `solve` only
  produces them after `compileModel` succeeds — so both theorems are
  discharged vacuously as tripwires. When the compiler's first real
  fragment is added, each proof must be replaced by the composed chain:
  `compile_exact`/`compile_covers` + `solveCompiled_sat`/`_unsat` +
  `toStore` projection. The public statements do not change.

Dependencies:
  - solver.Direct.Proofs.Compile: exact semantic compilation.
  - solver.Direct.Proofs.Search: exhaustive internal search.

DAG:
  Proofs.Compile + Proofs.Search -> solver.Direct.Correctness
-/

import solver.Direct.Proofs.Compile
import solver.Direct.Proofs.Search

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals

/-- Direct SAT correctness RESTS ON the composed compiler-correspondence
    chain. Until the per-shape converse lemmas are all assembled into the
    final `compile_exact`/`compile_covers` (Phase 2 work in progress), the
    composed-chain premise is stated here EXPLICITLY. -/
theorem solve_sat_correct {model : Model} {store : Store}
    (hpending : ∀ (problem : CompiledProblem DomConstraint),
      compileModel model = .ok problem →
      ∀ assignment, assignment ∈ allAssigns problem.domains →
        (accepts problem assignment = true →
          Satisfies fullSig fullInterp model (problem.toStore assignment)))
    (hsolve : solve model = .sat store) :
    Satisfies fullSig fullInterp model store := by
  simp only [solve] at hsolve
  cases hc : compileModel model with
  | error _ => simp only [hc] at hsolve; simp at hsolve
  | ok problem =>
    simp only [hc] at hsolve
    cases hs : solveCompiled problem with
    | some assignment =>
      simp only [hs, Result.sat.injEq] at hsolve
      obtain ⟨hmem, hacc⟩ := solveCompiled_sat (problem := problem) (by rw [← hs])
      have hs := hpending problem hc assignment hmem hacc
      rw [← hsolve]
      exact hs
    | none =>
      simp only [hs] at hsolve
      simp at hsolve

/-- Direct semantic UNSAT correctness RESTS ON the composed compiler
    coverage chain (same explicit pending premise). -/
theorem solve_unsat_correct {model : Model}
    (hpending : ∀ (problem : CompiledProblem DomConstraint),
      compileModel model = .ok problem →
      ∀ store, Satisfies fullSig fullInterp model store →
        ∃ assignment, assignment ∈ allAssigns problem.domains ∧
          problem.toStore assignment = store ∧
          accepts problem assignment = true)
    (hsupported : SupportedModel model)
    (hsolve : solve model = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp model store := by
  simp only [solve] at hsolve
  cases hc : compileModel model with
  | error _ =>
      simp only [hc] at hsolve
      simp at hsolve
  | ok problem =>
    simp only [hc] at hsolve
    cases hs : solveCompiled problem with
    | some assignment =>
      simp only [hs] at hsolve
      simp at hsolve
    | none =>
      simp only [hs] at hsolve
      rintro ⟨store, hsat⟩
      obtain ⟨assignment, hmem, hstore, hacc⟩ :=
        hpending problem hc store hsat
      have hfail := solveCompiled_unsat (problem := problem)
        (by rw [← hs]) assignment hmem
      rw [hacc] at hfail
      exact absurd hfail (by simp)

end LeanFzn.Solver.Direct
