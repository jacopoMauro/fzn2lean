/-
File: LeanFzn/Integration/ReferenceCorrectness.lean

Purpose:
  The public direct SAT/UNSAT theorems, closing the composed chain:
  `compile_exact`/`compile_covers` + `solveCompiled_sat`/`_unsat` +
  the `toStore` projection. No caller-supplied compiler-correspondence
  premise remains: the model-level well-formedness premise replaces
  it (the CLI checks it before solving).

Dependencies:
  - LeanFzn.Compiler.Proofs.Exact: exact/coverage whole-model theorems.
  - LeanFzn.Solver.Reference.Proofs.Search: exhaustive internal search.

DAG:
  Proofs.Exact + Proofs.Search -> LeanFzn.Compiler.Correctness
-/

import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Legacy.Solver.Reference.Proofs.Search
open LeanFzn.Compiler.Domains


namespace LeanFzn.Integration.Reference
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Compiler LeanFzn.Solver.Reference
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals

/-- **Direct SAT correctness**: a store returned by `solve` satisfies
    the model under the full signature and interpretation (every
    constraint holds, every declared variable reads an in-domain
    value, and — the fragment has no initializers — the initializer
    conditions are trivial). The well-formedness premise is the
    model-level static check the CLI performs before solving. -/
theorem solve_sat_correct {model : Model} {store : Store}
    (hwf : WellFormed fullSig model)
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
      subst hsolve
      -- the search's guarantee: membership + acceptance
      obtain ⟨hmem, hacc⟩ := solveCompiled_sat (problem := problem)
        (by rw [← hs])
      -- the whole-model exactness: the accepted assignment
      -- reconstructs the satisfying store conditions
      obtain ⟨hcons, hvars⟩ :=
        compile_exact hc hwf hmem hacc
      refine ⟨hwf, hcons, ?_, ?_⟩
      · -- the variable-declaration conditions
        intro d hd
        have := hvars d hd
        -- the fragment has no array variables (the gate); the
        -- basic shape is exactly the Satisfies condition
        match d with
        | .basic ty n _ _ => exact this
        | .array _ _ _ _ =>
            exact absurd this (by
              intro harr
              cases harr)
      · -- the initializer conditions: trivial in the fragment
        intro d hd
        -- the gate: every declared variable is initializer-free
        obtain ⟨ty, n, anns, hshape⟩ :=
          compileModel_vars_basic hc d hd
        rw [hshape]
        trivial
    | none =>
      simp only [hs] at hsolve
      simp at hsolve

/-- **Direct UNSAT correctness (honest stores)**: an `unsat` verdict
    excludes every store that satisfies the model's dynamic
    conditions AND is parameter-honest (every scalar parameter reads
    its declared model-given value — the FlatZinc instance fixes
    parameters; a solution store in the FlatZinc sense carries the
    model's parameter values, as does the reference checker's
    `completedStore` construction, `completedStore_paramHonest`). -/
theorem solve_unsat_correct {model : Model}
    (hwf : WellFormed fullSig model)
    (hsolve : solve model = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp model store ∧
      LeanFzn.Compiler.ParamHonest model store := by
  simp only [solve] at hsolve
  cases hc : compileModel model with
  | error _ => simp only [hc] at hsolve; simp at hsolve
  | ok problem =>
    simp only [hc] at hsolve
    cases hs : solveCompiled problem with
    | some assignment =>
      simp only [hs] at hsolve
      simp at hsolve
    | none =>
      simp only [hs] at hsolve
      rintro ⟨store, ⟨_, hcons, hvarsS, _⟩, hparam⟩
      -- adapt the Satisfies var-condition to the gate's basic-only
      -- shape (arrays are rejected by the compiler gate)
      have hvars : ∀ d ∈ model.variables, match d with
          | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
          | .array _ _ _ _ => False := by
        intro d hd
        match hdshape : d with
        | .basic ty n anns opt =>
            exact hvarsS (.basic ty n anns opt) (hdshape ▸ hd)
        | .array ty n anns elems =>
            exfalso
            obtain ⟨ty2, n2, anns2, hshape⟩ :=
              compileModel_vars_basic hc (.array ty n anns elems) hd
            cases hshape
      -- the coverage: the satisfying honest store yields an
      -- accepted assignment
      obtain ⟨a, hmem, hacc⟩ :=
        compile_covers hc hwf hcons hvars hparam
      -- the exhaustive search's failure excludes it
      have hfail := solveCompiled_unsat (problem := problem)
        (by rw [← hs]) a hmem
      rw [hacc] at hfail
      exact absurd hfail (by simp)

end LeanFzn.Integration.Reference
