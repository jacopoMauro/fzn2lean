/-
Purpose: the source-level certified solve command. Compile a model, check the
finite int/bool gate, run proved CP propagation and lazy clause learning on a
fuel-free chronological frontier, then transport verdicts through compiler
correspondence. Unsupported source shapes remain explicit errors.

D1 EXECUTABLE-TO-THEOREM MAPPING (2026-10-10):
  CLI route `solveCertified` (this file) -> certified chronological
  `analyzedSolve` path -> theorems `solveCertified_sat_correct`,
  `solveCertified_unsat_correct`, `solveCertified_total` (statements
  preserved verbatim).
  New computable driver entry `LeanFzn.Solver.UIP.solvePhaseCompiled`
  (`LeanFzn/Solver/UIP/Proofs/Search.lean`, over X2's `runPhaseFrom` with the
  compiled package) -> theorems `solvePhaseCompiled_sat_solution`,
  `solvePhaseCompiled_unsat_excludes`, `solvePhaseCompiled_total`, plus
  agreement `solvePhaseCompiled_eq_runReachable`. Its named premises
  (P2 `hpool`, S4/S5 `hdb`, S5 `hbr`) are explicit hypotheses, never
  axioms; the CLI stays on the chronological route where those premises
  cannot be discharged at runtime.
-/

import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Integration.Certified
import LeanFzn.Integration.Chronological
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Integration

/-- The LCG problem of a compiled problem: the same names, domains,
    and constraints, with an empty clause database (the first
    certified fragment needs no clause encoding). -/
def toLCG (problem : CompiledProblem DomConstraint) :
    LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := problem.names
    domains := problem.domains
    constraints := problem.constraints
    objective := ()
    clauses := [] }

/-- The user-facing result of the certified solve command. -/
inductive CliResult where
  /-- A satisfying store, with the certified SAT theorem applicable
      at the source level. -/
  | sat (store : Store)
  /-- Unsatisfiable: every parameter-honest satisfying store is
      excluded. -/
  | unsat
  /-- The model is outside the certified fragment. -/
  | unsupported (reason : String)
  /-- Defensive internal-error case, excluded on accepted models by the totality theorem. -/
  | unknown (reason : String)

/-- Compile, gate finite int/bool domains, and run proved domain propagation
    and lazy clause learning. The explicit frontier remembers unused siblings;
    termination is kernel-checked without fuel. SAT and parameter-honest UNSAT
    have source-level proofs. -/
def solveCertified (m : Model) : CliResult :=
  match compileModel m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match LeanFzn.Solver.Chronological.solve (toLCG problem) DomConstraint.satisfiedB
            (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
              (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem)) with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "internal: fuel-free driver returned unknown"
      else
        .unsupported
          "the model's search space is outside the certified gate \
           (every domain must be a nonempty finite int/bool domain)"

/-- **The source-level SAT theorem of the certified command**: a
    store returned by `solveCertified` satisfies the model (under
    well-formedness — the CLI checks it before calling). Holds for
    every model passing the widened gate: singletons AND multi-value
    domains (the engine's SAT soundness is decision-free). -/
theorem solveCertified_sat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveCertified at hres
  cases hc : compileModel m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only [reduceIte] at hres
      cases hgate : LeanFzn.Solver.Propagation.gateOk (toLCG problem) with
      | true =>
          rw [hgate] at hres
          simp only [reduceIte] at hres
          cases hsolve : LeanFzn.Solver.Chronological.solve (toLCG problem)
              DomConstraint.satisfiedB
              (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
              (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem)) with
          | sat a =>
              rw [hsolve] at hres
              simp only [CliResult.sat.injEq, reduceIte] at hres
              subst hres
              -- the LCG-level theorem (every premise derived; the
              -- widened gate carries multi-value domains)
              have hinternal := LeanFzn.Integration.solve_certified_sat_wide
                (m := m) (problem := toLCG problem) (compiled := problem)
                (hc := hc) (hlcg := rfl) (hcons := rfl)
                (hgate := hgate)
                (hclauses := rfl) (by rw [hsolve])
              obtain ⟨hfits, hcholds⟩ := hinternal
              -- the field agreement + acceptance
              have hacc : accepts problem a = true :=
                List.all_eq_true.mpr (fun c hc2 =>
                  (DomConstraint.satisfiedB_iff c a).mpr (hcholds c hc2))
              have hmem : a ∈ allAssigns problem.domains :=
                fits_mem_allAssigns problem.domains a hfits
              obtain ⟨hcons, hvars⟩ :=
                compile_exact (problem := problem) hc hwf hmem hacc
              -- assemble Satisfies
              refine ⟨hwf, hcons, ?_, ?_⟩
              · intro d hd
                match hdshape : d with
                | .basic ty n anns opt =>
                    exact hvars (.basic ty n anns opt) (hdshape ▸ hd)
                | .array ty n anns elems =>
                    exfalso
                    obtain ⟨ty2, n2, anns2, hshape⟩ :=
                      compileModel_vars_basic hc (.array ty n anns elems) hd
                    cases hshape
              · intro d hd
                obtain ⟨ty, n, anns, hshape⟩ :=
                  compileModel_vars_basic hc d hd
                rw [hshape]
                trivial
          | unsat =>
              rw [hsolve] at hres
              simp only [reduceIte] at hres
              simp at hres
          | unknown => rw [hsolve] at hres; simp at hres
      | false =>
          rw [hgate] at hres
          exact absurd hres (by intro hcon; cases hcon)

/-- **The source-level UNSAT theorem of the certified command**: an
    `unsat` verdict excludes every parameter-honest satisfying
    store. The proof covers every compiled model passing the finite-domain
    gate, including branches requiring decisions and backtracking. -/
theorem solveCertified_unsat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Compiler.ParamHonest m store := by
  unfold solveCertified at hres
  cases hc : compileModel m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only [reduceIte] at hres
      cases hgate : LeanFzn.Solver.Propagation.gateOk (toLCG problem) with
      | true =>
          rw [hgate] at hres
          simp only [reduceIte] at hres
          cases hsolve : LeanFzn.Solver.Chronological.solve (toLCG problem)
              DomConstraint.satisfiedB
              (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
              (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem)) with
          | sat a => rw [hsolve] at hres; simp at hres
          | unsat =>
              -- the WIDE door (the decision-descent master theorem's
              -- composition over ALL twenty registered families —
              -- the fixed propLinLe2's reasons are state-free valid,
              -- so no linLe coverage gate remains) decides the claim
              rw [hsolve] at hres
              rintro ⟨store, ⟨_, hcons2, hvarsS, _⟩, hparam⟩
              -- the LCG-level exclusion (the wide door)
              have hnone := LeanFzn.Integration.solve_certified_unsat_wide
                (m := m) (problem := toLCG problem)
                (compiled := problem)
                (hc := hc) (hlcg := rfl) (hcons := rfl)
                (hgate := hgate)
                (hclauses := rfl) (by rw [hsolve])
              -- the coverage: the store yields an accepted
              -- assignment (the same chain as the fragment door)
              have hvars : ∀ d ∈ m.variables, match d with
                  | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
                  | .array _ _ _ _ => False := by
                intro d hd
                match hdshape : d with
                | .basic ty n anns opt =>
                    exact hvarsS (.basic ty n anns opt) (hdshape ▸ hd)
                | .array ty n anns elems =>
                    exfalso
                    obtain ⟨ty2, n2, anns2, hshape⟩ :=
                      compileModel_vars_basic hc
                        (.array ty n anns elems) hd
                    cases hshape
              obtain ⟨a, hmem, hacc⟩ :=
                compile_covers (problem := problem) hc hwf hcons2
                  hvars hparam
              have hfit : Solver.Core.Assignment.Fits
                  (toLCG problem).toProblem.domains a :=
                ⟨(mem_allAssigns_length problem.domains a hmem),
                  fun i v hv =>
                    mem_allAssigns_fits problem.domains a hmem i v hv⟩
              have hinternal : ProblemSolution (toLCG problem)
                  DomConstraint.SatisfiedBy a :=
                ⟨hfit,
                  fun c hc2 => by
                    have hb : c.satisfiedB a = true :=
                      List.all_eq_true.mp hacc c hc2
                    exact ((DomConstraint.satisfiedB_iff c a).mp hb)⟩
              exact hnone ⟨a, hinternal⟩
          | unknown => rw [hsolve] at hres; simp at hres
      | false =>
          rw [hgate] at hres
          exact absurd hres (by intro hcon; cases hcon)

/-- Emit a solution text for the certified path's satisfying store
    (the FlatZinc convention, ending with the `----------`
    separator). Every declared variable must read a value — the
    SAT theorem guarantees it; a `none` read is a loud failure. -/
def emitCertifiedSolution (m : Model) (store : Store) : String :=
  let entries : List (String × Value) :=
    m.variables.filterMap fun d =>
      match store (VarDeclItem.name d) with
      | some v => some ((VarDeclItem.name d).name, v)
      | none => panic!
        s!"internal error: certified store has no value for            '{(VarDeclItem.name d).name}'"
  LeanFzn.Integration.emitSolution entries

/-- **The source-level total-verdict theorem**: for a model that
    compiles successfully and passes the certified gate, the
    `solve` command returns SAT or UNSAT — never `unknown`. The
    traversal is fuel-free (kernel-checked termination by the
    frontier-cost measure), so no accepted finite model can end
    without a verdict. -/
theorem solveCertified_total {m : Model} {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem)
    (hgate : LeanFzn.Solver.Propagation.gateOk (toLCG problem) = true) :
    ∃ store, solveCertified m = .sat store ∨ solveCertified m = .unsat := by
  unfold solveCertified
  rw [hc]
  simp only [reduceIte, hgate]
  -- the fuel-free driver never returns unknown
  have hnotu : LeanFzn.Solver.Chronological.solve (toLCG problem) DomConstraint.satisfiedB
      (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
              (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem)) ≠ .unknown := by
    exact LeanFzn.Solver.Chronological.solve_total (toLCG problem) DomConstraint.satisfiedB
      (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
      (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem))
  cases hsolve : LeanFzn.Solver.Chronological.solve (toLCG problem) DomConstraint.satisfiedB
      (problem.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
              (LeanFzn.Solver.Propagation.domPruningKit (toLCG problem)) with
  | sat a => exact ⟨problem.toStore a, Or.inl (by simp [hsolve])⟩
  | unsat => exact ⟨fun _ => none, Or.inr (by simp [hsolve])⟩
  | unknown => exact absurd hsolve hnotu

end LeanFzn.Integration
