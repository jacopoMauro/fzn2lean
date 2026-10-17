/-
Purpose: compose certified compiled search with the array front end and
source-model correspondence. Supported integer LCG families run through the
fuel-free first-UIP phase kernel; other accepted models use the proved
chronological fallback. SAT/UNSAT/totality meanings are preserved.
Dependencies: Integration.Lcg supplies compiled verdict proofs; compiler
normalization and exactness transport assignments to source stores; Emit and
Checker supply output conventions.
DAG: compiler + certified search -> this source entry -> CLI/optimization.
-/

import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Integration.Certified
import LeanFzn.Integration.Chronological
import LeanFzn.Integration.Lcg
import LeanFzn.Integration.LcgHeur
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Checker.Check
import LeanFzn.Integration.Emit
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Integration

/-- Shared compiled problem representation for the certified search routes. -/
abbrev toLCG := lcgProblem

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
  match compileModelFull m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match LcgHeur.solveCompiledLcgHeur problem with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "internal: fuel-free driver returned unknown"
      else
        .unsupported
          "the model's search space is outside the certified gate \
           (every domain must be a nonempty finite int/bool domain)"

/-- The public certified route returns a source-model satisfying store. -/
theorem solveCertified_sat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveCertified at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : LcgHeur.solveCompiledLcgHeur problem with
        | sat a =>
            rw [hs] at hres
            cases hres
            obtain ⟨hm, ha⟩ := LcgHeur.solveCompiledLcgHeur_sat hs
            exact ⟨hwf, (compileFull_exact hc hwf hm ha).1⟩
        | unsat => rw [hs] at hres; cases hres
        | unknown => rw [hs] at hres; cases hres
      · cases hres

/-- An UNSAT result excludes every parameter-honest satisfying source store. -/
theorem solveCertified_unsat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  unfold solveCertified at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : LcgHeur.solveCompiledLcgHeur problem with
        | sat a => rw [hs] at hres; cases hres
        | unsat =>
            rintro ⟨store, hsat, hp⟩
            obtain ⟨a, hm, ha⟩ := compileFull_covers hc hwf hsat.2 hp
            have hn := LcgHeur.solveCompiledLcgHeur_unsat hs a hm
            rw [ha] at hn
            cases hn
        | unknown => rw [hs] at hres; cases hres
      · cases hres

/-- Emit a solution text for the certified path's satisfying store
    (the FlatZinc convention, ending with the `----------`
    separator). Every declared variable must read a value — the
    SAT theorem guarantees it; a `none` read is a loud failure. -/
def certifiedEntries (m : Model) (store : Store) : List String :=
  m.variables.filterMap fun d =>
    match store (VarDeclItem.name d) with
    | some v => some (emitDeclEntry d v)
    | none => panic!
      s!"internal error: certified store has no value for \
         '{(VarDeclItem.name d).name}'"

/-- One complete solution text (entries then the separator). An
    optimisation driver (O1) can concatenate several of these and append
    `optimumMarker`. -/
def emitCertifiedSolution (m : Model) (store : Store) : String :=
  let entries := certifiedEntries m store
  "\n".intercalate entries ++ (if entries.isEmpty then "" else "\n") ++ solutionSeparator

/-- Gate-passing compiled sources always receive SAT or UNSAT, without fuel. -/
theorem solveCertified_total {m : Model} {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hgate : LeanFzn.Solver.Propagation.gateOk (toLCG problem) = true) :
    ∃ store, solveCertified m = .sat store ∨ solveCertified m = .unsat := by
  unfold solveCertified
  rw [hc]
  simp only [hgate, if_true]
  cases hs : LcgHeur.solveCompiledLcgHeur problem with
  | sat a => exact ⟨problem.toStore a, Or.inl rfl⟩
  | unsat => exact ⟨fun _ => none, Or.inr rfl⟩
  | unknown => exact False.elim (LcgHeur.solveCompiledLcgHeur_verdict problem hs)

end LeanFzn.Integration
