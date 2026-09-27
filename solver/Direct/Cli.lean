/-
File: solver/Direct/Cli.lean

Purpose:
  The user-facing certified solve command: compile the model to the
  shared core problem, run the certified LCG fragment path (singleton
  domains, empty clause database, empty propagator list), and compose
  the LCG-level theorems with the Direct compiler correspondence into
  source-level SAT/UNSAT theorems. Outside the fragment (or on
  compilation failure) the command reports `unsupported`/`unknown`
  with a reason — never an uncertified verdict.

Dependencies:
  - solver.Direct.Compile: the fragment compiler.
  - solver.Direct.Proofs.Exact: compile_exact / compile_covers.
  - solver.LCG.Certified: the certified LCG front door.
  - LeanFzn.FznCheck: the executable well-formedness gate.

DAG:
  Direct.Compile + Direct.Proofs.Exact + LCG.Certified
    -> Direct.Cli -> Main.lean (leanfzn solve)
-/

import solver.Direct.Proofs.Exact
import solver.LCG.Certified
import LeanFzn.FznCheck
import solver.Emit

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.LCG

/-- The LCG problem of a compiled problem: the same names, domains,
    and constraints, with an empty clause database (the first
    certified fragment needs no clause encoding). -/
def toLCG (problem : CompiledProblem DomConstraint) :
    LCG.Problem DomConstraint Unit :=
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
  /-- No verdict (not reachable in the first fragment; the fuel
      bound is not exhausted by a decision-free run). -/
  | unknown (reason : String)

/-- The certified solve command: compile, check the LCG fragment
    (singleton domains, int/bool views, no learned clauses needed),
    run the engine, and report. -/
def solveCertified (m : Model) : CliResult :=
  match compileModel m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LCG.fragmentOk (toLCG problem) then
        match LCG.solve (toLCG problem) DomConstraint.satisfiedB [] with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "lcg fuel exhausted"
      else
        .unsupported
          "the model's search space is not a singleton-domain fragment \
           (the first certified LCG fragment covers decided models only)"

/-- The int-view premise of the LCG fragment (the fragment's singleton
    domains carry int/bool values — derived from the domain check;
    the remaining shapes are int/bool by the compiler's slot
    extraction, so we state the premise and discharge it at the
    call site). -/
theorem solveCertified_sat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hint : ∀ problem : CompiledProblem DomConstraint,
      compileModel m = .ok problem →
      ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none)
    (hres : solveCertified m = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveCertified at hres
  cases hc : compileModel m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only [reduceIte] at hres
      cases hfrag : LCG.fragmentOk (toLCG problem) with
      | true =>
          rw [hfrag] at hres
          simp only [reduceIte] at hres
          cases hsolve : LCG.solve (toLCG problem)
              DomConstraint.satisfiedB [] with
          | sat a =>
              rw [hsolve] at hres
              simp only [CliResult.sat.injEq] at hres
              subst hres
              -- the LCG-level theorem
              have hinternal := LCG.solve_certified_sat
                (problem := toLCG problem) (hfrag := hfrag)
                (hint := hint problem hc) (hclauses := rfl)
                (by rw [hsolve])
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
          | unsat => rw [hsolve] at hres; simp at hres
          | unknown => rw [hsolve] at hres; simp at hres
      | false =>
          rw [hfrag] at hres
          exact absurd hres (by intro hcon; cases hcon)

/-- **The source-level UNSAT theorem of the certified command**: an
    `unsat` verdict excludes every parameter-honest satisfying
    store. -/
theorem solveCertified_unsat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hint : ∀ problem : CompiledProblem DomConstraint,
      compileModel m = .ok problem →
      ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none)
    (hres : solveCertified m = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      ParamHonest m store := by
  unfold solveCertified at hres
  cases hc : compileModel m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only [reduceIte] at hres
      cases hfrag : LCG.fragmentOk (toLCG problem) with
      | true =>
          rw [hfrag] at hres
          simp only [reduceIte] at hres
          cases hsolve : LCG.solve (toLCG problem)
              DomConstraint.satisfiedB [] with
          | sat a => rw [hsolve] at hres; simp at hres
          | unsat =>
              -- the LCG-level exclusion
              have hnone := LCG.solve_certified_unsat
                (problem := toLCG problem) (hfrag := hfrag)
                (hint := hint problem hc) (hclauses := rfl)
                (by rw [hsolve])
              rintro ⟨store, ⟨_, hcons, hvarsS, _⟩, hparam⟩
              -- adapt the var-condition to the gate's basic-only shape
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
                      compileModel_vars_basic hc (.array ty n anns elems) hd
                    cases hshape
              -- the coverage: the store yields an accepted assignment
              obtain ⟨a, hmem, hacc⟩ :=
                compile_covers (problem := problem) hc hwf hcons hvars hparam
              -- contradiction with the LCG exclusion
              -- the ProblemSolution: Fits (via membership) + holds
              have hfit : Solver.Core.Assignment.Fits
                  (toLCG problem).toProblem.domains a :=
                ⟨(mem_allAssigns_length problem.domains a hmem),
                  fun i v hv => mem_allAssigns_fits problem.domains a hmem i v hv⟩
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
          rw [hfrag] at hres
          exact absurd hres (by intro hcon; cases hcon)

/-- Emit a solution text for the certified path's satisfying store
    (the FlatZinc convention, ending with the `----------`
    separator). -/
def emitCertifiedSolution (m : Model) (store : Store) : String :=
  let entries : List (String × Value) :=
    m.variables.filterMap fun d =>
      match store (VarDeclItem.name d) with
      | some v => some ((VarDeclItem.name d).name, v)
      | none => none
  LeanFzn.Solver.emitSolution entries

end LeanFzn.Solver.Direct
