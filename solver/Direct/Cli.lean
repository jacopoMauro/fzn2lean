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
import solver.LCG.Proofs.Propagators
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

/-- The certified solve command: compile, check the widened LCG gate
    (nonempty finite int/bool-viewed domains — decisions and
    backtracking allowed), run the engine over the proved
    propagators, and report. SAT always carries the source-level
    theorem (the engine's SAT soundness is decision-free). UNSAT is
    CLAIMED only inside the singleton fragment, where the
    decision-free exclusion is proved; outside it an engine
    `.unsat` is reported as `unknown` (no verdict) until the
    decision-descent proof (PLAN.md §3) lands. -/
def solveCertified (m : Model) : CliResult :=
  match compileModel m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LCG.gateOk (toLCG problem) then
        match LCG.solve (toLCG problem) DomConstraint.satisfiedB
            (problem.constraints.filterMap LCG.propagatorOfProved) with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "lcg fuel exhausted"
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
      cases hgate : LCG.gateOk (toLCG problem) with
      | true =>
          rw [hgate] at hres
          simp only [reduceIte] at hres
          cases hsolve : LCG.solve (toLCG problem)
              DomConstraint.satisfiedB
              (problem.constraints.filterMap LCG.propagatorOfProved) with
          | sat a =>
              rw [hsolve] at hres
              simp only [CliResult.sat.injEq, reduceIte] at hres
              subst hres
              -- the LCG-level theorem (every premise derived; the
              -- widened gate carries multi-value domains)
              have hinternal := LCG.solve_certified_sat_wide
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
    store. The command reports `unsat` only inside the singleton
    fragment (where the decision-free exclusion is proved), so the
    theorem's obligation is unchanged. -/
theorem solveCertified_unsat_correct {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      ParamHonest m store := by
  unfold solveCertified at hres
  cases hc : compileModel m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only [reduceIte] at hres
      cases hgate : LCG.gateOk (toLCG problem) with
      | true =>
          rw [hgate] at hres
          simp only [reduceIte] at hres
          cases hsolve : LCG.solve (toLCG problem)
              DomConstraint.satisfiedB
              (problem.constraints.filterMap LCG.propagatorOfProved) with
          | sat a => rw [hsolve] at hres; simp at hres
          | unsat =>
              -- the WIDE door (the decision-descent master theorem's
              -- composition over ALL twenty registered families —
              -- the fixed propLinLe2's reasons are state-free valid,
              -- so no linLe coverage gate remains) decides the claim
              rw [hsolve] at hres
              rintro ⟨store, ⟨_, hcons2, hvarsS, _⟩, hparam⟩
              -- the LCG-level exclusion (the wide door)
              have hnone := LCG.solve_certified_unsat_wide
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
  LeanFzn.Solver.emitSolution entries

end LeanFzn.Solver.Direct
