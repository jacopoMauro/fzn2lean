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
import LeanFzn.Legacy.Integration.Kernel.Certified
import LeanFzn.Legacy.Integration.Kernel.Chronological
import LeanFzn.Legacy.Integration.Kernel.Annot
import LeanFzn.Legacy.Integration.Solve.Core
import LeanFzn.Legacy.Integration.Kernel.Lcg
import LeanFzn.Legacy.Solver.Propagation.Proofs.Propagators
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

/-- The refusal reason for a model outside the certified search gate. -/
def gateRefusal : String :=
  "the model's search space is outside the certified gate \
   (every domain must be a nonempty finite int/bool domain)"

/-- Compile, gate finite int/bool domains, and run proved domain propagation
    and lazy clause learning. The explicit frontier remembers unused siblings;
    termination is kernel-checked without fuel. SAT and parameter-honest UNSAT
    have source-level proofs. `o` selects the LCG branch's search
    heuristics (`SearchConfig`; default: the unchanged route); every
    choice is certified. -/
def solveCertified (m : Model) (o : SearchConfig := {}) : CliResult :=
  match compileModelFull m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match solveSearchConfig problem o with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "internal: fuel-free driver returned unknown"
      else
        .unsupported gateRefusal

/-- Stats twin of `solveCertified` (K0): the same certified route, returning
the terminal engine counters beside the verdict. The counters are observations
only; `solveCertifiedStats_fst` proves the verdict component unchanged. -/
def solveCertifiedStats (m : Model) (o : SearchConfig := {}) :
    CliResult × SearchStats :=
  match compileModelFull m with
  | .error reason => (.unsupported reason, {})
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match solveSearchConfigStats problem o with
        | (.sat a, st) => (.sat (problem.toStore a), st)
        | (.unsat, st) => (.unsat, st)
        | (.unknown, st) =>
            (.unknown "internal: fuel-free driver returned unknown", st)
      else
        (.unsupported gateRefusal, {})

/-- The instrumented certified route decides exactly `solveCertified`. -/
theorem solveCertifiedStats_fst (m : Model) (o : SearchConfig := {}) :
    (solveCertifiedStats m o).1 = solveCertified m o := by
  unfold solveCertifiedStats solveCertified
  cases hc : compileModelFull m with
  | error reason => rfl
  | ok problem =>
      simp only
      by_cases hg : LeanFzn.Solver.Propagation.gateOk (toLCG problem) = true
      · rw [if_pos hg, if_pos hg]
        cases h : solveSearchConfig problem o with
        | sat a =>
            have hs := solveSearchConfigStats_fst problem o
            rw [h] at hs
            cases hstats : solveSearchConfigStats problem o with
            | mk r st =>
                rw [hstats] at hs
                subst hs
                rfl
        | unsat =>
            have hs := solveSearchConfigStats_fst problem o
            rw [h] at hs
            cases hstats : solveSearchConfigStats problem o with
            | mk r st =>
                rw [hstats] at hs
                subst hs
                rfl
        | unknown =>
            have hs := solveSearchConfigStats_fst problem o
            rw [h] at hs
            cases hstats : solveSearchConfigStats problem o with
            | mk r st =>
                rw [hstats] at hs
                subst hs
                rfl
      · rw [if_neg hg, if_neg hg]

/-- The public certified route returns a source-model satisfying store. -/
theorem solveCertified_sat_correct {o : SearchConfig} {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m o = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveCertified at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : solveSearchConfig problem o with
        | sat a =>
            rw [hs] at hres
            cases hres
            obtain ⟨hm, ha⟩ := solveSearchConfig_sat hs
            exact ⟨hwf, (compileFull_exact hc hwf hm ha).1⟩
        | unsat => rw [hs] at hres; cases hres
        | unknown => rw [hs] at hres; cases hres
      · cases hres

/-- An UNSAT result excludes every parameter-honest satisfying source store. -/
theorem solveCertified_unsat_correct {o : SearchConfig} {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertified m o = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  unfold solveCertified at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : solveSearchConfig problem o with
        | sat a => rw [hs] at hres; cases hres
        | unsat =>
            rintro ⟨store, hsat, hp⟩
            obtain ⟨a, hm, ha⟩ := compileFull_covers hc hwf hsat.2 hp
            have hn := solveSearchConfig_unsat hs a hm
            rw [ha] at hn
            cases hn
        | unknown => rw [hs] at hres; cases hres
      · cases hres

/-- Gate-passing compiled sources always receive SAT or UNSAT, without fuel. -/
theorem solveCertified_total {o : SearchConfig} {m : Model} {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hgate : LeanFzn.Solver.Propagation.gateOk (toLCG problem) = true) :
    ∃ store, solveCertified m o = .sat store ∨ solveCertified m o = .unsat := by
  unfold solveCertified
  rw [hc]
  simp only [hgate, if_true]
  cases hs : solveSearchConfig problem o with
  | sat a => exact ⟨problem.toStore a, Or.inl rfl⟩
  | unsat => exact ⟨fun _ => none, Or.inr rfl⟩
  | unknown => exact False.elim (solveSearchConfig_verdict problem o hs)

/-! ## The Core-engine source route (N9) -/

section CoreSeam
open LeanFzn.Engine

/-- Compile, gate, and run the array-based Core engine.  An internal Core
    `.gaveUp` falls back inside `solveSearchConfigCore` to the already
    certified kernel route, so every verdict still carries the theorem of
    the entry that produced it. -/
def solveCertifiedCore (m : Model) (o : SearchConfig := {}) : CliResult :=
  match compileModelFull m with
  | .error reason => .unsupported reason
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match solveSearchConfigCore problem o with
        | .sat a => .sat (problem.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "internal: Core driver returned unknown"
      else
        .unsupported gateRefusal

/-- Stats twin of `solveCertifiedCore`: the terminal `EngineStats` of the
    identical Core run (or of its kernel fallback). -/
def solveCertifiedCoreStats (m : Model) (o : SearchConfig := {}) :
    CliResult × EngineStats :=
  match compileModelFull m with
  | .error reason => (.unsupported reason, {})
  | .ok problem =>
      if LeanFzn.Solver.Propagation.gateOk (toLCG problem) then
        match solveSearchConfigCoreFull problem o with
        | (.sat a, st) => (.sat (problem.toStore a), st)
        | (.unsat, st) => (.unsat, st)
        | (.unknown, st) =>
            (.unknown "internal: Core driver returned unknown", st)
      else
        (.unsupported gateRefusal, {})

/-- The stats twin decides exactly `solveCertifiedCore`. -/
theorem solveCertifiedCoreStats_fst (m : Model) (o : SearchConfig := {}) :
    (solveCertifiedCoreStats m o).1 = solveCertifiedCore m o := by
  unfold solveCertifiedCoreStats solveCertifiedCore
  cases hc : compileModelFull m with
  | error reason => rfl
  | ok problem =>
      simp only
      by_cases hg : LeanFzn.Solver.Propagation.gateOk (toLCG problem) = true
      · rw [if_pos hg, if_pos hg]
        cases h : solveSearchConfigCoreFull problem o with
        | mk r st =>
            have hf := solveSearchConfigCoreFull_fst problem o
            rw [h] at hf
            simp only at hf
            rw [← hf]
            cases r <;> rfl
      · rw [if_neg hg, if_neg hg]

/-- A Core SAT result yields a satisfying source-model store. -/
theorem solveCertifiedCore_sat_correct {o : SearchConfig} {m : Model} {store : Store}
    (hwf : WellFormed fullSig m)
    (hres : solveCertifiedCore m o = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveCertifiedCore at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : solveSearchConfigCore problem o with
        | sat a =>
            rw [hs] at hres
            cases hres
            obtain ⟨hm, ha⟩ := solveSearchConfigCore_sat hs
            exact ⟨hwf, (compileFull_exact hc hwf hm ha).1⟩
        | unsat => rw [hs] at hres; cases hres
        | unknown => rw [hs] at hres; cases hres
      · cases hres

/-- A Core UNSAT result excludes every parameter-honest satisfying source
    store. -/
theorem solveCertifiedCore_unsat_correct {o : SearchConfig} {m : Model}
    (hwf : WellFormed fullSig m)
    (hres : solveCertifiedCore m o = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  unfold solveCertifiedCore at hres
  cases hc : compileModelFull m with
  | error reason => rw [hc] at hres; simp at hres
  | ok problem =>
      rw [hc] at hres
      simp only at hres
      split at hres
      · cases hs : solveSearchConfigCore problem o with
        | sat a => rw [hs] at hres; cases hres
        | unsat =>
            rintro ⟨store, hsat, hp⟩
            obtain ⟨a, hm, ha⟩ := compileFull_covers hc hwf hsat.2 hp
            have hn := solveSearchConfigCore_unsat hs a hm
            rw [ha] at hn
            cases hn
        | unknown => rw [hs] at hres; cases hres
      · cases hres

end CoreSeam

end LeanFzn.Integration
