/-
Purpose: Core-only optional certified preprocessing entries (PLAN P7.1).
Dependencies: Engine.Search, Compiler.Preprocess and the public configuration.
DAG: compiler semantics -> certified presolve -> public solver/optimizer entries.
The presolve mode is policy only: it transforms the problem before search and
every result is mapped back through the proved acceptance equivalence.
-/
import LeanFzn.Engine.Search
import LeanFzn.Compiler.Preprocess

namespace LeanFzn.Core
open LeanFzn LeanFzn.Engine LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Integration

/-- Apply the selected certified preprocessing mode.  `none` (and the
kernel-only `root` mode, which Core rejects) are the identity; `dedup`
keeps the first occurrence of every syntactically identical constraint. -/
def presolveProblem (o : SearchConfig) (p : CompiledProblem DomConstraint) :
    CompiledProblem DomConstraint :=
  match o.presolve with
  | .dedup => p.preprocess
  | .none => p
  | .root => p

@[simp] theorem presolveProblem_domains (o : SearchConfig)
    (p : CompiledProblem DomConstraint) :
    (presolveProblem o p).domains = p.domains := by
  unfold presolveProblem
  split <;> rfl

@[simp] theorem presolveProblem_names (o : SearchConfig)
    (p : CompiledProblem DomConstraint) :
    (presolveProblem o p).names = p.names := by
  unfold presolveProblem
  split <;> rfl

@[simp] theorem presolveProblem_source (o : SearchConfig)
    (p : CompiledProblem DomConstraint) :
    (presolveProblem o p).source = p.source := by
  unfold presolveProblem
  split <;> rfl

@[simp] theorem presolveProblem_toStore (o : SearchConfig)
    (p : CompiledProblem DomConstraint) :
    (presolveProblem o p).toStore = p.toStore := by
  unfold presolveProblem
  split <;> rfl

@[simp] theorem presolveProblem_objective (o : SearchConfig)
    (p : CompiledProblem DomConstraint) :
    (presolveProblem o p).objective = p.objective := by
  unfold presolveProblem
  split <;> rfl

/-- The acceptance predicate is unchanged by the certified presolve modes. -/
theorem accepts_presolveProblem (o : SearchConfig)
    (p : CompiledProblem DomConstraint) (a : List LeanFzn.Semantics.Value) :
    accepts (presolveProblem o p) a = true ↔ accepts p a = true := by
  unfold presolveProblem
  split
  · exact accepts_preprocess p a
  · rfl
  · rfl

/-- Core's fuel-bounded entry after optional certified preprocessing. -/
def coreSolveFullPre (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) : CoreResult × EngineStats :=
  coreSolveFullWith (presolveProblem o p) o prev fuel

/-- Core's fuel-bounded entry after optional certified preprocessing, with an
already converted domain array for the preprocessed problem. -/
def coreSolveFullPrePrepared (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) (doms : Array DomC)
    (hconv : convertDomains (presolveProblem o p).domains = some doms) :
    CoreResult × EngineStats :=
  coreSolveFullWithPrepared (presolveProblem o p) o prev fuel doms hconv

/-- The prepared preprocessed entry equals the ordinary one. -/
theorem coreSolveFullPrePrepared_eq (p : CompiledProblem DomConstraint)
    (o : SearchConfig) (prev : Option (List Value)) (fuel : Nat)
    (doms : Array DomC)
    (hconv : convertDomains (presolveProblem o p).domains = some doms) :
    coreSolveFullPrePrepared p o prev fuel doms hconv = coreSolveFullPre p o prev fuel := by
  unfold coreSolveFullPrePrepared coreSolveFullPre
  exact coreSolveFullWithPrepared_eq _ o prev fuel doms hconv

/-- Core's verdict after optional certified preprocessing. -/
def coreSolvePre (p : CompiledProblem DomConstraint) (o : SearchConfig)
    (prev : Option (List Value)) (fuel : Nat) : CoreResult :=
  (coreSolveFullPre p o prev fuel).1

/-- Core's SAT soundness after optional certified preprocessing. -/
theorem coreSolveFullPre_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat} {a : List Value}
    {st : EngineStats}
    (h : coreSolveFullPre p o prev fuel = (.sat a, st)) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  have hfst : (coreSolveFullPre p o prev fuel).1 = .sat a := by
    rw [h]
  have hq := coreSolveFullWith_sat hfst
  exact ⟨by simpa [presolveProblem_domains] using hq.1,
    (accepts_presolveProblem o p a).mp hq.2⟩

/-- Core's SAT soundness for the verdict-only preprocessed entry. -/
theorem coreSolvePre_sat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat} {a : List Value}
    (h : coreSolvePre p o prev fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreSolvePre at h
  cases hf : coreSolveFullPre p o prev fuel with
  | mk r st =>
      cases r with
      | sat a' =>
          simp [hf] at h
          cases h
          exact coreSolveFullPre_sat hf
      | unsat => simp [hf] at h
      | gaveUp => simp [hf] at h

/-- Core's UNSAT soundness after optional certified preprocessing. -/
theorem coreSolveFullPre_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    {st : EngineStats}
    (h : coreSolveFullPre p o prev fuel = (.unsat, st)) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro b hb
  have hbq : b ∈ allAssigns (presolveProblem o p).domains := by
    simpa [presolveProblem_domains] using hb
  have hfst : (coreSolveFullPre p o prev fuel).1 = .unsat := by
    rw [h]
  have hq := coreSolveFullWith_unsat hfst b hbq
  by_cases hp : accepts p b = true
  · have hqtrue : accepts (presolveProblem o p) b = true :=
      (accepts_presolveProblem o p b).mpr hp
    rw [hq] at hqtrue
    exact Bool.noConfusion hqtrue
  · cases h : accepts p b with
    | false => rfl
    | true => exact absurd h hp

/-- Core's UNSAT soundness for the verdict-only preprocessed entry. -/
theorem coreSolvePre_unsat {p : CompiledProblem DomConstraint}
    {o : SearchConfig} {prev : Option (List Value)} {fuel : Nat}
    (h : coreSolvePre p o prev fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreSolvePre at h
  cases hf : coreSolveFullPre p o prev fuel with
  | mk r st =>
      cases r with
      | sat a' => simp [hf] at h
      | unsat => exact coreSolveFullPre_unsat hf
      | gaveUp => simp [hf] at h

end LeanFzn.Core
