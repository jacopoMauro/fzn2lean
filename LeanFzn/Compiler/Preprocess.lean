/-
File: LeanFzn/Compiler/Preprocess.lean

Purpose:
  Optional certified preprocessing for compiled Core problems (PLAN P7.1).
  The first, deliberately small step canonicalises duplicate constraints:
  two syntactically identical `DomConstraint`s contribute the same leaf
  predicate, so keeping the first occurrence preserves the accepted-assignment
  set exactly.  The objective slot, source model and reconstruction store are
  untouched, so every objective value is preserved as well.

  The operation is a pure transformation of `CompiledProblem`; callers choose
  it through `--presolve=dedup`.  The uncompiled source model and the
  `toStore` reconstruction map are never modified.

Dependencies:
  - LeanFzn.Compiler.Compile: `CompiledProblem`, `accepts`.
  - LeanFzn.Solver.Core.Enumerate: `allAssigns`.

DAG:
  compiler semantics -> certified preprocessing -> public solver entries.
-/
import LeanFzn.Compiler.Compile
import LeanFzn.Solver.Core.Enumerate
import Std.Data.HashSet.Lemmas

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.Core

/-! ## Deduplication with a lawful Boolean equality -/

/-- The structural equality on `DomConstraint` used by deduplication.  The
underlying `DecidableEq` instance is derived from the representation; this
`BEq` instance is lawful by construction. -/
instance : BEq DomConstraint := ⟨fun a b => decide (a = b)⟩

instance : ReflBEq DomConstraint where
  rfl := by intro a; simp

instance : LawfulBEq DomConstraint where
  eq_of_beq := by intro a b h; simpa using h

/-! ### Hashing vocabulary

The linear-time deduplication needs a hash for each constraint and the values
it contains.  The instances are derived here rather than on the model types so
that `LeanFzn/Semantics` and the engine representation stay untouched. -/

deriving instance Hashable for LeanFzn.Semantics.IntSetValue
deriving instance Hashable for LeanFzn.Semantics.Value
deriving instance Hashable for DomIntArg
deriving instance Hashable for DomConstraint

/-- Hash-set deduplication: `seen` holds the elements already emitted, `as` the
elements still to visit.  This is the linear-time twin of `List.eraseDups`. -/
def dedupGo (seen : Std.HashSet DomConstraint) : List DomConstraint → List DomConstraint
  | [] => []
  | a :: as => if a ∈ seen then dedupGo seen as else a :: dedupGo (seen.insert a) as

/-- The hash-set loop emits exactly the elements of `as` that are not in
`seen`, deduplicated in first-occurrence order. -/
theorem dedupGo_eq (seen : Std.HashSet DomConstraint) (as : List DomConstraint) :
    dedupGo seen as = (as.filter fun b => b ∉ seen).eraseDups := by
  induction as generalizing seen with
  | nil => rfl
  | cons a as ih =>
    rw [dedupGo]
    by_cases h : a ∈ seen
    · rw [ite_eq_left h, List.filter_cons_of_neg (by simpa using h), ih]
    · rw [ite_eq_right h, ih (seen.insert a), List.filter_cons_of_pos (by simpa using h),
        List.eraseDups_cons]
      apply congrArg (List.cons a)
      apply congrArg List.eraseDups
      rw [List.filter_filter]
      apply List.filter_congr
      intro b _
      by_cases hb : b = a
      · subst hb
        simp
      · have hba : (b == a) = false := by simp [hb]
        have hab : (a == b) = false := by simp [Ne.symm hb]
        simp [Std.HashSet.mem_insert, hba, hab]

/-- Remove later occurrences of an element, keeping the first occurrence in
order. -/
def dedupList (as : List DomConstraint) : List DomConstraint :=
  dedupGo ∅ as

/-- The hash-set implementation is extensionally the `List.eraseDups`
specification: the same elements survive in the same order. -/
theorem dedupList_eq (as : List DomConstraint) :
    dedupList as = as.eraseDups := by
  unfold dedupList
  rw [dedupGo_eq]
  apply congrArg List.eraseDups
  rw [List.filter_eq_self]
  intro b _
  simp

/-- Deduplication does not change membership. -/
theorem mem_dedupList (as : List DomConstraint) (x : DomConstraint) :
    x ∈ dedupList as ↔ x ∈ as := by
  rw [dedupList_eq]
  exact List.mem_eraseDups

/-- A Boolean universal test is unchanged by deduplication. -/
theorem all_dedupList (as : List DomConstraint) (q : DomConstraint → Bool) :
    (dedupList as).all q = true ↔ as.all q = true := by
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    exact h x ((mem_dedupList as x).mpr hx)
  · intro h x hx
    exact h x ((mem_dedupList as x).mp hx)

/-! ## Problem preprocessing -/

/-- Canonicalise duplicate constraints, keeping the first occurrence. -/
def CompiledProblem.preprocess (p : CompiledProblem DomConstraint) :
    CompiledProblem DomConstraint :=
  { p with constraints := dedupList p.constraints }

@[simp] theorem preprocess_names (p : CompiledProblem DomConstraint) :
    p.preprocess.names = p.names := rfl

@[simp] theorem preprocess_domains (p : CompiledProblem DomConstraint) :
    p.preprocess.domains = p.domains := rfl

@[simp] theorem preprocess_objective (p : CompiledProblem DomConstraint) :
    p.preprocess.objective = p.objective := rfl

@[simp] theorem preprocess_source (p : CompiledProblem DomConstraint) :
    p.preprocess.source = p.source := rfl

@[simp] theorem preprocess_toStore (p : CompiledProblem DomConstraint) :
    p.preprocess.toStore = p.toStore := rfl

@[simp] theorem preprocess_domainsArray (p : CompiledProblem DomConstraint) :
    p.preprocess.domainsArray = p.domainsArray := rfl

/-- The accepted assignments of a preprocessed problem are exactly those of
the original problem. -/
theorem accepts_preprocess (p : CompiledProblem DomConstraint)
    (a : List LeanFzn.Semantics.Value) :
    accepts p.preprocess a = true ↔ accepts p a = true := by
  unfold accepts CompiledProblem.preprocess
  exact all_dedupList p.constraints (fun c => c.satisfiedB a)

theorem accepts_preprocess_forward (p : CompiledProblem DomConstraint)
    (a : List LeanFzn.Semantics.Value)
    (h : accepts p.preprocess a = true) : accepts p a = true :=
  (accepts_preprocess p a).mp h

theorem accepts_preprocess_backward (p : CompiledProblem DomConstraint)
    (a : List LeanFzn.Semantics.Value)
    (h : accepts p a = true) : accepts p.preprocess a = true :=
  (accepts_preprocess p a).mpr h

/-- Preprocessing preserves both the search box and the acceptance predicate;
this is the complete solution-set equivalence used by the public solver. -/
theorem preprocess_solution_iff (p : CompiledProblem DomConstraint)
    (a : List LeanFzn.Semantics.Value) :
    (a ∈ allAssigns p.preprocess.domains ∧ accepts p.preprocess a = true) ↔
      (a ∈ allAssigns p.domains ∧ accepts p a = true) := by
  rw [preprocess_domains, accepts_preprocess]

/-- Duplicate constraints are exactly the removed elements; the surviving
list is a subset of the original. -/
theorem preprocess_constraints_subset (p : CompiledProblem DomConstraint) :
    ∀ c, c ∈ p.preprocess.constraints → c ∈ p.constraints := by
  intro c hc
  exact (mem_dedupList p.constraints c).mp hc

/-- Every original constraint is represented in the preprocessed problem. -/
theorem preprocess_constraints_complete (p : CompiledProblem DomConstraint) :
    ∀ c, c ∈ p.constraints → c ∈ p.preprocess.constraints := by
  intro c hc
  exact (mem_dedupList p.constraints c).mpr hc

end LeanFzn.Compiler
