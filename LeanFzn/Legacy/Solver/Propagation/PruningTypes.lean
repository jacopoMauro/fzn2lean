/- Shared refinement contracts and observations, independent of search strategy. -/
import LeanFzn.Solver.Propagation.FrontierSemantics
import LeanFzn.Solver.Propagation.Operations
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

structure SearchStats where
  /-- Executed scheduler transitions (K0 `--stats` throughput counter). -/
  steps : Nat := 0
  /-- Choices with more than one remaining value; forced singleton descent is not a decision. -/
  decisions : Nat := 0
  propagations : Nat := 0
  conflicts : Nat := 0
  learnedClauses : Nat := 0
  checkedLeaves : Nat := 0
  /-- Value-reducing unit deductions from learned clauses; excludes database-conflict pops. -/
  learnedPrunes : Nat := 0
  deriving Repr, BEq

def SearchStats.add (a b : SearchStats) : SearchStats :=
  ⟨a.steps+b.steps, a.decisions+b.decisions, a.propagations+b.propagations,
   a.conflicts+b.conflicts, a.learnedClauses+b.learnedClauses,
   a.checkedLeaves+b.checkedLeaves, a.learnedPrunes+b.learnedPrunes⟩

structure Refinement where
  frame : Option PrefixFrame
  learned : List Clause := []
  stats : SearchStats := {}

/-- The sparse scheduled refinement output (M3): the positional `Refinement`
record's sparse counterpart, carrying the sparse frame the scheduled closure
produces. -/
structure SparseRefinement where
  frame : Option BranchFrame
  learned : List Clause := []
  stats : SearchStats := {}

def EntailedDB (leaf : Assignment → Bool) (db : List Clause) : Prop :=
  ∀ c ∈ db, ∀ a, leaf a = true → c.SatisfiedBy a

structure PruningKit (leaf : Assignment → Bool) where
  run : PrefixFrame → List Clause → Refinement
  cost_le : ∀ f db g, (run f db).frame = some g → branchCost g.1 ≤ branchCost f.1
  preserves : ∀ f db, EntailedDB leaf db → ∀ a, leaf a = true → PrefixCovers f a →
    ∃ g, (run f db).frame = some g ∧ PrefixCovers g a
  learns : ∀ f db, EntailedDB leaf db → EntailedDB leaf (run f db).learned

theorem refined_pop_lt (f g : PrefixFrame) (rest : List PrefixFrame)
    (_h : branchCost g.1 ≤ branchCost f.1) : frontierCost rest < frontierCost (f::rest) :=
  frontierCost_cons f rest

theorem refined_expand_lt (f : PrefixFrame) (v : Value) (vs : List Value)
    (d : Domain) (hd : d.enum = v :: vs) (doms : List Domain)
    (chosen : Assignment) (rest : List PrefixFrame)
    (h : branchCost (d :: doms) ≤ branchCost f.1) :
    frontierCost ((doms, chosen ++ [v]) ::
        (Dom.ofList vs :: doms, chosen) :: rest) < frontierCost (f :: rest) := by
  have he := frontierCost_expand v vs d hd doms chosen rest
  simp only [frontierCost, List.map_cons, List.sum_cons] at he ⊢
  omega


end LeanFzn.Solver.Propagation
