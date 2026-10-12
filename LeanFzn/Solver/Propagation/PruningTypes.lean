/- Shared refinement contracts and observations, independent of search strategy. -/
import LeanFzn.Solver.Propagation.FrontierSemantics
import LeanFzn.Solver.Propagation.Operations
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

structure SearchStats where
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
  ⟨a.decisions+b.decisions, a.propagations+b.propagations,
   a.conflicts+b.conflicts, a.learnedClauses+b.learnedClauses,
   a.checkedLeaves+b.checkedLeaves, a.learnedPrunes+b.learnedPrunes⟩

structure Refinement where
  frame : Option BranchFrame
  learned : List Clause := []
  stats : SearchStats := {}

def EntailedDB (leaf : Assignment → Bool) (db : List Clause) : Prop :=
  ∀ c ∈ db, ∀ a, leaf a = true → c.SatisfiedBy a

structure PruningKit (leaf : Assignment → Bool) where
  run : BranchFrame → List Clause → Refinement
  cost_le : ∀ f db g, (run f db).frame = some g → branchCost g.1 ≤ branchCost f.1
  preserves : ∀ f db, EntailedDB leaf db → ∀ a, leaf a = true → FrameCovers f a →
    ∃ g, (run f db).frame = some g ∧ FrameCovers g a
  learns : ∀ f db, EntailedDB leaf db → EntailedDB leaf (run f db).learned

theorem refined_pop_lt (f g : BranchFrame) (rest : List BranchFrame)
    (_h : branchCost g.1 ≤ branchCost f.1) : frontierCost rest < frontierCost (f::rest) :=
  frontierCost_cons f rest

theorem refined_expand_lt (f : BranchFrame) (v : Value) (vs : Domain)
    (doms : List Domain) (chosen : Assignment) (rest : List BranchFrame)
    (h : branchCost ((v::vs)::doms) ≤ branchCost f.1) :
    frontierCost ((doms,chosen++[v])::(vs::doms,chosen)::rest) < frontierCost (f::rest) := by
  have he := frontierCost_expand v vs doms chosen rest
  simp only [frontierCost, List.map_cons, List.sum_cons] at he ⊢
  omega


end LeanFzn.Solver.Propagation
