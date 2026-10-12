/-
Purpose: fuel-free chronological search with an explicit pending-branch stack.
Dependencies: Core.Types supplies domains, assignments and verdicts.
DAG: Core.Types -> Frontier -> Engine; Proofs.Frontier proves coverage/progress.
-/
import LeanFzn.Solver.Core.Types
open LeanFzn.Semantics


namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Solver.Core

/-- Remaining domains and the already selected chosen for one pending subtree. -/
abbrev BranchFrame := List Domain × Assignment

/-! ## The decreasing measure

`branchCost` counts the transitions needed to exhaust a frame when no
leaf succeeds; `frontierCost` sums it over the pending stack. Every
nonterminal transition of the chronological traversal decreases
`frontierCost` by exactly one, which is the well-founded measure of the
fuel-free driver below. The measure lives only in the termination
proof; the executable never computes it. -/

/-- Number of transitions needed to exhaust a frame when no leaf succeeds. -/
def branchCost : List Domain → Nat
  | [] => 1
  | d :: rest => 1 + d.length * (branchCost rest + 1)

/-- A finite measure of all pending work. Every nonterminal transition
    decreases it by exactly one, including consuming an exhausted sibling. -/
def frontierCost (pending : List BranchFrame) : Nat :=
  (pending.map fun f => branchCost f.1).sum

/-- Every frame has a positive cost. -/
theorem branchCost_pos (slots : List Domain) : 0 < branchCost slots := by
  cases slots <;> simp [branchCost]; omega

/-- Popping a frame strictly decreases the frontier cost. -/
theorem frontierCost_cons (f : BranchFrame) (pending : List BranchFrame) :
    frontierCost pending < frontierCost (f :: pending) := by
  have hp := branchCost_pos f.1
  simp only [frontierCost, List.map_cons, List.sum_cons]
  omega

/-- The expansion transition of a nonempty next domain: pushing the
    selected child's frame and the sibling frame costs exactly one more
    than the parent frame it replaces. -/
theorem frontierCost_expand (v : Value) (vs : Domain) (rest : List Domain)
    (chosen : Assignment) (pending : List BranchFrame) :
    frontierCost ((rest, chosen ++ [v]) :: (vs :: rest, chosen) :: pending) + 1
      = frontierCost (((v :: vs) :: rest, chosen) :: pending) := by
  simp only [frontierCost, List.map_cons, List.sum_cons]
  have h1 : branchCost (vs :: rest) = 1 + vs.length * (branchCost rest + 1) := by
    simp [branchCost]
  have h2 : branchCost ((v :: vs) :: rest)
      = 1 + (vs.length + 1) * (branchCost rest + 1) := by
    simp [branchCost, List.length_cons, Nat.succ_mul]
  rw [h1, h2]
  have hpos : 0 < branchCost rest + 1 := by omega
  have hsplit : (vs.length + 1) * (branchCost rest + 1)
      = vs.length * (branchCost rest + 1) + (branchCost rest + 1) := by
    rw [Nat.succ_mul]
  omega

/-! ## The fuel-free traversal

`frontierSolve` is the total, kernel-checked chronological traversal.
Termination is by `frontierCost pending`; the measure is proof-only
(erased in compiled code), so the executable carries no search budget,
default fuel, timeout or iteration counter. The result is an internal
two-constructor verdict: a satisfying assignment, or `unsat`. -/

/-- The internal verdict of the fuel-free traversal: either a witness
    that passed the leaf predicate, or exhaustion of the whole frontier
    (no represented assignment satisfies the leaf). -/
inductive FrontierResult where
  /-- A complete assignment that passed the leaf predicate. -/
  | sat (a : Assignment)
  /-- Every represented assignment failed the leaf predicate. -/
  | unsat

/-- The fuel-free chronological traversal of the pending-branch stack.
    Empty stack: UNSAT. Complete prefix: test the leaf. Empty next
    domain: drop the exhausted frame. Nonempty next domain: explore the
    selected value's child, then the unused siblings, then the tail. -/
def frontierSolve (leaf : Assignment → Bool) (pending : List BranchFrame) :
    FrontierResult :=
  match pending with
  | [] => .unsat
  | (slots, chosen) :: rest =>
      match slots with
      | [] => if leaf chosen then .sat chosen else frontierSolve leaf rest
      | [] :: _ => frontierSolve leaf rest
      | (v :: vs) :: doms =>
          frontierSolve leaf
            ((doms, chosen ++ [v]) :: (vs :: doms, chosen) :: rest)
termination_by frontierCost pending
decreasing_by
  · -- popping a frame
    simp_wf
    exact frontierCost_cons _ _
  · -- dropping an exhausted frame
    simp_wf
    exact frontierCost_cons _ _
  · -- expansion: the two pushed frames cost one more than the parent
    simp_wf
    have h := frontierCost_expand v vs doms chosen rest
    omega

/-- The historical fuel-bounded traversal, retained as an explicitly
    named diagnostic reference. It is NOT the driver: the public path
    uses `frontierSolve`. Fuel exhaustion reports `unknown`. -/
def frontierSearch (leaf : Assignment → Bool) : Nat → List BranchFrame → SearchResult
  | _, [] => .unsat
  | 0, _ :: _ => .unknown
  | fuel + 1, (slots, chosen) :: pending =>
      match slots with
      | [] => if leaf chosen then .sat chosen else frontierSearch leaf fuel pending
      | [] :: _ => frontierSearch leaf fuel pending
      | (v :: vs) :: rest =>
          frontierSearch leaf fuel ((rest, chosen ++ [v]) :: (vs :: rest, chosen) :: pending)
end LeanFzn.Solver.Propagation
